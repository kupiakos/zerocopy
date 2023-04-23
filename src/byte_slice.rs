
use super::*;


#[allow(clippy::missing_safety_doc)] // TODO(fxbug.dev/99068)
/// A mutable or immutable reference to a byte slice.
///
/// `ByteSlice` abstracts over the mutability of a byte slice reference, and is
/// implemented for various special reference types such as `Ref<[u8]>` and
/// `RefMut<[u8]>`.
///
/// Note that, while it would be technically possible, `ByteSlice` is not
/// implemented for [`Vec<u8>`], as the only way to implement the [`split_at`]
/// method would involve reallocation, and `split_at` must be a very cheap
/// operation in order for the utilities in this crate to perform as designed.
///
/// For more flexible behavior, see the [`yoke`] library.
///
/// [`Vec<u8>`]: alloc::vec::Vec
/// [`split_at`]: crate::ByteSlice::split_at
/// [`yoke`]: https://docs.rs/yoke/latest/yoke/struct.Yoke.html
pub unsafe trait ByteSlice: Deref<Target = [u8]> + Sized + self::sealed::Sealed {
    /// The type of casting a `Self` into a `T` with the same ownership.
    /// TODO: be more clear, rename maybe?
    type Cast<'a, T: ?Sized>: Deref<Target = T>
    where
        Self: 'a,
        T: 'a;

    /// Gets a raw pointer to the first byte in the slice.
    #[inline]
    fn as_ptr(&self) -> *const u8 {
        <[u8]>::as_ptr(self)
    }

    /// Splits the slice at the midpoint.
    ///
    /// `x.split_at(mid)` returns `x[..mid]` and `x[mid..]`.
    ///
    /// # Panics
    ///
    /// `x.split_at(mid)` panics if `mid > x.len()`.
    fn split_at(self, mid: usize) -> (Self, Self) { todo!() }

    unsafe fn _cast_as_unchecked<'a, T>(self) -> Self::Cast<'a, T>
    where
        Self: 'a,
        T: 'a;
}

/// `ByteSlice` but only for read-only byte slices
pub unsafe trait ReadOnlyByteSlice: ByteSlice {}
unsafe impl ReadOnlyByteSlice for &'_ [u8] {}
// todo: others

#[allow(clippy::missing_safety_doc)] // TODO(fxbug.dev/99068)
/// A mutable reference to a byte slice.
///
/// `ByteSliceMut` abstracts over various ways of storing a mutable reference to
/// a byte slice, and is implemented for various special reference types such as
/// `RefMut<[u8]>`.
pub unsafe trait ByteSliceMut: ByteSlice + DerefMut {
    // type CastMut<'a, T>: DerefMut<Target = T>
    // where
    //     Self: 'a,
    //     T: 'a;

    /// Gets a mutable raw pointer to the first byte in the slice.
    #[inline]
    fn as_mut_ptr(&mut self) -> *mut u8 {
        <[u8]>::as_mut_ptr(self)
    }
}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for &'a [u8] {
    type Cast<'b, T: ?Sized> = &'b T where Self: 'b, T: 'b;

    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        <[u8]>::split_at(self, mid)
    }

    unsafe fn _cast_as_unchecked<'b, T>(self) -> Self::Cast<'b, T>
    where
        Self: 'b,
        T: 'b,
    {
        unsafe { &*self.as_ptr().cast() }
    }
}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for &'a mut [u8] {
    type Cast<'b, T: ?Sized> = &'b mut T where Self: 'b, T: 'b;

    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        <[u8]>::split_at_mut(self, mid)
    }

    unsafe fn _cast_as_unchecked<'b, T>(self) -> Self::Cast<'b, T>
    where
        Self: 'b,
        T: 'b,
    {
        unsafe { &mut *self.as_mut_ptr().cast() }
    }
}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for Ref<'a, [u8]> {
    type Cast<'b, T: ?Sized> = Ref<'b, T> where Self: 'b, T: 'b;
    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        Ref::map_split(self, |slice| <[u8]>::split_at(slice, mid))
    }

    unsafe fn _cast_as_unchecked<'b, T>(self) -> Self::Cast<'b, T>
    where
        Self: 'b,
        T: 'b,
    {
        todo!()
        // Ref::map(self, |x| LayoutVerified::<&'a [u8], T>::new(x).unwrap_unchecked().into_ref())
    }
}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for RefMut<'a, [u8]> {
    unsafe fn _cast_as_unchecked<'b, T>(self) -> Self::Cast<'b, T>
    where
        Self: 'b,
        T: 'b,
    {
        RefMut::map(self, |x| unsafe { &mut *x.as_mut_ptr().cast::<T>() })
    }

    type Cast<'b, T: ?Sized>
    where
        Self: 'b,
        T: 'b = RefMut<'b, T>;
}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSliceMut for &'a mut [u8] {}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSliceMut for RefMut<'a, [u8]> {}

/// Byte slices that are cheap to split.
pub trait CheapSplit: Sized {
    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        todo!()
        // RefMut::map_split(self, |slice| <[u8]>::split_at_mut(slice, mid))
    }
}

/// Bytes and byte wrappers that can be cast to wrap another type.
///
/// - [x] `&[u8]        -> &T`
/// - [ ] `&mut [u8]    -> &mut T`
/// - [ ] `Vec<u8>      -> Box<T>`
/// - [ ] `String       -> Box<T>`
/// - [ ] `Cow<[u8]>    -> Cow<Box<T>>`
/// - [ ] `Ref<[u8]>    -> Ref<T>`
/// - [ ] `RefMut<[u8]> -> RefMut<[u8]>`
/// - [ ] `Rc<[u8]>     -> Rc<T>`
/// - [ ] `Arc<[u8]>    -> Arc<T>`
/// `Cow<str>`
// pub trait CastableBytes<'a> {
pub trait CastableBytes {
    /// - `Cast<T>` must have same ownership as `Self` with a possibly shorter lifetime 'a.
    type Cast<'a, T: ?Sized>: 'a where Self: 'a, T: 'a;

    /// # Safety for callers
    ///
    /// - The bytes pointed to by `self` must be a valid byte pattern for `T`.
    /// - The bytes pointed to by `self` must not be made uninitialized.
    ///   - This includes `*out = T::new_zeroed()`.
    /// - `Self::Cast<T>` must not contain interior mutability.
    ///   Stacked Borrows currently rejects a `&u8` unsafely cast to `&Cell<u8>`.
    // unsafe fn cast_as_unchecked<T>(self) -> Self::Cast<T>;
    unsafe fn cast_as_unchecked<'a, T>(self) -> Self::Cast<'a, T> where Self: 'a, T: 'a;
}

// pub trait Cast2 {
//     type Cast<T: ?Sized>;
//     fn cast_ref<'a, T>(&'a self) -> &Self::Cast<T> where T: 'a;
// }

// impl<'a> CastableBytes<'a> for &'a [u8] {
impl<'b> CastableBytes for &'b [u8] {
    type Cast<'a, T: ?Sized> = &'a T where 'b: 'a, T: 'a;

    unsafe fn cast_as_unchecked<'a, T>(self) -> &'a T where Self: 'a, T: 'a {
        unsafe { &*(self as *const _ as *const T) }
    }
}

// impl<'a> Cast2 for &'a [u8] {
//     type Cast<T: ?Sized> = &'a T;

//     unsafe fn cast_ref_unchecked<'a, T>(&'a self) -> &T where T: 'a {
//         todo!()
//     }
// }

fn test_cast_inner<'a, C: CastableBytes + 'a>(c: C) -> C::Cast<'a, [u8; 4]> {
    unsafe { c.cast_as_unchecked() }
}

fn test_cast(c: &[u8]) -> &[u8; 4] {
// fn test_cast<'a, C: CastableBytes + Clone>(c: C) -> C::Cast<'a, [u8; 4]> where C: 'a {
    // assert!(c.len(), 4);
    let x = ();
    let y = 10;
    let z = &y;

    unsafe {
       test_cast_inner(c)
    }
}
