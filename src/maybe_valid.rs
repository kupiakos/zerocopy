use super::*;

use core::mem::MaybeUninit;

trait MakeUninit {
    type Uninit: ?Sized;

    fn new_uninit(val: Self) -> Self::Uninit
    where
        Self: Sized,
        Self::Uninit: Sized;
    fn new_uninit_ref(val: &Self) -> &Self::Uninit;
    /// # Safety
    ///
    /// Byte validity of `Self` must be maintained.
    /// Field bytes cannot be made uninitialized, unless they are within a `MaybeUninit`.
    unsafe fn new_uninit_mut(val: &mut Self) -> &mut Self::Uninit;
}

// trait Uninit {
//     type Inner;

//     fn new_uninit(val: Self::Inner) -> Self
//     where
//         Self::Inner: Sized,
//         Self: Sized;
//     fn new_uninit_ref(val: &Self::Inner) -> &Self;
//     fn new_uninit_mut(val: &mut Self) -> &mut Self;
// }

impl<T> MakeUninit for T {
    type Uninit = MaybeUninit<T>;

    fn new_uninit(val: Self) -> Self::Uninit {
        todo!()
    }

    fn new_uninit_ref(val: &Self) -> &Self::Uninit {
        todo!()
    }

    unsafe fn new_uninit_mut(val: &mut Self) -> &mut Self::Uninit {
        todo!()
    }
}
impl<T> MakeUninit for [T] {
    type Uninit = [MaybeUninit<T>];

    fn new_uninit(val: [T]) -> [MaybeUninit<T>]
    where
        for<'a> Self: Sized,
        for<'a> Self::Uninit: Sized,
    {
        unreachable!()
    }

    fn new_uninit_ref(val: &Self) -> &Self::Uninit {
        todo!()
    }

    unsafe fn new_uninit_mut(val: &mut Self) -> &mut Self::Uninit {
        todo!()
    }
}

// for T: Sized -> MaybeUninit<T>
// for [T]      -> [MaybeUninit<T>]

/// Marks a type as having initialized field bytes, but a possibly invalid byte pattern.
///
/// This is similar to `Bytes<MaybeUninit<T>>`, but not quite the same.
/// `MaybeValid<T>` is only `AsBytes` if `T: AsBytes`.
/// Padding bytes and `MaybeUninit<T>` in `MaybeValid<T>` may still be uninitialized.
///
/// `MaybeValid<T>` is `FromBytes` if `T: TryFromBytes`.
#[repr(transparent)]
pub struct MaybeValid<T: MakeUninit + ?Sized>(
    // Invariant: all field bytes in `T` must be initialized
    T::Uninit,
);

impl<T: MakeUninit + ?Sized> MaybeValid<T> {
    /// Wrap a `val`, erasing the knowledge of its byte validity.
    pub fn new(val: T) -> Self {
        Self(T::new_uninit(val))
    }

    /// Wrap a `&val`, erasing the knowledge of the pointee's byte validity.
    pub fn new_ref(val: &T) -> &Self {
        // SAFETY: `repr(transparent)` guarantees identical layout to `T`.
        unsafe { &*(val as *const _ as *const Self) }
    }

    pub fn new_mut(val: &mut T) -> &mut Self
    where
        T: FromBytes,
    {
        // SAFETY:
        // - `repr(transparent)` guarantees identical layout to `T`.
        // - The inner `MaybeUninit<T>` is not mutated through.
        unsafe { &mut *(val as *mut _ as *mut Self) }
    }

    /// Extracts the inner value of this `MaybeValid<T>`.
    ///
    /// # Safety
    /// `self` must have a valid byte pattern for `T`.
    pub unsafe fn assume_valid(self) -> Self
    where
        T: Sized,
    {
        self.0
    }

    /// Extracts the inner value of this `MaybeValid<T>`.
    ///
    /// # Safety
    /// `self` must have a valid byte pattern for `T`.
    pub unsafe fn assume_valid_ref(&self) -> &Self {
        self.0.assume_init_ref()
    }

    pub unsafe fn assume_valid_mut(&mut self) -> &mut Self {
        self.0.assume_init_mut()
    }
}

impl<T> MaybeValid<[T]> {
    // TODO
}
