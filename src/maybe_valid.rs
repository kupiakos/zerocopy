use super::*;

use core::{mem::MaybeUninit, cell::Cell};

pub unsafe trait MakeUninit {
    /// # Safety
    ///
    /// This must have the same layout as `Self` and be able to be entirely filled with
    /// uninitialized bytes.
    type Uninit: ?Sized;

    /// # Safety for implementors
    ///
    /// `val` must have the same address as the output
    fn new_uninit_ref(val: &Self) -> &Self::Uninit;

    /// Wrap a `&mut T` as uninitialized data.
    ///
    /// # Safety for callers
    ///
    /// Byte validity of `*val` must be maintained.
    /// `*output = MaybeUninit::uninit()` is undefined behavior unless `output` is entirely uninit.
    /// Field bytes cannot be made uninitialized, unless they are within a `MaybeUninit`.
    ///
    /// # Safety for implementors
    ///
    /// `val` must have the same address as the output.
    unsafe fn new_uninit_mut(val: &mut Self) -> &mut Self::Uninit;

    /// Assume that `*val` is initialized to contain a valid `Self`, getting a `&Self` to it.
    ///
    /// # Safety
    ///
    /// The same as [`MaybeUninit::assume_init_ref`].
    /// [`MaybeUninit::assume_init_ref`]: https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#method.assume_init_ref
    unsafe fn assume_init_ref(val: &Self::Uninit) -> &Self;

    /// Assume that `*val` is initialized to contain a valid `Self`, getting a `&mut Self` to it.
    ///
    /// # Safety
    ///
    /// The same as [`MaybeUninit::assume_init_mut`].
    /// [`MaybeUninit::assume_init_mut`]: https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#method.assume_init_mut
    unsafe fn assume_init_mut(val: &mut Self::Uninit) -> &mut Self;
}

unsafe impl<T> MakeUninit for T {
    type Uninit = MaybeUninit<T>;

    fn new_uninit_ref(val: &Self) -> &Self::Uninit {
        // SAFETY:
        // - `MaybeUninit<T>` has identical layout to `T`
        // - `MaybeUninit<T>` has a no byte validity requirement
        // - The original `T` referent cannot be made invalid through `&MaybeUninit<T>`.
        unsafe { &*(val as *const Self as *const MaybeUninit<T>) }
    }

    unsafe fn new_uninit_mut(val: &mut Self) -> &mut Self::Uninit {
        // SAFETY:
        // - `MaybeUninit<T>` has identical layout to `T`
        // - `MaybeUninit<T>` has a no byte validity requirement
        // - The user promises to not mutate the referent in a way that makes it invalid.
        unsafe { &mut *(val as *mut Self as *mut MaybeUninit<T>) }
    }

    unsafe fn assume_init_ref(val: &Self::Uninit) -> &Self {
        // SAFETY: the caller has the same safety contract as the callee
        unsafe { val.assume_init_ref() }
    }

    unsafe fn assume_init_mut(val: &mut Self::Uninit) -> &mut Self {
        // SAFETY: the caller has the same safety contract as the callee
        unsafe { val.assume_init_mut() }
    }
}

// TODO: slice DST
unsafe impl<T> MakeUninit for [T] {
    type Uninit = [MaybeUninit<T>];

    fn new_uninit_ref(val: &Self) -> &Self::Uninit {
        // SAFETY:
        // - `[MaybeUninit<T>]` has identical layout to `[T]`
        // - `[MaybeUninit<T>]` has a no byte validity requirement
        // - The original `[T]` referent cannot be made invalid through `&[MaybeUninit<T>]`.
        unsafe { &*(val as *const Self as *const [MaybeUninit<T>]) }
    }

    unsafe fn new_uninit_mut(val: &mut Self) -> &mut Self::Uninit {
        // SAFETY:
        // - `[MaybeUninit<T>]` has identical layout to `[T]`
        // - `[MaybeUninit<T>]` has a no byte validity requirement
        // - The user promises to not mutate the referent in a way that makes it invalid.
        unsafe { &mut *(val as *mut Self as *mut [MaybeUninit<T>]) }
    }

    unsafe fn assume_init_ref(val: &Self::Uninit) -> &Self {
        // SAFETY:
        // - This is the same operation as `MaybeUninit::slice_assume_init_ref`
        // - This has the same contract for every element as `assume_init_ref`, which
        //   is the contract of this function.
        unsafe { &*(val as *const [MaybeUninit<T>] as *const [T]) }
    }

    unsafe fn assume_init_mut(val: &mut Self::Uninit) -> &mut Self {
        // SAFETY:
        // - This is the same operation as `MaybeUninit::slice_assume_init_mut`
        // - This has the same contract for every element as `assume_init_mut`, which
        //   is the contract of this function.
        unsafe { &mut *(val  as *mut [MaybeUninit<T>] as *mut Self) }
    }
}

// for T: Sized -> MaybeUninit<T>
// for [T]      -> [MaybeUninit<T>]

/// Marks types that have no interior mutability.
///
/// In other words, the bytes of this type can only be mutated behind a `mut Self` or `&mut Self`,
/// exclusive access to the type.
///
/// Most of the time, you won't need to worry about this. However, it is necessary to maintain
/// soundness in some other marker types like `Bytes`.
///
/// It's not enough to not mutate through this trait - `&[u8]` cannot be soundly cast to a
/// `&[Cell<u8>]`.
///
/// This has historically been called the [`Freeze`] auto trait.
/// The author believes it should be made available in stable code for these sorts of use cases.
///
/// [`Freeze`]: https://github.com/rust-lang/rust/issues/60715
pub unsafe trait NoInteriorMutable: core::panic::RefUnwindSafe {
    // The `Self: Sized` bound makes it so that `FromZeroes` is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;
}

// impl<T, Reason> NoInteriorMutable for T where T: NoInteriorMutableBecause<Reason> {}

// TODO: implement for many built-in types - idea, copy from docs page of RefUnwindSafe?

/// Marks a type as having initialized field bytes, but a possibly invalid byte pattern.
///
/// # Capabilities
///
/// - `MaybeValid<T>` is `FromZeroes + FromBytes` for all `T`.
/// - `MaybeValid<T> where T: FromBytes` is `Into<T>`
/// - `MaybeValid<T> where T: TryFromBytes` can be safely fallibly converted to `T`, `&T`, and `&mut T`
/// - `MaybeValid<T>` is `AsBytes` if `T: AsBytes`
///   - tip: `MaybeValid<Bytes<T>>` is always `AsBytes` and `FromBytes`.
/// - `MaybeValid<T>` does not affect alignment.
///
/// # `MaybeValid<T>` vs. other similar types
///
/// Like `MaybeUninit<T>`, `MaybeValid<T>` does not have to carry a valid `T`.
/// Unlike `MaybeUninit<T>`, `MaybeValid<T>` has to have at least enough valid bits to.
///
/// This is similar to `Bytes<MaybeUninit<T>>`, but not quite the same.
/// `MaybeValid<T>` is only `AsBytes` if `T: AsBytes`.
/// Padding bytes and `MaybeUninit<T>` in `MaybeValid<T>` may still be uninitialized.
/// This is similar to the difference between
/// `ptr::write_bytes(p, 0, len)` and `*p = mem::zeroed()` - the latter may still include
/// uninitialized bytes.
///
#[repr(transparent)]
#[derive(Debug)]
pub struct MaybeValid<T: MakeUninit + ?Sized>(
    // Invariant: all field bytes in `T` must be initialized
    T::Uninit,
);

unsafe impl<T: ?Sized + MakeUninit> FromZeroes for MaybeValid<T> {
    fn only_derive_is_allowed_to_implement_this_trait() {
        unreachable!()
    }
}

unsafe impl<T: ?Sized + MakeUninit> FromBytes for MaybeValid<T> {
    fn only_derive_is_allowed_to_implement_this_trait() {
        unreachable!()
    }
}

impl<T> MaybeValid<T>
where
    T: MakeUninit<Uninit = MaybeUninit<T>> + Sized,
{
    /// Wrap a `val`, erasing the knowledge of its byte validity.
    pub fn new(val: T) -> Self
    {
        Self(MaybeUninit::new(val))
    }

    /// Extracts the inner value of this `MaybeValid<T>`.
    ///
    /// # Safety
    ///
    /// `self` must have a valid byte pattern for `T`.
    pub unsafe fn assume_valid(self) -> T
    {
        unsafe { self.0.assume_init() }
    }
}

impl<T: MakeUninit + ?Sized> MaybeValid<T> {
    /// Wrap a `&T`, erasing the knowledge of the `*val`'s byte validity.
    pub fn new_ref(val: &T) -> &Self {
        // SAFETY: `T::Uninit` is `repr(transparent)` over `T` and points to a valid `T`
        unsafe { &*(T::new_uninit_ref(val) as *const _ as *const Self) }
    }

    /// Wrap a `&mut T`, erasing the knowledge of `*val`'s byte validity.
    ///
    /// `T` must have no byte validity requirement so `*out = MaybeValid::new_zeroed()` is sound.
    pub fn new_mut(val: &mut T) -> &mut Self
    where
        T: FromBytes,
    {
        // SAFETY:
        // - `T::Uninit` is `repr(transparent)` over `T` and points to a valid `T`
        // - The inner `MaybeUninit<T>`  mutated through.
        unsafe { &mut *(T::new_uninit_mut(val) as *mut _ as *mut Self) }
    }

    /// Extracts a reference to the inner value of this `MaybeValid<T>`.
    ///
    /// # Safety
    ///
    /// `self` must have a valid byte pattern for `T`.
    pub unsafe fn assume_valid_ref(&self) -> &T {
        // SAFETY: `self` must have a valid byte pattern for `T`.
        unsafe { T::assume_init_ref(&self.0) }
    }

    /// Extracts a mutable reference to the inner value of this `MaybeValid<T>`.
    ///
    /// # Safety
    ///
    /// `self` must have a valid byte pattern for `T`.
    pub unsafe fn assume_valid_mut(&mut self) -> &mut T {
        // SAFETY: `self` must have a valid byte pattern for `T`.
        unsafe { T::assume_init_mut(&mut self.0) }
    }
}

impl<T> MaybeValid<[T]> {
    // TODO
}
