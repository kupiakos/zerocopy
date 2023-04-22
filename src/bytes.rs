// todo license
//! TODO: docs
// TODO: consolidate `zerocopy` impl blocks with more local `where`s

use core::ops::Range;

use super::*;
// use util::TransparentWrapper;

/// A `T` that provably has all of its bytes initialized.
/// All bytes of `T` are initialized, so this object is `AsBytes`
#[repr(transparent)]
#[derive(Debug)]
pub struct Bytes<T: ?Sized>(T);

impl<T: ?Sized> Bytes<T> {
    /// Wraps an `AsBytes` type in `Bytes`
    pub fn new(val: T) -> Self
    where
        T: AsBytes + Sized,
    {
        // SAFETY: `T` is all initialized bytes
        Self(val)
    }

    /// Constructs a `Bytes<T>` from all zero bytes.
    pub fn new_zeroed() -> Self
    where
        T: FromZeroes + Sized,
    {
        // SAFETY: `T` is zeroed
        Self(T::new_zeroed())
    }

    /// Wraps a reference to an `AsBytes` type in `Bytes`
    pub fn new_ref(val: &T) -> &Self
    where
        T: AsBytes,
    {
        // SAFETY: `AsBytes` guarantees `T` is all initialized bytes
        unsafe { Self::from_ref_unchecked(val) }
    }

    /// Make a `&mut Bytes<T>` from ` &mut T`.
    ///
    /// If `T` is not `AsBytes`, this might mutate `val` to
    /// initialize uninitialized bytes.
    pub fn new_mut(val: &mut T) -> &mut Self
    where
        T: MakeBytes,
    {
        val.make_bytes();
        // SAFETY: `MakeBytes` guarantees `val` is all initialized bytes
        unsafe { Self::from_mut_unchecked(val) }
    }

    /// Zero the bytes of `val` to construct a `&mut Bytes<T>`.
    pub fn new_mut_zeroed(val: &mut T) -> &mut Self
    where
        T: FromZeroes,
    {
        val.zero();
        // SAFETY: `val` is all zero bytes
        unsafe { Self::from_mut_unchecked(val) }
    }

    /// Constructs a &Bytes<T>` from data the programmer knows is initialized.
    ///
    /// # Safety
    ///
    /// All bytes of `T` must be initialized.
    pub unsafe fn new_unchecked(val: T) -> Self
    where
        T: Sized,
    {
        Bytes(val)
    }

    /// Constructs a `&Bytes<T>` from data the programmer knows is initialized.
    ///
    /// # Safety
    ///
    /// All bytes of `T` must be initialized.
    pub unsafe fn from_ref_unchecked(val: &T) -> &Self {
        // SAFETY:
        // - `repr(transparent)` over `T` guarantees identical layout and pointer metadata
        // - All bytes are initialized.
        unsafe { &*(val as *const _ as *const Self) }
    }

    /// Constructs a `&Bytes<T>` from data the programmer knows is initialized.
    //
    /// # Safety
    /// All bytes of `T` must be initialized.
    pub unsafe fn from_mut_unchecked(val: &mut T) -> &mut Self {
        // SAFETY:
        // - `repr(transparent)` over `T` guarantees identical layout and pointer metadata
        // - All bytes are initialized.
        unsafe { &mut *(val as *mut _ as *mut Self) }
    }
}

// SAFETY: This is an invariant of `Bytes`.
unsafe impl<T: ?Sized> AsBytes for Bytes<T> {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
        unreachable!()
    }
}

// SAFETY: `Bytes<T: FromZeroes>` can be constructed from zeroes.
unsafe impl<T: ?Sized + FromZeroes> FromZeroes for Bytes<T> {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
        unreachable!()
    }
}

// SAFETY: All byte patterns of `Bytes<T: FromBytes>` are valid.
unsafe impl<T: ?Sized + FromBytes> FromBytes for Bytes<T> {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
        unreachable!()
    }
}

/// Write zeroes to the given byte spans in `val`.
unsafe fn zero_spans<T: ?Sized>(val: &mut T, spans: &[Range<usize>]) {
    let p: *mut T = val;
    for &Range { start, end } in spans {
        unsafe {
            let p = p.cast::<u8>().add(start);
            core::ptr::write_bytes(p, 0, end - start)
        }
    }
}

/// Initialize any uninitialized bytes in `T` so it can be made into bytes.
///
/// `derive(AsBytes)` and `derive(MakeBytes)` both derive this.
pub unsafe trait MakeBytes {
    #[doc(hidden)]
    /// Spans of the bytes that can be zeroed to make `self` bytes.
    ///
    /// This constant is considered an implementation detail.
    ///
    /// # Safety
    ///
    /// same rules as zero_spans
    /// TODO: be formal
    const __PRIVATE_UNINIT_SPANS: &'static [Range<usize>];

    /// Ensures that `self` is all initialized bytes.
    ///
    /// This is done writing all maybe-uninitialized bytes with zeroes.
    #[inline(always)]
    fn make_bytes(&mut self) -> &[u8] {
        // SAFETY: sound as required by by __PRIVATE_UNINIT_SPANS
        unsafe { zero_spans(self, Self::__PRIVATE_UNINIT_SPANS) }
        // SAFETY: all uninitialized spans of `MakeBytes` have been zeroed
        unsafe { Bytes::<Self>::from_ref_unchecked(self) }.as_bytes()
    }

    /// Ensures that `self` is all initialized bytes.
    ///
    /// This is done writing all maybe-uninitialized bytes with zeroes.
    ///
    #[inline(always)]
    fn make_mut_bytes(&mut self) -> &mut [u8]
    where
        Self: FromBytes,
    {
        self.make_bytes();
        unsafe { Bytes::<Self>::from_mut_unchecked(self) }.as_mut_bytes()
    }
}

unsafe impl<T: AsBytes> MakeBytes for T {
    const __PRIVATE_UNINIT_SPANS: &'static [Range<usize>] = &[];

    #[inline(always)]
    fn make_bytes(&mut self) -> &[u8] {
        self.as_bytes()
    }

    #[inline(always)]
    fn make_mut_bytes(&mut self) -> &mut [u8]
    where
        Self: FromBytes,
    {
        self.as_mut_bytes()
    }
}

unsafe impl<T> MakeBytes for MaybeUninit<T> {
    const __PRIVATE_UNINIT_SPANS: &'static [Range<usize>] = &[0..core::mem::size_of::<T>()];
}

// not these types directly, maybe just `From`/`TryFrom`?
trait LoosenContract<To> {}
trait TransposeContract<To> {}
trait TryCheckContract<To> {}
