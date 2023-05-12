use core::{
    fmt::{self, Display, Formatter},
    mem, alloc::Layout,
};

use crate::{ByteSlice, FromZeroes, LayoutVerified, Unalign};

/// The conversion failed because of the bytes had an invalid layout for the destination type.
#[derive(Clone, Copy, Debug)]
#[repr(usize)] // this results in smaller codegen on RISC-V
pub enum LayoutError {
    /// The byte slice was not a correct size.
    Size = 1,

    /// The byte slice was not aligned for `&T`.
    Align,
}

impl LayoutError {
    /// Returns a static string error message.
    pub fn static_message(self) -> &'static str {
        match self {
            LayoutError::Size => "The byte slice was too small",
            LayoutError::Align => "The byte slice was not aligned on boundary for the target type",
        }
    }
}

impl Display for LayoutError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.static_message())
    }
}

/// Types that can be unsafely but in some cases soundly be interpreted from bytes, also called a
/// _bytecast_.
///
/// A _bytecast_ is a reinterpretation of the bytes of a slice as if it were another type.
/// So long as invariants of the destination type isn't invalidated, this is sound in Rust - it
/// has no strict aliasing requirement.
///
// TODO: example, link to strict aliasing
///
/// However, as the [`AsBytes`] and [`FromBytes`] traits describe, byte validity and the presence of
/// `MaybeUninit` data affect whether a bytecast can be safely performed.
///
/// This is automatically implemented for all `Sized` types, `[T]`, and any `#[derive(SliceDst)]`
/// types.
///
/// This is not implemented for trait objects; these are never allowed to be treated as swappable
/// memory due to erasure of lifetimes.
///
/// [`AsBytes`]: crate::AsBytes
// TODO: Document the erasure of lifetimes above, there's a link somewhere that demonstrates it.
//       Essentially, a `dyn Trait + 'a` can store lifetimes longer than `'a` that could violate
//       lifetimes if swapped through a `&mut dyn Trait` cast to a `&mut impl Sized`.
//       It's related to why `&'a mut dyn Trait + 'b` can be cast to `&'a mut dyn Trait + 'a`.
pub(crate) unsafe trait UncheckedFromBytes {
    const MIN_SIZE: usize;

    /// The compile-time known alignment requirement for this type.
    // TODO: consolidate with other known alignment stuffs
    const ALIGN: usize;

    /// Unsafely cast a byte slice to another type optionally ending in a slice.
    ///
    /// # Safety for callers
    ///
    /// - `Self` must not contain shared (interior) mutability (remove for `&mut`)
    /// - `bytes` must be aligned to `Self::ALIGN` bytes.
    /// - The `bytes` of `Self` must be large enough for the input.
    ///   - For `Sized` types, `bytes.len() >= size_of::<Self>()`.
    ///   - For `[T]`, `bytes` can be any length. The output is the slice with the largest length
    ///     that fits in `bytes`.
    ///   - For `#[derive(SliceDst)]` types:
    ///     - A) If the type has no defined length field,
    ///          `bytes.len() >= MIN_SIZE` must be true.
    ///     - B) If the type has a defined length field, that length field must not specify a length
    ///          exceeding that of `bytes.len()`.
    ///
    /// # Safety for implementers
    /// - The address of the output must equal the address of `bytes`.
    unsafe fn bytecast_ref_unchecked(bytes: &[u8]) -> &Self;
    unsafe fn bytecast_mut_unchecked(bytes: &mut [u8]) -> &mut Self;
    // fn min_size() -> usize;
    // fn align() -> usize;
}

// This can't do UncheckedFromBytes blanket impl'd for `impl Sized` + `impl SliceDst`,
// where `SliceDst` is implemented on [T]` and `derive`d types.
// That violates the coherence rules. However, it *is* valid to do
// `impl Sized` + `[T]` + `derive`d `SliceDst` types.

unsafe impl<T> UncheckedFromBytes for T {
    const MIN_SIZE: usize = mem::size_of::<T>();
    const ALIGN: usize = mem::align_of::<T>();

    /// # Safety
    /// `bytes` must be large enough for `Self`
    unsafe fn bytecast_ref_unchecked(bytes: &[u8]) -> &Self {
        unsafe { &*(bytes as *const [u8]).cast() }
    }

    unsafe fn bytecast_mut_unchecked(bytes: &mut [u8]) -> &mut Self {
        unsafe { &mut *(bytes as *mut [u8]).cast() }
    }

    // fn min_size() -> usize {
    //     mem::size_of::<T>()
    // }

    // fn align() -> usize {
    //     mem::align_of::<T>()
    // }
}

unsafe impl<T> UncheckedFromBytes for [T] {
    const MIN_SIZE: usize = 0;
    const ALIGN: usize = mem::align_of::<T>();

    /// # Safety
    /// `bytes` must be properly aligned for `T`.
    unsafe fn bytecast_ref_unchecked(bytes: &[u8]) -> &Self {
        let len = bytes.len() / mem::size_of::<T>();
        let data: *const T = bytes.as_ptr().cast();

        // SAFETY:
        // - The length of `[T]` metadata is the size in bytes divided by `size_of::<T>()`.
        // - The alignment of `bytes` for `T` has been checked by the caller.
        unsafe { core::slice::from_raw_parts(data, len) }
    }

    /// # Safety
    /// `bytes` must be properly aligned for `T`.
    unsafe fn bytecast_mut_unchecked(bytes: &mut [u8]) -> &mut Self {
        let len = bytes.len() / mem::size_of::<T>();
        let data: *mut T = bytes.as_mut_ptr().cast();

        // SAFETY:
        // - The length of `[T]` metadata is the size in bytes divided by `size_of::<T>()`.
        // - The alignment of `bytes` for `T` has been checked by the caller.
        unsafe { core::slice::from_raw_parts_mut(data, len) }
    }

    // fn min_size() -> usize {
    //     mem::size_of::<T>()
    // }

    // fn align() -> usize {
    //     mem::align_of::<T>()
    // }
}

/// Types for which any byte pattern is valid.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(FromBytes)]`.
///
/// `FromBytes` types can safely be deserialized from an untrusted sequence of
/// bytes because any byte sequence corresponds to a valid instance of the type.
///
/// When Bytecast
///
/// `FromBytes` is ignorant of byte order. For byte order-aware types, see the
/// [`byteorder`] module.
///
/// # Safety
///
/// If `T: FromBytes`, then unsafe code may assume that it is sound to treat any
/// initialized sequence of bytes of length `size_of::<T>()` as a `T`. If a type
/// is marked as `FromBytes` which violates this contract, it may cause
/// undefined behavior.
///
/// If a type has the following properties, then it is safe to implement
/// `FromBytes` for that type:
/// - If the type is a struct, all of its fields must implement `FromBytes`
/// - If the type is an enum:
///   - It must be a C-like enum (meaning that all variants have no fields)
///   - It must have a defined representation (`repr`s `C`, `u8`, `u16`, `u32`,
///     `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, or `isize`).
///   - The maximum number of discriminants must be used (so that every possible
///     bit pattern is a valid one). Be very careful when using the `C`,
///     `usize`, or `isize` representations, as their size is
///     platform-dependent.
/// - The type must not contain interior mutability. This is required by `Bytes<T>`, which
///   otherwise could have its invariant violated with `T = Bytes<Cell<MaybeUninit<i32>>>`.
///   `Cell<MaybeUninit<T>>` is valid for all byte patterns, but if it implemented `FromBytes`,
///   `Bytes` could deref to `&Cell<MaybeUninit<T>>` and be `replace`d with uninit data.
/// # Rationale
///
/// ## Why isn't an explicit representation required for structs?
///
/// Per the [Rust reference](reference),
///
/// > The representation of a type can change the padding between fields, but
/// does not change the layout of the fields themselves.
///
/// [reference]: https://doc.rust-lang.org/reference/type-layout.html#representations
///
/// Since the layout of structs only consists of padding bytes and field bytes,
/// a struct is soundly `FromBytes` if:
/// 1. its padding is soundly `FromBytes`, and
/// 2. its fields are soundly `FromBytes`.
///
/// The answer to the first question is always yes: padding bytes do not have
/// any validity constraints. A [discussion] of this question in the Unsafe Code
/// Guidelines Working Group concluded that it would be virtually unimaginable
/// for future versions of rustc to add validity constraints to padding bytes.
///
/// [discussion]: https://github.com/rust-lang/unsafe-code-guidelines/issues/174
///
/// Whether a struct is soundly `FromBytes` therefore solely depends on whether
/// its fields are `FromBytes`.
pub unsafe trait FromBytes: FromZeroes {
    // The `Self: Sized` bound makes it so that `FromBytes` is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Performs a zero-copy bytecast of `bytes`, reading the same bytes as a `&Self`.
    ///
    /// If `bytes.len() != size_of::<Self>()` or `bytes` is not aligned to `align_of::<Self>()`,
    /// this returns a [`LayoutError`].
    fn try_bytecast_ref(bytes: &[u8]) -> Result<&Self, LayoutError> {
        todo!()
    }

    /// Performs a zero-copy bytecast of `bytes`, reading the same bytes as a `&Self`.
    ///
    /// If `bytes.len() != size_of::<Self>()` or `bytes` is not aligned to `align_of::<Self>()`,
    /// this returns a [`LayoutError`].
    fn try_bytecast_mut(bytes: &mut [u8]) -> Result<&mut Self, LayoutError> {
        todo!()
    }

    // suffix/prefix require a way to specify complexity of cloning
    // suffix/prefix requires not just a reject/accept, but ability to declare the remainder so that
    // try_bytecast can check

    /// Reads a copy of `Self` from `bytes`.
    ///
    /// If `bytes.len() != size_of::<Self>()`, this returns `None`.
    ///
    // `read_from*` can accept a `&[u8]` rather than `impl ByteSlice` - this is simpler since
    // any `ByteSlice` can always be converted into `&[u8]`, most often implicitly, and will
    // always perform a borrowing operation to do the copy instead of consuming.
    fn read_from(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        let lv = LayoutVerified::<_, Unalign<Self>>::new_unaligned(bytes)?;
        Some(lv.read().into_inner())
    }

    /// Reads a copy of `Self` from the prefix of `bytes`.
    ///
    /// `read_from_prefix` reads a `Self` from the first `size_of::<Self>()`
    /// bytes of `bytes`. If `bytes.len() < size_of::<Self>()`, this returns
    /// `None`.
    fn read_from_prefix(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        let (lv, _suffix) = LayoutVerified::<_, Unalign<Self>>::new_unaligned_from_prefix(bytes)?;
        Some(lv.read().into_inner())
    }

    /// Reads a copy of `Self` from the suffix of `bytes`.
    ///
    /// `read_from_suffix` reads a `Self` from the last `size_of::<Self>()`
    /// bytes of `bytes`. If `bytes.len() < size_of::<Self>()`, this returns
    /// `None`.
    fn read_from_suffix(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        let (_prefix, lv) = LayoutVerified::<_, Unalign<Self>>::new_unaligned_from_suffix(bytes)?;
        Some(lv.read().into_inner())
    }
}
