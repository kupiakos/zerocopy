//! Most of the implementations of known types with zerocopy traits is done here.

use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::{
    NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
    NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize, Wrapping,
};

use crate::{AsBytes, FromBytes, FromZeroes, Unalign, Unaligned};

/// Documents multiple unsafe blocks with a single safety comment.
///
/// Invoked as:
///
/// ```rust,ignore
/// safety_comment! {
///     // Non-doc comments come first.
///     /// SAFETY:
///     /// Safety comment starts on its own line.
///     macro_1!(args);
///     macro_2! { args };
/// }
/// ```
///
/// The macro invocations are emitted, each decorated with the following
/// attribute: `#[allow(clippy::undocumented_unsafe_blocks)]`.
// TODO: rework so that it's included in the doc comments
macro_rules! safety_comment {
    (#[doc = r" SAFETY:"] $(#[doc = $_doc:literal])* $($macro:ident!$args:tt;)*) => {
        #[allow(clippy::undocumented_unsafe_blocks)]
        const _: () = { $($macro!$args;)* };
    }
}

/// Unsafely implements trait(s) for a type.
macro_rules! unsafe_impl {
    // Implement `$trait` for `$ty` with no bounds.
    ($ty:ty: $trait:ty) => {
        unsafe impl $trait for $ty { fn only_derive_is_allowed_to_implement_this_trait() {} }
    };
    // Implement all `$traits` for `$ty` with no bounds.
    ($ty:ty: $($traits:ty),*) => {
        $( unsafe_impl!($ty: $traits); )*
    };
    // For all `$tyvar` with no bounds, implement `$trait` for `$ty`.
    ($tyvar:ident => $trait:ident for $ty:ty) => {
        unsafe impl<$tyvar> $trait for $ty { fn only_derive_is_allowed_to_implement_this_trait() {} }
    };
    // For all `$tyvar: ?Sized` with no bounds, implement `$trait` for `$ty`.
    ($tyvar:ident: ?Sized => $trait:ident for $ty:ty) => {
        unsafe impl<$tyvar: ?Sized> $trait for $ty { fn only_derive_is_allowed_to_implement_this_trait() {} }
    };
    // For all `$tyvar: $bound`, implement `$trait` for `$ty`.
    ($tyvar:ident: $bound:path => $trait:ident for $ty:ty) => {
        unsafe impl<$tyvar: $bound> $trait for $ty { fn only_derive_is_allowed_to_implement_this_trait() {} }
    };
    // For all `$tyvar: $bound + ?Sized`, implement `$trait` for `$ty`.
    ($tyvar:ident: ?Sized + $bound:path => $trait:ident for $ty:ty) => {
        unsafe impl<$tyvar: ?Sized + $bound> $trait for $ty { fn only_derive_is_allowed_to_implement_this_trait() {} }
    };
    // For all `$tyvar: $bound` and for all `const $constvar: $constty`,
    // implement `$trait` for `$ty`.
    ($tyvar:ident: $bound:path, const $constvar:ident: $constty:ty => $trait:ident for $ty:ty) => {
        unsafe impl<$tyvar: $bound, const $constvar: $constty> $trait for $ty {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
    };
}

/// Uses `align_of` to confirm that a type or set of types have alignment 1.
///
/// Note that `align_of<T>` requires `T: Sized`, so this macro doesn't work for
/// unsized types.
macro_rules! assert_unaligned {
    ($ty:ty) => {
        // We only compile this assertion under `cfg(test)` to avoid taking an
        // extra non-dev dependency (and making this crate more expensive to
        // compile for our dependents).
        #[cfg(test)]
        static_assertions::const_assert_eq!(core::mem::align_of::<$ty>(), 1);
    };
    ($($ty:ty),*) => {
        $(assert_unaligned!($ty);)*
    };
}

safety_comment! {
    /// SAFETY:
    /// Per the reference [1], "the unit tuple (`()`) ... is guaranteed as a
    /// zero-sized type to have a size of 0 and an alignment of 1."
    /// - `FromZeroes`, `FromBytes`: There is only one possible sequence of 0
    ///   bytes, and `()` is inhabited.
    /// - `AsBytes`: Since `()` has size 0, it contains no padding bytes.
    /// - `Unaligned`: `()` has alignment 1.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#tuple-layout
    unsafe_impl!((): FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_unaligned!(());
}

safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`, `FromBytes`: all bit patterns are valid for integers [1]
    /// - `AsBytes`: integers have no padding bytes [1]
    /// - `Unaligned` (`u8` and `i8` only): The reference [2] specifies the size
    ///   of `u8` and `i8` as 1 byte. We also know that:
    ///   - Alignment is >= 1
    ///   - Size is an integer multiple of alignment
    ///   - The only value >= 1 for which 1 is an integer multiple is 1
    ///   Therefore, the only possible alignment for `u8` and `i8` is 1.
    ///
    /// [1] TODO(https://github.com/rust-lang/reference/issues/1291): Once the
    ///     reference explicitly guarantees these properties, cite it.
    /// [2] https://doc.rust-lang.org/reference/type-layout.html#primitive-data-layout
    unsafe_impl!(u8: FromZeroes, FromBytes, AsBytes, Unaligned);
    unsafe_impl!(i8: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_unaligned!(u8, i8);
    unsafe_impl!(u16: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i16: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(u32: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i32: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(u64: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i64: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(u128: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i128: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(usize: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(isize: FromZeroes, FromBytes, AsBytes);
}

safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`, `FromBytes`: the `{f32,f64}::from_bits` constructors'
    ///   documentation [1,2] states that they are currently equivalent to
    ///   `transmute`. [3]
    /// - `AsBytes`: the `{f32,f64}::to_bits` methods' documentation [4,5]
    ///   states that they are currently equivalent to `transmute`. [3]
    ///
    /// TODO: Make these arguments more precisely in terms of the documentation.
    ///
    /// [1] https://doc.rust-lang.org/nightly/std/primitive.f32.html#method.from_bits
    /// [2] https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.from_bits
    /// [3] TODO(https://github.com/rust-lang/reference/issues/1291): Once the
    ///     reference explicitly guarantees these properties, cite it.
    /// [4] https://doc.rust-lang.org/nightly/std/primitive.f32.html#method.to_bits
    /// [5] https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.to_bits
    unsafe_impl!(f32: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(f64: FromZeroes, FromBytes, AsBytes);
}

safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`: Per the reference [1], 0x00 is a valid bit pattern for
    ///   `bool`.
    /// - `AsBytes`: Per the reference [1], `bool` always has a size of 1 with
    ///   valid bit patterns 0x01 and 0x00, so the only byte of the bool is
    ///   always initialized
    /// - `Unaligned`: Per the reference [1], "[a]n object with the boolean type
    ///   has a size and alignment of 1 each."
    ///
    /// [1] https://doc.rust-lang.org/reference/types/boolean.html
    unsafe_impl!(bool: FromZeroes, AsBytes, Unaligned);
    assert_unaligned!(bool);
}
safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`: Per the reference [1], 0x0000 is a valid bit pattern for
    ///   `char`.
    /// - `AsBytes`: `char` is represented as a 32-bit unsigned word (`u32`)
    ///   [1], which is `AsBytes`. Note that unlike `u32`, not all bit patterns
    ///   are valid for `char`.
    ///
    /// [1] https://doc.rust-lang.org/reference/types/textual.html
    unsafe_impl!(char: FromZeroes, AsBytes);
}
safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`, `AsBytes`, `Unaligned`: Per the reference [1], `str` has
    ///   the same layout as `[u8]`, and `[u8]` is `FromZeroes`, `AsBytes`, and
    ///   `Unaligned`.
    ///
    /// Note that we don't `assert_unaligned!(str)` because `assert_unaligned!`
    /// uses `align_of`, which only works for `Sized` types.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#str-layout
    unsafe_impl!(str: FromZeroes, AsBytes, Unaligned);
}

safety_comment! {
    // `NonZeroXxx` is `AsBytes`, but not `FromZeroes` or `FromBytes`.
    //
    /// SAFETY:
    /// - `AsBytes`: `NonZeroXxx` has the same layout as its associated
    ///    primitive. Since it is the same size, this guarantees it has no
    ///    padding - integers have no padding, and there's no room for padding
    ///    if it can represent all of the same values except 0.
    /// - `Unaligned`: `NonZeroU8` and `NonZeroI8` document that
    ///   `Option<NonZeroU8>` and `Option<NonZeroI8>` both have size 1. [1] [2]
    ///   This is worded in a way that makes it unclear whether it's meant as a
    ///   guarantee, but given the purpose of those types, it's virtually
    ///   unthinkable that that would ever change. `Option` cannot be smaller
    ///   than its contained type, which implies that, and `NonZeroX8` are of
    ///   size 1 or 0. `NonZeroX8` can represent multiple states, so they cannot
    ///   be 0 bytes, which means that they must be 1 byte. The only valid
    ///   alignment for a 1-byte type is 1.
    ///
    /// [1] https://doc.rust-lang.org/stable/std/num/struct.NonZeroU8.html
    /// [2] https://doc.rust-lang.org/stable/std/num/struct.NonZeroI8.html
    /// TODO(https://github.com/rust-lang/rust/pull/104082): Cite documentation
    /// that layout is the same as primitive layout.
    unsafe_impl!(NonZeroU8: AsBytes, Unaligned);
    unsafe_impl!(NonZeroI8: AsBytes, Unaligned);
    assert_unaligned!(NonZeroU8, NonZeroI8);
    unsafe_impl!(NonZeroU16: AsBytes);
    unsafe_impl!(NonZeroI16: AsBytes);
    unsafe_impl!(NonZeroU32: AsBytes);
    unsafe_impl!(NonZeroI32: AsBytes);
    unsafe_impl!(NonZeroU64: AsBytes);
    unsafe_impl!(NonZeroI64: AsBytes);
    unsafe_impl!(NonZeroU128: AsBytes);
    unsafe_impl!(NonZeroI128: AsBytes);
    unsafe_impl!(NonZeroUsize: AsBytes);
    unsafe_impl!(NonZeroIsize: AsBytes);
}
safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`, `FromBytes`, `AsBytes`: The Rust compiler reuses `0`
    ///   value to represent `None`, so `size_of::<Option<NonZeroXxx>>() ==
    ///   size_of::<xxx>()`; see `NonZeroXxx` documentation.
    /// - `Unaligned`: `NonZeroU8` and `NonZeroI8` document that
    ///   `Option<NonZeroU8>` and `Option<NonZeroI8>` both have size 1. [1] [2]
    ///   This is worded in a way that makes it unclear whether it's meant as a
    ///   guarantee, but given the purpose of those types, it's virtually
    ///   unthinkable that that would ever change. The only valid alignment for
    ///   a 1-byte type is 1.
    ///
    /// [1] https://doc.rust-lang.org/stable/std/num/struct.NonZeroU8.html
    /// [2] https://doc.rust-lang.org/stable/std/num/struct.NonZeroI8.html
    ///
    /// TODO(https://github.com/rust-lang/rust/pull/104082): Cite documentation
    /// for layout guarantees.
    unsafe_impl!(Option<NonZeroU8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    unsafe_impl!(Option<NonZeroI8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_unaligned!(Option<NonZeroU8>, Option<NonZeroI8>);
    unsafe_impl!(Option<NonZeroU16>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI16>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroU32>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI32>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroU64>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI64>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroU128>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI128>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroUsize>: FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroIsize>: FromZeroes, FromBytes, AsBytes);
}

safety_comment! {
    /// SAFETY:
    /// The reference [1] suggests (but does not clearly promise) that
    /// `PhantomData` has size 0 and alignment 1.
    /// - `FromZeroes`, `FromBytes`: There is only one possible sequence of 0
    ///   bytes, and `PhantomData` is inhabited.
    /// - `AsBytes`: Since `PhantomData` has size 0, it contains no padding
    ///   bytes.
    /// - `Unaligned`: Per the preceding reference, `PhantomData` has alignment
    ///   1.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#the-transparent-representation
    ///
    /// TODO(https://github.com/rust-lang/rust/pull/104081): Cite guaranteed
    /// size and alignment.
    unsafe_impl!(T: ?Sized => FromZeroes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => FromBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => AsBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => Unaligned for PhantomData<T>);
    assert_unaligned!(PhantomData<()>, PhantomData<u8>, PhantomData<u64>);
}
safety_comment! {
    /// SAFETY:
    /// `Wrapping<T>` is guaranteed by its docs [1] to have the same layout as
    /// `T`. Also, `Wrapping<T>` is `#[repr(transparent)]`, and has a single
    /// field, which is `pub`. Per the reference [2], this means that the
    /// `#[repr(transparent)]` attribute is "considered part of the public ABI".
    ///
    /// [1] https://doc.rust-lang.org/nightly/core/num/struct.Wrapping.html#layout-1
    /// [2] https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent
    unsafe_impl!(T: FromZeroes => FromZeroes for Wrapping<T>);
    unsafe_impl!(T: FromBytes => FromBytes for Wrapping<T>);
    unsafe_impl!(T: AsBytes => AsBytes for Wrapping<T>);
    unsafe_impl!(T: Unaligned => Unaligned for Wrapping<T>);
    assert_unaligned!(Wrapping<()>, Wrapping<u8>);
}
safety_comment! {
    // `MaybeUninit<T>` is `FromZeroes` and `FromBytes`, but never `AsBytes`
    // since it may contain uninitialized bytes.
    //
    /// SAFETY:
    /// - `FromZeroes`, `FromBytes`: `MaybeUninit<T>` has no restrictions on its
    ///   contents.
    /// - `Unaligned`: `MaybeUninit<T>` is guaranteed by its documentation [1]
    ///   to have the same alignment as `T`.
    ///
    /// [1] https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#layout-1
    unsafe_impl!(T => FromZeroes for MaybeUninit<T>);
    unsafe_impl!(T => FromBytes for MaybeUninit<T>);
    unsafe_impl!(T: Unaligned => Unaligned for MaybeUninit<T>);
    assert_unaligned!(MaybeUninit<()>, MaybeUninit<u8>);
}
safety_comment! {
    /// SAFETY:
    /// `ManuallyDrop` has the same layout as `T`, and accessing the inner value
    /// is safe (meaning that it's unsound to leave the inner value
    /// uninitialized while exposing the `ManuallyDrop` to safe code).
    /// - `FromZeroes`, `FromBytes`: Since it has the same layout as `T`, any
    ///   valid `T` is a valid `ManuallyDrop<T>`. If `T: FromZeroes`, a sequence
    ///   of zero bytes is a valid `T`, and thus a valid `ManuallyDrop<T>`. If
    ///   `T: FromBytes`, any sequence of bytes is a valid `T`, and thus a valid
    ///   `ManuallyDrop<T>`.
    /// - `AsBytes`: Since it has the same layout as `T`, and since it's unsound
    ///   to let safe code access a `ManuallyDrop` whose inner value is
    ///   uninitialized, safe code can only ever access a `ManuallyDrop` whose
    ///   contents are a valid `T`. Since `T: AsBytes`, this means that safe
    ///   code can only ever access a `ManuallyDrop` with all initialized bytes.
    /// - `Unaligned`: `ManuallyDrop` has the same layout (and thus alignment)
    ///   as `T`, and `T: Unaligned` guarantees that that alignment is 1.
    unsafe_impl!(T: ?Sized + FromZeroes => FromZeroes for ManuallyDrop<T>);
    unsafe_impl!(T: ?Sized + FromBytes => FromBytes for ManuallyDrop<T>);
    unsafe_impl!(T: ?Sized + AsBytes => AsBytes for ManuallyDrop<T>);
    unsafe_impl!(T: ?Sized + Unaligned => Unaligned for ManuallyDrop<T>);
    assert_unaligned!(ManuallyDrop<()>, ManuallyDrop<u8>);
}
safety_comment! {
    /// SAFETY:
    /// Per the reference [1]:
    ///
    ///   An array of `[T; N]` has a size of `size_of::<T>() * N` and the same
    ///   alignment of `T`. Arrays are laid out so that the zero-based `nth`
    ///   element of the array is offset from the start of the array by `n *
    ///   size_of::<T>()` bytes.
    ///
    ///   ...
    ///
    ///   Slices have the same layout as the section of the array they slice.
    ///
    /// In other words, the layout of a `[T]` or `[T; N]` is a sequence of `T`s
    /// laid out back-to-back with no bytes in between. Therefore, `[T]` or `[T;
    /// N]` are `FromZeroes`, `FromBytes`, and `AsBytes` if `T` is
    /// (respectively). Furthermore, since an array/slice has "the same
    /// alignment of `T`", `[T]` and `[T; N]` are `Unaligned` if `T` is.
    ///
    /// Note that we don't `assert_unaligned!` for slice types because
    /// `assert_unaligned!` uses `align_of`, which only works for `Sized` types.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#array-layout
    unsafe_impl!(T: FromZeroes, const N: usize => FromZeroes for [T; N]);
    unsafe_impl!(T: FromBytes, const N: usize => FromBytes for [T; N]);
    unsafe_impl!(T: AsBytes, const N: usize => AsBytes for [T; N]);
    unsafe_impl!(T: Unaligned, const N: usize => Unaligned for [T; N]);
    assert_unaligned!([(); 0], [(); 1], [u8; 0], [u8; 1]);
    unsafe_impl!(T: FromZeroes => FromZeroes for [T]);
    unsafe_impl!(T: FromBytes => FromBytes for [T]);
    unsafe_impl!(T: AsBytes => AsBytes for [T]);
    unsafe_impl!(T: Unaligned => Unaligned for [T]);
}

safety_comment! {
    /// SAFETY:
    /// Since `T: AsBytes`, we know that it's safe to construct a `&[u8]` from
    /// an aligned `&T`. Since `&[u8]` itself has no alignment requirements, it
    /// must also be safe to construct a `&[u8]` from a `&T` at any address.
    /// Since `Unalign<T>` is `#[repr(C, packed)]`, everything about its layout
    /// except for its alignment is the same as `T`'s layout.
    unsafe_impl!(T: AsBytes => AsBytes for Unalign<T>);
}
