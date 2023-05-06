//! SIMD support
//!
//! Per the Unsafe Code Guidelines Reference [1]:
//!
//!   Packed SIMD vector types are `repr(simd)` homogeneous tuple-structs
//!   containing `N` elements of type `T` where `N` is a power-of-two and the
//!   size and alignment requirements of `T` are equal:
//!
//!   ```rust
//!   #[repr(simd)]
//!   struct Vector<T, N>(T_0, ..., T_(N - 1));
//!   ```
//!
//!   ...
//!
//!   The size of `Vector` is `N * size_of::<T>()` and its alignment is an
//!   implementation-defined function of `T` and `N` greater than or equal to
//!   `align_of::<T>()`.
//!
//!   ...
//!
//!   Vector elements are laid out in source field order, enabling random access
//!   to vector elements by reinterpreting the vector as an array:
//!
//!   ```rust
//!   union U {
//!      vec: Vector<T, N>,
//!      arr: [T; N]
//!   }
//!
//!   assert_eq!(size_of::<Vector<T, N>>(), size_of::<[T; N]>());
//!   assert!(align_of::<Vector<T, N>>() >= align_of::<[T; N]>());
//!
//!   unsafe {
//!     let u = U { vec: Vector<T, N>(t_0, ..., t_(N - 1)) };
//!
//!     assert_eq!(u.vec.0, u.arr[0]);
//!     // ...
//!     assert_eq!(u.vec.(N - 1), u.arr[N - 1]);
//!   }
//!   ```
//!
//! Given this background, we can observe that:
//! - The size and bit pattern requirements of a SIMD type are equivalent to the
//!   equivalent array type. Thus, for any SIMD type whose primitive `T` is
//!   `FromZeroes`, `FromBytes`, or `AsBytes`, that SIMD type is also
//!   `FromZeroes`, `FromBytes`, or `AsBytes` respectively.
//! - Since no upper bound is placed on the alignment, no SIMD type can be
//!   guaranteed to be `Unaligned`.
//!
//! Also per [1]:
//!
//!   This chapter represents the consensus from issue #38. The statements in
//!   here are not (yet) "guaranteed" not to change until an RFC ratifies them.
//!
//! See issue #38 [2]. While this behavior is not technically guaranteed, the
//! likelihood that the behavior will change such that SIMD types are no longer
//! `FromZeroes`, `FromBytes`, or `AsBytes` is next to zero, as that would defeat
//! the entire purpose of SIMD types. Nonetheless, we put this behavior behind
//! the `simd` Cargo feature, which requires consumers to opt into this stability
//! hazard.
//!
//! [1] https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
//! [2] https://github.com/rust-lang/unsafe-code-guidelines/issues/38

/// Defines a module which implements `FromZeroes`, `FromBytes`, and
/// `AsBytes` for a set of types from a module in `core::arch`.
///
/// `$arch` is both the name of the defined module and the name of the
/// module in `core::arch`, and `$typ` is the list of items from that module
/// to implement `FromZeroes`, `FromBytes`, and `AsBytes` for.
#[allow(unused_macros)] // `allow(unused_macros)` is needed because some
                        // target/feature combinations don't emit any impls
                        // and thus don't use this macro.
macro_rules! simd_arch_mod {
    ($arch:ident, $($typ:ident),*) => {
        mod $arch {
            use core::arch::$arch::{$($typ),*};

            use crate::*;
            safety_comment! {
                /// SAFETY:
                /// See comment on module definition for justification.
                $( unsafe_impl!($typ: FromZeroes, FromBytes, AsBytes); )*
            }
        }
    };
}

#[cfg(target_arch = "x86")]
simd_arch_mod!(x86, __m128, __m128d, __m128i, __m256, __m256d, __m256i);
#[cfg(target_arch = "x86_64")]
simd_arch_mod!(x86_64, __m128, __m128d, __m128i, __m256, __m256d, __m256i);
#[cfg(target_arch = "wasm32")]
simd_arch_mod!(wasm32, v128);
#[cfg(all(feature = "simd-nightly", target_arch = "powerpc"))]
simd_arch_mod!(powerpc, vector_bool_long, vector_double, vector_signed_long, vector_unsigned_long);
#[cfg(all(feature = "simd-nightly", target_arch = "powerpc64"))]
simd_arch_mod!(
    powerpc64,
    vector_bool_long,
    vector_double,
    vector_signed_long,
    vector_unsigned_long
);
#[cfg(all(feature = "simd-nightly", target_arch = "aarch64"))]
#[rustfmt::skip]
simd_arch_mod!(
    aarch64, float32x2_t, float32x4_t, float64x1_t, float64x2_t, int8x8_t, int8x8x2_t,
    int8x8x3_t, int8x8x4_t, int8x16_t, int8x16x2_t, int8x16x3_t, int8x16x4_t, int16x4_t,
    int16x8_t, int32x2_t, int32x4_t, int64x1_t, int64x2_t, poly8x8_t, poly8x8x2_t, poly8x8x3_t,
    poly8x8x4_t, poly8x16_t, poly8x16x2_t, poly8x16x3_t, poly8x16x4_t, poly16x4_t, poly16x8_t,
    poly64x1_t, poly64x2_t, uint8x8_t, uint8x8x2_t, uint8x8x3_t, uint8x8x4_t, uint8x16_t,
    uint8x16x2_t, uint8x16x3_t, uint8x16x4_t, uint16x4_t, uint16x8_t, uint32x2_t, uint32x4_t,
    uint64x1_t, uint64x2_t
);
#[cfg(all(feature = "simd-nightly", target_arch = "arm"))]
#[rustfmt::skip]
simd_arch_mod!(arm, int8x4_t, uint8x4_t);
