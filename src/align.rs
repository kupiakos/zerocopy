use core::{marker::PhantomData, ops::{Deref, DerefMut}};

use crate::{AsBytes, FromBytes};



// List alignments from lowest to highest
macro_rules! impl_align_types {
    ($($align:literal),* $(,)?) => {
        impl_align_types!(@impl $($align),*; );
    };
    (@impl ; $($_lesser:literal),*) => {};
    (@impl $align:literal $(, $rest:literal)*; $($lesser:literal),* $(,)?) => {
        // nest recursively in modules so the `Align` type doesn't clash
        // is there a better way to do this that's not a proc macro?
        pub(crate) mod nest {
            use super::{AlignOf, Aligned, LeqAlign, KnownAlign, SupportedAlign};

            // Different types created for each alignment with different nesting.
            #[repr(C, align($align))]
            pub struct Align([u8; 0]);
            unsafe impl SupportedAlign for AlignOf<$align> {
                type AlignZst = Align;
            }
            unsafe impl KnownAlign for AlignOf<$align> {
                type Align = AlignOf<$align>;
            }
            unsafe impl Aligned<$align> for AlignOf<$align> {}
            // unsafe impl LesserAlign<AlignOf<$align>> for AlignOf<$align> {}
            // $(
            //     unsafe impl GreaterAlign<AlignOf<$align>> for AlignOf<$lesser> {}
            // )*
            impl_align_types!(@impl chain $align; $($lesser),*);
            impl_align_types!(@impl $($rest),*; $align, $($lesser),*);
        }
    };
    (@impl chain $align:literal; $prev:literal $(,$_lesser:literal)* $(,)?) => {
        unsafe impl<T> LeqAlign<AlignOf<$prev>> for T where T: LeqAlign<AlignOf<$align>> {}
    };
    (@impl chain $align:literal; $(,$_lesser:literal)* $(,)?) => {};
}

impl_align_types!(1,2,4,8,16,32,64);


/// Represents an alignment of `N` bytes.
///
/// This is also a zero sized type with an alignment of `N` bytes.
pub struct AlignOf<const N: usize>(<Self as SupportedAlign>::AlignZst) where AlignOf<N>: SupportedAlign;

pub unsafe trait SupportedAlign {
    type AlignZst;
}

/// `Self` represents a same or lower alignment compared to `To`.
unsafe trait LeqAlign<To> {}
// unsafe impl 
// unsafe trait GreaterAlign<To> {}

// any type is LesserAlign<To> if its alignment is greater than `To`s

unsafe impl<const N: usize> LeqAlign<AlignOf<N>> for AlignOf<N> where AlignOf<N>: SupportedAlign {}
// unsafe impl<T> LeqAlign<AlignOf<1>> for T where T: LeqAlign<AlignOf<2>> {}
// unsafe impl<T> LeqAlign<AlignOf<2>> for T where T: LeqAlign<AlignOf<4>> {}
// unsafe impl<T> LeqAlign<AlignOf<4>> for T where T: LeqAlign<AlignOf<8>> {}



// unsafe impl<A, To> LesserAlign<To> for A
// where
//     A: Aligned<2>,
//     To: Aligned<2>,
// {}

// unsafe impl<A: SupportedAlign, To> LesserAlign<To> for A
// where To: GreaterAlign<A> {}

/// Align a `T` on a `N` byte boundary, possibly introducing padding.
///
/// The compiler will always see the `T` as aligned on this boundary at compile time.
#[repr(C)]
pub struct Align<T, const N: usize> where AlignOf<N>: SupportedAlign {
    /// This makes `Self` aligned on `N` bytes. This might introduce tail padding.
    align: AlignOf<N>,

    /// The wrapped value.
    value: T,
}

/// A reference to `T` that has a checked alignment of N bytes.
///
/// This is different than `Align<T>` because it doesn't change the alignment of `T` from Rust's
/// perspective or ever require additional padding, it just represents a check of a reference's
/// alignment.
#[repr(transparent)]
struct CheckedAlign<T: ?Sized, const N: usize>(T);

impl<T: ?Sized, const N: usize> Deref for CheckedAlign<T, N> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized, const N: usize> DerefMut for CheckedAlign<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}


/// `Self` has an alignment requirement of `N` bytes.
pub unsafe trait Aligned<const N: usize>
where AlignOf<N>: SupportedAlign
{
}

pub unsafe trait KnownAlign {
    type Align: SupportedAlign;
}

// this is "does there exist an `N` that `T` and `U` are aligned on"
// which is always true
// i need "this has a looser alignment than the destination"
fn cast_ref<T, U>(x: &T) -> &U
where
    T: AsBytes,
    U: FromBytes + LeqAlign<T>,
{

    unsafe { &*(x as *const _ as *const U) }
}


// fn good_cast(x: &u32) -> &[u16; 2] {
//     cast_ref(x)
// }



// unsafe impl Aligned<{core::mem::align_of::<u8>()}> for u8 {}
// unsafe impl Aligned<{core::mem::align_of::<u16>()}> for u16 {}
// unsafe impl Aligned<{core::mem::align_of::<[u16; 2]>()}> for [u16; 2] {}
// unsafe impl Aligned<{core::mem::align_of::<u32>()}> for u32 {}

