// Based on the typenum library.
// Some pieces are directly copied.

mod supported_sizes;
mod type_ops {
    use super::*;

    pub struct Less;
    pub struct Equal;
    pub struct Greater;

    mod internal {
        use super::*;
        pub trait PrivateCmp<Rhs, SoFar> {
            type Output;
        }
        pub type PrivateCmpOut<A, Rhs, SoFar> = <A as PrivateCmp<Rhs, SoFar>>::Output;

        pub trait IsLessOrEqualPrivate<Rhs, Cmp> {
            type Output: Bit;
        }
        impl<L, R> IsLessOrEqualPrivate<R, Less> for L {
            type Output = B<true>;
        }
        impl<L, R> IsLessOrEqualPrivate<R, Equal> for L {
            type Output = B<true>;
        }
        impl<L, R> IsLessOrEqualPrivate<R, Greater> for L {
            type Output = B<false>;
        }
    }
    use internal::*;

    pub trait Ord: sealed::Sealed {}
    impl sealed::Sealed for Less {}
    impl Ord for Less {}
    impl sealed::Sealed for Equal {}
    impl Ord for Equal {}
    impl sealed::Sealed for Greater {}
    impl Ord for Greater {}

    pub type Mul2<N> = Bits<N, false>;
    pub type Mul4<N> = Bits<Bits<N, false>, false>;
    pub type Mul8<N> = Bits<Bits<Bits<N, false>, false>, false>;

    /// A type operator for compparing `Self` and `Rhs`. Like [`Ord::cmp`] but for types.
    ///
    /// [`Ord::cmp`]: core::cmp::Ord::cmp
    pub trait Cmp<Rhs = Self> {
        /// The result. Should only ever be [`Greater`], [`Less`], or [`Equal`].
        type Output;
    }

    pub trait IsLessOrEqual<Rhs = Self> {
        // type Output: Bit;
    }
    impl<L, R> IsLessOrEqual<R> for L
    where
        L: Cmp<R> + IsLessOrEqualPrivate<R, <L as Cmp<R>>::Output>,
        <L as IsLessOrEqualPrivate<R, <L as Cmp<R>>::Output>>::Output: IsTrue,
    {
    }

    pub trait IsTrue: sealed::Sealed {}
    impl IsTrue for B<true> {}

    impl Cmp<Zero> for Zero {
        /// Zero == Zero
        type Output = Equal;
    }
    impl Cmp<B<false>> for B<false> {
        /// 0 == 0
        type Output = Equal;
    }
    impl Cmp<B<true>> for B<true> {
        /// 1 == 1
        type Output = Equal;
    }
    impl Cmp<B<false>> for B<true> {
        /// 1 > 0
        type Output = Greater;
    }
    impl Cmp<B<true>> for B<false> {
        /// 0 < 1
        type Output = Less;
    }
    impl<Rest: Num, const SET: bool> Cmp<Bits<Rest, SET>> for Zero {
        /// Zero < Nonzero
        type Output = Less;
    }
    impl<Rest: Num, const SET: bool> Cmp<Zero> for Bits<Rest, SET> {
        /// Nonzero > Zero
        type Output = Greater;
    }
    // Does consolidating this impl with the next one help or hurt perf? Similarly below.
    impl<RestLeft, RestRight: Num> Cmp<Bits<RestRight, false>> for Bits<RestLeft, false>
    where
        RestLeft: PrivateCmp<RestRight, Equal> + Num,
    {
        /// Bits<RestLeft, false> cmp Bits<RestRight, false>: SoFar=Equal
        type Output = PrivateCmpOut<RestLeft, RestRight, Equal>;
    }
    impl<RestLeft, RestRight: Num> Cmp<Bits<RestRight, true>> for Bits<RestLeft, true>
    where
        RestLeft: PrivateCmp<RestRight, Equal> + Num,
    {
        /// Bits<RestLeft, true> cmp Bits<RestRight, true>: SoFar=Equal
        type Output = PrivateCmpOut<RestLeft, RestRight, Equal>;
    }
    impl<RestLeft, RestRight: Num> Cmp<Bits<RestRight, false>> for Bits<RestLeft, true>
    where
        RestLeft: PrivateCmp<RestRight, Greater> + Num,
    {
        /// Bits<RestLeft, 1> cmp Bits<RestRight, 0>: SoFar=Greater
        type Output = PrivateCmpOut<RestLeft, RestRight, Greater>;
    }
    impl<RestLeft, RestRight: Num> Cmp<Bits<RestRight, true>> for Bits<RestLeft, false>
    where
        RestLeft: PrivateCmp<RestRight, Less> + Num,
    {
        /// Bits<RestLeft, 0> cmp Bits<RestRight, 1>: SoFar=Less
        type Output = PrivateCmpOut<RestLeft, RestRight, Less>;
    }

    /// Comparing non-terimal bits, with both having bit `false`.
    /// These are `Equal`, so we propagate `SoFar`.
    impl<RestLeft, RestRight, SoFar> PrivateCmp<Bits<RestRight, false>, SoFar> for Bits<RestLeft, false>
    where
        RestLeft: Num,
        RestRight: Num,
        SoFar: Ord,
        RestLeft: PrivateCmp<RestRight, SoFar>,
    {
        type Output = PrivateCmpOut<RestLeft, RestRight, SoFar>;
    }

    /// Comparing non-terimal bits, with both having bit `true`.
    /// These are `Equal`, so we propagate `SoFar`.
    impl<RestLeft, RestRight, SoFar> PrivateCmp<Bits<RestRight, true>, SoFar> for Bits<RestLeft, true>
    where
        RestLeft: Num,
        RestRight: Num,
        SoFar: Ord,
        RestLeft: PrivateCmp<RestRight, SoFar>,
    {
        type Output = PrivateCmpOut<RestLeft, RestRight, SoFar>;
    }

    /// Comparing non-terimal bits, with `Lhs` having bit `false` and `Rhs` having bit `true`.
    /// `SoFar`, Lhs is `Less`.
    impl<RestLeft, RestRight, SoFar> PrivateCmp<Bits<RestRight, true>, SoFar> for Bits<RestLeft, false>
    where
        RestLeft: Num,
        RestRight: Num,
        SoFar: Ord,
        RestLeft: PrivateCmp<RestRight, Less>,
    {
        type Output = PrivateCmpOut<RestLeft, RestRight, Less>;
    }

    /// Comparing non-terimal bits, with `Lhs` having bit `true` and `Rhs` having bit `false`.
    /// `SoFar`, Lhs is `Greater`.
    impl<RestLeft, RestRight, SoFar> PrivateCmp<Bits<RestRight, false>, SoFar> for Bits<RestLeft, true>
    where
        RestLeft: Num,
        RestRight: Num,
        SoFar: Ord,
        RestLeft: PrivateCmp<RestRight, Greater>,
    {
        type Output = PrivateCmpOut<RestLeft, RestRight, Greater>;
    }

    /// Got to the end of just the `Lhs`. It's `Less`.
    impl<U: Num, SoFar: Ord, const SET: bool> PrivateCmp<Bits<U, SET>, SoFar> for Zero {
        type Output = Less;
    }

    /// Got to the end of just the `Rhs`. `Lhs` is `Greater`.
    impl<U: Num, SoFar: Ord, const SET: bool> PrivateCmp<Zero, SoFar> for Bits<U, SET> {
        type Output = Greater;
    }

    /// Got to the end of both! Return `SoFar`
    impl<SoFar: Ord> PrivateCmp<Zero, SoFar> for Zero {
        type Output = SoFar;
    }
}
use type_ops::*;

/// The terminating type for `Bits`; it always comes after the most significant bit.
pub struct Zero;

type SizeBits<T> = <<T as KnownSize>::Size as SupportedSize>::Bits;

pub trait CompatibleSize<To: KnownSize>: KnownSize {
    fn bytecast_ref(&self) -> &To {
        unsafe { &*(self as *const _ as *const To) }
    }
}
impl<From, To> CompatibleSize<To> for From
where
    From: KnownSize,
    To: KnownSize,
    SizeBits<To>: IsLessOrEqual<SizeBits<From>>,
{
}

/// `B` for "bit".
///
/// Implements `Bit`.
/// Used as a concrete type when typechecking a bit.
#[derive(Clone, Copy, Default)]
pub struct B<const SET: bool>;

mod sealed {
    pub trait Sealed {}
}

pub trait Bit: Copy + Default + sealed::Sealed + 'static {
    const SET: bool;
}
impl<const SET: bool> sealed::Sealed for B<SET> {}
impl<const SET: bool> Bit for B<SET> {
    const SET: bool = SET;
}

/// Represents the bits of a non-zero number.
///
/// There are no leading zeroes, and `Zero` represents 0, so `Bits<Zero, false>` is not allowed.
/// This means `Bits` always represents a non-zero number.
pub struct Bits<Rest, const SET: bool>(Rest);

pub trait Num: sealed::Sealed {}
impl sealed::Sealed for Zero {}
impl Num for Zero {}
impl<Rest: Num, const SET: bool> sealed::Sealed for Bits<Rest, SET> {}
impl<Rest: Num, const SET: bool> Num for Bits<Rest, SET> {}

pub struct SizeOf<const N: usize>;

pub unsafe trait KnownSize {
    type Size: SupportedSize;
}

pub unsafe trait SupportedSize {
    type Bits: Num;
    // type Array;
}

unsafe impl<B: Num> SupportedSize for B {
    type Bits = B;
}

unsafe impl SupportedSize for SizeOf<0> {
    type Bits = Zero;
}

unsafe impl SupportedSize for SizeOf<1> {
    type Bits = Bits<Zero, true>;
}

unsafe impl SupportedSize for SizeOf<2> {
    type Bits = Bits<Bits<Zero, true>, false>;
}

unsafe impl SupportedSize for SizeOf<3> {
    type Bits = Bits<Bits<Zero, true>, true>;
}

unsafe impl SupportedSize for SizeOf<4> {
    type Bits = Bits<Bits<Bits<Zero, true>, false>, false>;
}

unsafe impl SupportedSize for SizeOf<5> {
    type Bits = Bits<Bits<Bits<Zero, true>, false>, true>;
}
unsafe impl SupportedSize for SizeOf<6> {
    type Bits = Bits<Bits<Bits<Zero, true>, true>, false>;
}
unsafe impl SupportedSize for SizeOf<7> {
    type Bits = Bits<Bits<Bits<Zero, true>, true>, true>;
}
unsafe impl SupportedSize for SizeOf<8> {
    type Bits = Bits<Bits<Bits<Bits<Zero, true>, false>, false>, false>;
}

// TODO: type multiplication will allow for conversion between arrays of `SupportedSize`.
// For now, known sizes for arrays of integers

unsafe impl KnownSize for u8 {
    type Size = SizeOf<1>;
}

unsafe impl KnownSize for u16 {
    type Size = SizeOf<2>;
}

unsafe impl KnownSize for u32 {
    type Size = SizeOf<4>;
}

unsafe impl<const N: usize> KnownSize for [u8; N]
where
    SizeOf<N>: SupportedSize,
{
    type Size = SizeOf<N>;
}

unsafe impl<const N: usize> KnownSize for [u16; N]
where
    SizeOf<N>: SupportedSize,
{
    type Size = Mul2<<SizeOf<N> as SupportedSize>::Bits>;
}

unsafe impl<const N: usize> KnownSize for [u32; N]
where
    SizeOf<N>: SupportedSize,
{
    type Size = Mul4<<SizeOf<N> as SupportedSize>::Bits>;
}

// fn cast_ref_with_less_size<T, U>(lhs: &T) -> &U
// where
//     T: KnownSize,
//     U: KnownSize,
// {
// }

// type Out = [u8; 3];  /* compiles, smaller size */
type Out = [u8; 4]; /* compiles, same size */
// type Out = [u8; 5]; /* fails to compile, larger size */
fn test_cast(lhs: &u32) -> &[u16; 2] {
    lhs.bytecast_ref()
}
