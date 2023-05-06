//! [Sealed trait pattern][sealed]
//!
//! [sealed]: https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed

use core::cell::{Ref, RefMut};

pub trait Sealed {}
impl<'a> Sealed for &'a [u8] {}
impl<'a> Sealed for &'a mut [u8] {}
impl<'a> Sealed for Ref<'a, [u8]> {}
impl<'a> Sealed for RefMut<'a, [u8]> {}
