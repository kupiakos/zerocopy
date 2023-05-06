//! Utilities that take advantage of both byte and layout properties of `zerocopy`.

#[cfg(feature = "alloc")]
pub(crate) mod alloc_support;

#[cfg(feature = "byteorder")]
pub mod byteorder;
mod layout_verified;
mod transmute;

pub use layout_verified::LayoutVerified;
