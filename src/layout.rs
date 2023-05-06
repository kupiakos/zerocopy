//! Traits, conversions, and contracts related to size and alignment of types.
//!
//! [`crate::LayoutVerified`] is in `util` since it's a utility of both byte and layout-related
//! code.

mod runtime_align;
mod unalign;
mod unaligned;

pub(crate) use runtime_align::aligned_to;
pub use unalign::Unalign;
pub use unaligned::Unaligned;
