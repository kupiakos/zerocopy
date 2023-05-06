// Copyright 2018 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// After updating the following doc comment, make sure to run the following
// command to update `README.md` based on its contents:
//
//   ./generate-readme.sh > README.md

//! Utilities for safe zero-copy parsing and serialization.
//!
//! This crate provides utilities which make it easy to perform zero-copy
//! parsing and serialization by allowing zero-copy conversion to/from byte
//! slices.
//!
//! This is enabled by four core marker traits, each of which can be derived
//! (e.g., `#[derive(FromBytes)]`):
//! - [`FromZeroes`] indicates that a sequence of zero bytes represents a valid
//!   instance of a type
//! - [`FromBytes`] indicates that a type may safely be converted from an
//!   arbitrary byte sequence
//! - [`AsBytes`] indicates that a type may safely be converted *to* a byte
//!   sequence
//! - [`Unaligned`] indicates that a type's alignment requirement is 1
//!
//! Types which implement a subset of these traits can then be converted to/from
//! byte sequences with little to no runtime overhead.
//!
//! Note that these traits are ignorant of byte order. For byte order-aware
//! types, see the [`byteorder`] module.
//!
//! # Features
//!
//! `alloc`: By default, `zerocopy` is `no_std`. When the `alloc` feature is
//! enabled, the `alloc` crate is added as a dependency, and some
//! allocation-related functionality is added.
//!
//! `byteorder` (enabled by default): Adds the [`byteorder`] module and a
//! dependency on the `byteorder` crate. The `byteorder` module provides byte
//! order-aware equivalents of the multi-byte primitive numerical types. Unlike
//! their primitive equivalents, the types in this module have no alignment
//! requirement and support byte order conversions. This can be useful in
//! handling file formats, network packet layouts, etc which don't provide
//! alignment guarantees and which may use a byte order different from that of
//! the execution platform.
//!
//! `simd`: When the `simd` feature is enabled, `FromZeroes`, `FromBytes`, and
//! `AsBytes` impls are emitted for all stable SIMD types which exist on the
//! target platform. Note that the layout of SIMD types is not yet stabilized,
//! so these impls may be removed in the future if layout changes make them
//! invalid. For more information, see the Unsafe Code Guidelines Reference page
//! on the [Layout of packed SIMD vectors][simd-layout].
//!
//! `simd-nightly`: Enables the `simd` feature and adds support for SIMD types
//! which are only available on nightly. Since these types are unstable, support
//! for any type may be removed at any point in the future.
//!
//! [simd-layout]: https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html

// Sometimes we want to use lints which were added after our MSRV.
// `unknown_lints` is `warn` by default and we deny warnings in CI, so without
// this attribute, any unknown lint would cause a CI failure when testing with
// our MSRV.
#![allow(unknown_lints)]
#![deny(renamed_and_removed_lints)]
#![deny(
    anonymous_parameters,
    deprecated_in_future,
    illegal_floating_point_literal_pattern,
    late_bound_lifetime_arguments,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    path_statements,
    patterns_in_fns_without_body,
    rust_2018_idioms,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused_extern_crates,
    unused_qualifications,
    variant_size_differences
)]
#![deny(
    clippy::all,
    clippy::alloc_instead_of_core,
    clippy::arithmetic_side_effects,
    clippy::as_underscore,
    clippy::assertions_on_result_states,
    clippy::as_conversions,
    clippy::correctness,
    clippy::dbg_macro,
    clippy::decimal_literal_representation,
    clippy::get_unwrap,
    clippy::indexing_slicing,
    clippy::obfuscated_if_else,
    clippy::perf,
    clippy::print_stdout,
    clippy::std_instead_of_core,
    clippy::style,
    clippy::suspicious,
    clippy::todo,
    clippy::undocumented_unsafe_blocks,
    clippy::unimplemented,
    clippy::unnested_or_patterns,
    clippy::unwrap_used,
    clippy::use_debug
)]
#![deny(
    rustdoc::bare_urls,
    rustdoc::broken_intra_doc_links,
    rustdoc::invalid_codeblock_attributes,
    rustdoc::invalid_html_tags,
    rustdoc::invalid_rust_codeblocks,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_intra_doc_links
)]
// In test code, it makes sense to weight more heavily towards concise, readable
// code over correct or debuggable code.
#![cfg_attr(test, allow(
    // In tests, you get line numbers and have access to source code, so panic
    // messages are less important. You also often unwrap a lot, which would
    // make expect'ing instead very verbose.
    clippy::unwrap_used,
    // In tests, there's no harm to "panic risks" - the worst that can happen is
    // that your test will fail, and you'll fix it. By contrast, panic risks in
    // production code introduce the possibly of code panicking unexpectedly "in
    // the field".
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
))]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "simd-nightly", feature(stdsimd))]

mod bytes;
#[doc(hidden)]
pub mod derive_util;
mod impls;
mod layout;
pub(crate) mod sealed;
#[cfg(feature = "simd")]
mod simd;
#[cfg(test)]
mod tests;
mod util;

pub use bytes::{AsBytes, ByteSlice, ByteSliceMut, FromBytes, FromZeroes};
pub use layout::{Unalign, Unaligned};
pub(crate) use sealed::Sealed;
pub use util::LayoutVerified;

#[cfg(feature = "alloc")]
pub use util::alloc_support::*;

#[cfg(feature = "byteorder")]
pub use util::byteorder;

#[cfg(feature = "byteorder")]
pub use crate::byteorder::*;
pub use zerocopy_derive::*;

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use {
    alloc::boxed::Box,
    alloc::vec::Vec,
    core::{alloc::Layout, ptr::NonNull},
};

// This allows derives of `FromZeroes`, `FromBytes`, `AsBytes`, and `Unaligned` to work in this
// crate, since they reference the name `zerocopy`.
extern crate self as zerocopy;

/// Used in [`transmute!`] below.
#[doc(hidden)]
pub use core::mem::transmute as __real_transmute;
