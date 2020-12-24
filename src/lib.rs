//! String types for XML.
#![warn(rust_2018_idioms)]
// `clippy::missing_docs_in_private_items` implies `missing_docs`.
#![warn(clippy::missing_docs_in_private_items)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
mod macros;

pub mod names;
