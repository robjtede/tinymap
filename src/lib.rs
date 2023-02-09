#![forbid(unsafe_code)]
#![allow(clippy::redundant_pattern_matching)] // I'm trying to reduce the amount of LLVM IR output
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod array_map;
#[cfg(feature = "alloc")]
pub mod tiny_map;

pub use array_map::ArrayMap;
#[cfg(feature = "alloc")]
pub use tiny_map::TinyMap;
