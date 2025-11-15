//! Optimization passes for WAFFLE.
#![no_std]
#![forbid(unsafe_code)]
#![allow(dead_code)]

#[macro_use]
extern crate alloc;

// Re-export dependencies
pub use waffle_entity as entity;
pub use waffle_ir as ir;
pub use waffle_ir::*;
pub use waffle_ir::cfg::CFGInfo;
pub use waffle_passes_shared;

// #[cfg(feature = "copying")]
pub mod mapping;
// #[cfg(feature = "tcore")]
pub mod tcore;