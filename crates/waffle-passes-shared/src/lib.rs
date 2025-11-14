//! Shared optimization passes for WAFFLE (used by both backend and passes crates).
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

pub mod maxssa;
pub mod resolve_aliases;

pub use maxssa::*;
pub use resolve_aliases::*;
