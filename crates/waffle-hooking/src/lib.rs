//! Hooking functionality for WAFFLE.
#![no_std]
#![forbid(unsafe_code)]
#![allow(dead_code)]

#[macro_use]
extern crate alloc;

// Re-export dependencies
pub use waffle_entity as entity;
pub use waffle_ir as ir;
pub use waffle_ir::*;

mod hooking;
pub use hooking::*;
