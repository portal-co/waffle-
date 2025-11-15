//! Type-safe indices and indexed containers for WAFFLE.
#![no_std]
#![forbid(unsafe_code)]

#[macro_use]
extern crate alloc;

// Re-export arena_traits for use by other crates
pub use arena_traits;

pub mod entity;
pub mod pool;
pub mod entities;

pub use entity::*;
pub use pool::*;
