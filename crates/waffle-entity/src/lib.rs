//! Type-safe indices and indexed containers for WAFFLE.
#![no_std]
#![forbid(unsafe_code)]

#[macro_use]
extern crate alloc;

pub mod entity;
pub mod pool;

pub use entity::*;
pub use pool::*;
