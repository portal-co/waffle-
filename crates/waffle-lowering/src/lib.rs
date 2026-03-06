//! Memory-lowering passes for WAFFLE.
#![no_std]
#![forbid(unsafe_code)]
#![allow(dead_code)]

#[macro_use]
extern crate alloc;

pub use waffle_passes::entity;
pub use waffle_passes::ir;

pub mod mem_fusing;
pub mod unmem;
