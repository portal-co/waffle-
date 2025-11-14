//! Core IR (Intermediate Representation) for WAFFLE Wasm analysis framework.
#![no_std]
#![forbid(unsafe_code)]
#![allow(dead_code)]

#[macro_use]
extern crate alloc;

// Re-export waffle-entity
pub use waffle_entity as entity;
pub use waffle_entity::*;

// Re-export wasmparser and wasm-encoder for easier use
pub use wasmparser;
pub use wasm_encoder;

pub mod cfg;
mod errors;
// First define basic types and entity declarations
#[path = "ir_types.rs"]
mod ir_types;
// Then import ir module which depends on those types
pub mod ir;
// Then import subtypes which depends on both
#[path = "ir_subtypes.rs"]
mod ir_subtypes;
pub mod op_traits;
mod ops;
pub mod scoped_map;
mod interp;
pub mod util;

pub use errors::*;
pub use ir_types::*;
pub use ir::*;
pub use ir_subtypes::*;
pub use op_traits::SideEffect;
pub use ops::{Ieee32, Ieee64, MemoryArg, Operator};
pub use interp::*;

#[cfg(feature = "ssa-traits-02")]
mod ssa_traits_impls_02;
#[cfg(feature = "ssa-traits-03")]
mod ssa_traits_impls_03;

#[doc(hidden)]
pub mod td;
