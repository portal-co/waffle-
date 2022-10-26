//! WAFFLE Wasm analysis framework.

#![allow(dead_code)]

// Re-export wasmparser for easier use of the right version by our embedders.
pub use wasmparser;

mod backend;
mod cfg;
mod frontend;
mod ir;
mod op_traits;
mod ops;
mod use_count;

pub use ir::*;
pub use ops::Operator;
