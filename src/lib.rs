//! WAFFLE Wasm analysis framework.
//!
//! waffle is a *decompiler and compiler* library for WebAssembly: it
//! defines an SSA-based IR (intermediate representation), with a
//! frontend that translates Wasm to this IR, and a backend that
//! compiles this IR back to Wasm. It can be used by programs that
//! need to transform/modify or add new code to Wasm modules.
//!
//! A good starting point is the `Module`: it can be constructed from
//! Wasm bytecode in memory with `Module::from_wasm_bytes()` and
//! recompiled to Wasm with `Module::to_wasm_bytes()`, after
//! modifications are performed or new code is added. A new module can
//! also be built from scratch with `Module::empty()`.
#![allow(dead_code)]
#![no_std]
#![forbid(unsafe_code)]

// Re-export all the smaller crates
#[cfg(feature = "backend")]
pub use waffle_backend as backend;
pub use waffle_entity as entity;
#[cfg(feature = "frontend")]
pub use waffle_frontend as frontend;
pub use waffle_ir as ir;
pub use waffle_passes as passes;

#[cfg(feature = "copying")]
pub use waffle_copying as copying;
#[cfg(feature = "fuzzing")]
pub use waffle_fuzzing as fuzzing;
#[cfg(feature = "hooking")]
pub use waffle_hooking as hooking;

// Re-export wasmparser and wasm-encoder for easier use
pub use wasm_encoder;
pub use wasmparser;

// Re-export commonly used items to preserve existing API
#[cfg(feature = "backend")]
pub use waffle_backend::*;
pub use waffle_entity::*;
#[cfg(feature = "frontend")]
pub use waffle_frontend::*;
pub use waffle_ir::*;
pub use waffle_passes::*;

#[cfg(feature = "copying")]
pub use waffle_copying::*;
#[cfg(feature = "fuzzing")]
pub use waffle_fuzzing::*;
#[cfg(feature = "hooking")]
pub use waffle_hooking::*;

#[cfg(all(feature = "frontend", feature = "backend"))]
pub trait ModuleExt<'a>: backend::ModuleExt<'a> + frontend::ModuleExt<'a> {}
#[cfg(all(feature = "frontend", feature = "backend"))]
impl<'a, T: backend::ModuleExt<'a> + frontend::ModuleExt<'a>> ModuleExt<'a> for T {}
