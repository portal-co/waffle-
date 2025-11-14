//! Backend: convert IR to Wasm for WAFFLE.
#![no_std]
#![forbid(unsafe_code)]
#![allow(dead_code)]

#[macro_use]
extern crate alloc;

use alloc::vec::Vec;
use anyhow::Result;

// Re-export dependencies
pub use waffle_entity as entity;
pub use waffle_ir as ir;
pub use waffle_ir::*;
pub use waffle_ir::cfg::CFGInfo;
pub use waffle_passes_shared;

pub mod backend;
pub use backend::*;

/// Compile a WAFFLE Module to Wasm bytes.
pub fn to_wasm_bytes(module: &Module<'_>) -> Result<Vec<u8>> {
    backend::compile(module).map(|m| m.finish())
}

/// Compile a WAFFLE Module to a wasm_encoder::Module.
pub fn to_encoded_module(module: &Module<'_>) -> Result<wasm_encoder::Module> {
    backend::compile(module)
}

pub trait ModuleExt<'a>{
    fn module(&self) -> &Module<'a>;
    fn to_wasm_bytes(&self) -> Result<Vec<u8>>{
        return to_wasm_bytes(self.module());
    }
    fn to_encoded_module(&self) -> Result<wasm_encoder::Module>{
        return to_encoded_module(self.module());
    }
}
impl<'a> ModuleExt<'a> for Module<'a>{
    fn module(&self) -> &Module<'a> {
        self
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn empty_module_valid() {
        let module = Module::empty();
        let _ = module.to_wasm_bytes().unwrap();
    }
}
