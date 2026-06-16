//! Frontend: convert Wasm to IR for WAFFLE.
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

mod frontend;
pub use frontend::*;
pub use wax_core::build::OperatorSink;

/// Parse a WebAssembly module from bytes into a WAFFLE Module.
pub fn from_wasm_bytes<'a>(bytes: &'a [u8], options: &FrontendOptions) -> Result<Module<'a>> {
    wasm_to_ir(bytes, options)
}

/// Expand a function body, parsing its lazy reference to original bytecode into IR if needed.
pub fn expand_func<'a, 'b>(module: &'b mut Module<'a>, id: Func) -> Result<&'b mut FuncDecl<'a>> {
     #[cfg(feature = "backend")]
    if let FuncDecl::Compiled(..) = module.funcs[id] {
        module.funcs[id].clone().decompile(|mut func| {
            let mut func = module.funcs[id].clone();
            parse_func_decl(&mut func, module)?;
            module.funcs[id] = func;
            anyhow::Ok(())
        })?;
    }
    if let FuncDecl::Lazy(..) = module.funcs[id] {
        // End the borrow. This is cheap (a slice copy).
        let mut func = module.funcs[id].clone();
        parse_func_decl(&mut func, module)?;
        module.funcs[id] = func;
    }
    Ok(&mut module.funcs[id])
}

/// Helper function to parse a FuncDecl in place.
fn parse_func_decl<'a>(func_decl: &mut FuncDecl<'a>, module: &Module<'a>) -> Result<()> {
    match func_decl {
        FuncDecl::Lazy(sig, name, body) => {
            let parsed_body = parse_body(module, *sig, body)?;
            *func_decl = FuncDecl::Body(*sig, name.clone(), parsed_body);
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Clone a function body without expanding it, and return a new function body with IR expanded.
pub fn clone_and_expand_body<'a>(module: &Module<'a>, id: Func) -> Result<FunctionBody> {
    let mut body = module.funcs[id].clone();
    parse_func_decl(&mut body, module)?;
    Ok(match body {
        FuncDecl::Body(_, _, body) => body,
        _ => unreachable!(),
    })
}

/// For all functions that are lazy references to initial bytecode, expand them into IR.
pub fn expand_all_funcs<'a>(module: &mut Module<'a>) -> Result<()> {
    for id in 0..module.funcs.len() {
        let id = Func::new(id);
        expand_func(module, id)?;
    }
    Ok(())
}

pub trait ModuleExt<'a>: Sized {
    fn module(&self) -> &Module<'a>;
    fn module_mut(&mut self) -> &mut Module<'a>;
    fn from_wasm_bytes(bytes: &'a [u8], options: &FrontendOptions) -> Result<Self>;
    fn expand_all_funcs(&mut self) -> Result<()> {
        expand_all_funcs(self.module_mut())
    }
}
impl<'a> ModuleExt<'a> for Module<'a> {
    fn module(&self) -> &Module<'a> {
        self
    }

    fn module_mut(&mut self) -> &mut Module<'a> {
        self
    }

    fn from_wasm_bytes(bytes: &'a [u8], options: &FrontendOptions) -> Result<Self> {
        from_wasm_bytes(bytes, options)
    }
}
