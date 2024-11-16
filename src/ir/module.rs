use std::collections::BTreeMap;
use std::iter::{empty, once};

use super::{ControlTag, Func, FuncDecl, Global, Memory, ModuleDisplay, Signature, Table, Type};
use crate::entity::{EntityRef, EntityVec};
use crate::ir::{Debug, DebugMap, FunctionBody};
use crate::{backend, frontend};
use anyhow::Result;
use either::Either;
use indexmap::IndexMap;

pub use crate::frontend::FrontendOptions;

#[derive(Clone, Debug)]
pub struct Module<'a> {
    /// The original Wasm module this module was parsed from, if
    /// any. Used only for "lazy function bodies", which retain a
    /// range that can refer into this slice.
    pub orig_bytes: Option<&'a [u8]>,
    /// The functions in this module: imports, un-expanded ("lazily
    /// parsed") functions, functions as IR, or IR compiled into new
    /// bytecode.
    pub funcs: EntityVec<Func, FuncDecl<'a>>,
    /// Type signatures, referred to by `funcs`, `imports` and
    /// `exports`.
    pub signatures: EntityVec<Signature, SignatureData>,
    /// Global variables in this module.
    pub globals: EntityVec<Global, GlobalData>,
    /// Tables in this module.
    pub tables: EntityVec<Table, TableData>,
    /// Imports into this module. Function imports must also have an
    /// entry at the appropriate function index in `funcs`.
    pub imports: Vec<Import>,
    /// Exports from this module.
    pub exports: Vec<Export>,
    /// Memories/heapds that this module contains.
    pub memories: EntityVec<Memory, MemoryData>,
    /// Control tags that this module contains
    pub control_tags: EntityVec<ControlTag, ControlTagData>,
    /// The "start function" invoked at instantiation, if any.
    pub start_func: Option<Func>,
    /// Debug-info associated with function bodies: interning pools
    /// for source file names and locations in those files.
    pub debug: Debug,
    /// Maps from original Wasm bytecode offsets to source locations.
    pub debug_map: DebugMap,
    pub custom_sections: BTreeMap<String, Vec<u8>>,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ControlTagData {
    ///The signature used when invoking this tag
    pub sig: Signature,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignatureData {
    /// Parameters: a Wasm function may have zero or more primitive
    /// types as parameters.
    pub params: Vec<Type>,
    /// Returns: a Wasm function (when using the multivalue extension,
    /// which we assume to be present) may have zero or more primitive
    /// types as return values.
    pub returns: Vec<Type>,
}

/// The size of a single Wasm page, used in memory definitions.
pub const WASM_PAGE: usize = 0x1_0000; // 64KiB

/// A memory definition.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryData {
    /// How many Wasm pages (64KiB size) in the initial memory size?
    pub initial_pages: usize,
    /// How many Wasm pages (64KiB size) in the maximum memory size?
    pub maximum_pages: Option<usize>,
    /// Initialization data (initial image) for this memory.
    pub segments: Vec<MemorySegment>,
    pub memory64: bool,
    pub shared: bool,
    pub page_size_log2: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemorySegment {
    /// The offset of this data.
    pub offset: usize,
    /// The data, overlaid on previously-existing data at this offset.
    pub data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TableData {
    /// The type of element in this table.
    pub ty: Type,
    pub initial: u64,
    /// The maximum size (in elements), if any, of this table.
    pub max: Option<u64>,
    /// If this is a table of function references, the initial
    /// contents of the table. `null` funcrefs are represented by
    /// `Func::invalid()`.
    pub func_elements: Option<Vec<Func>>,
    pub table64: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalData {
    /// The type of this global variable.
    pub ty: Type,
    /// The initial value of this global variable, as a bundle of 64
    /// bits (all primitive types, `i32`/`i64`/`f32`/`f64`, can be
    /// represented in this way).
    pub value: Option<u64>,
    /// Whether this global variable is mutable.
    pub mutable: bool,
}

impl From<&wasmparser::FuncType> for SignatureData {
    fn from(fty: &wasmparser::FuncType) -> Self {
        Self {
            params: fty
                .params()
                .iter()
                .map(|&ty| ty.into())
                .collect::<Vec<Type>>(),
            returns: fty
                .results()
                .iter()
                .map(|&ty| ty.into())
                .collect::<Vec<Type>>(),
        }
    }
}
impl From<wasmparser::FuncType> for SignatureData {
    fn from(fty: wasmparser::FuncType) -> Self {
        (&fty).into()
    }
}

impl From<&SignatureData> for wasm_encoder::SubType {
    fn from(value: &SignatureData) -> Self {
        wasm_encoder::SubType {
            is_final: true,
            supertype_idx: None,
            composite_type: wasm_encoder::CompositeType::Func(wasm_encoder::FuncType::new(
                value.params.iter().cloned().map(|a| a.into()),
                value.returns.iter().cloned().map(|a| a.into()),
            )),
        }
    }
}

impl Signature {
    pub fn recurses(&self, module: &Module) -> bool {
        return match &module.signatures[*self] {
            SignatureData { params, returns } => params
                .iter()
                .chain(returns.iter())
                .flat_map(|a| a.sigs())
                .any(|sig| sig.index() >= self.index()),
        };
    }
}

impl Type {
    pub fn sigs<'a>(&'a self) -> impl Iterator<Item = Signature> + 'a {
        match self {
            Type::TypedFuncRef {
                nullable,
                sig_index,
            } => Either::Right(once(*sig_index)),
            _ => Either::Left(empty()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Import {
    /// The name of the module the import comes from.
    pub module: String,
    /// The name of the export within that module that this import
    /// comes from.
    pub name: String,
    /// The kind of import and its specific entity index.
    pub kind: ImportKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportKind {
    /// An import of a table.
    Table(Table),
    /// An import of a function.
    Func(Func),
    /// An import of a global.
    Global(Global),
    /// An import of a memory.
    Memory(Memory),
    /// An import of a control tag
    ControlTag(ControlTag),
}

impl std::fmt::Display for ImportKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ImportKind::Table(table) => write!(f, "{}", table)?,
            ImportKind::Func(func) => write!(f, "{}", func)?,
            ImportKind::Global(global) => write!(f, "{}", global)?,
            ImportKind::Memory(mem) => write!(f, "{}", mem)?,
            ImportKind::ControlTag(control_tag) => write!(f, "{}", control_tag)?,
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Export {
    /// The name of this export.
    pub name: String,
    /// The kind of export and its specific entity index.
    pub kind: ExportKind,
}

#[derive(Clone, Debug)]
pub enum ExportKind {
    /// An export of a table.
    Table(Table),
    /// An export of a function.
    Func(Func),
    /// An export of a global.
    Global(Global),
    /// An export of a memory.
    Memory(Memory),
    /// An export of a control tag
    ControlTag(ControlTag),
}

impl std::fmt::Display for ExportKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ExportKind::Table(table) => write!(f, "{}", table)?,
            ExportKind::Func(func) => write!(f, "{}", func)?,
            ExportKind::Global(global) => write!(f, "{}", global)?,
            ExportKind::Memory(memory) => write!(f, "{}", memory)?,
            ExportKind::ControlTag(control_tag) => write!(f, "{}", control_tag)?,
        }
        Ok(())
    }
}

impl<'a> Module<'a> {
    // pub(crate) fn with_orig_bytes(orig_bytes: &'a [u8]) -> Module<'a> {
    //     Module {
    //         orig_bytes,
    //         funcs: EntityVec::default(),
    //         signatures: EntityVec::default(),
    //         globals: EntityVec::default(),
    //         tables: EntityVec::default(),
    //         imports: vec![],
    //         exports: vec![],
    //         memories: EntityVec::default(),
    //         start_func: None,
    //         debug: Debug::default(),
    //         debug_map: DebugMap::default(),
    //         custom_sections: BTreeMap::default(),
    //     }
    // }

    pub fn empty() -> Module<'static> {
        Module {
            orig_bytes: None,
            funcs: EntityVec::default(),
            signatures: EntityVec::default(),
            globals: EntityVec::default(),
            tables: EntityVec::default(),
            imports: vec![],
            exports: vec![],
            memories: EntityVec::default(),
            start_func: None,
            debug: Debug::default(),
            debug_map: DebugMap::default(),
            custom_sections: Default::default(),
            control_tags: Default::default(),
        }
    }

    /// Parse a WebAssembly module, as a slice of bytes in memory,
    /// into a waffle Module ready to be manipulated and recompile.
    pub fn from_wasm_bytes(bytes: &'a [u8], options: &FrontendOptions) -> Result<Self> {
        frontend::wasm_to_ir(bytes, options)
    }

    /// Take this module and strip its reference to the original
    /// bytes, producing a module with the same logical contents.
    ///
    /// Note that this has a few side-effects:
    /// - Any (non-debug) custom sections are lost; i.e., they will
    ///   not be roundtripped from the original Wasm module.
    /// - All function bodies are expanded to IR so they can be
    ///   recompiled into new bytecode. The bytecode should be
    ///   equivalent, but will not literally be the same bytecode as the
    ///   original module.
    pub fn without_orig_bytes(self) -> Module<'static> {
        Module {
            orig_bytes: None,
            funcs: EntityVec::from(
                self.funcs
                    .into_vec()
                    .into_iter()
                    .map(|decl| decl.without_orig_bytes())
                    .collect::<Vec<_>>(),
            ),
            signatures: self.signatures,
            globals: self.globals,
            tables: self.tables,
            imports: self.imports,
            exports: self.exports,
            memories: self.memories,
            start_func: self.start_func,
            debug: self.debug,
            debug_map: self.debug_map,
            custom_sections: self.custom_sections,
            control_tags: self.control_tags,
        }
    }
}

impl<'a> Module<'a> {
    // pub(crate) fn frontend_add_table(&mut self, ty: Type, initial: u64, max: Option<u64>) -> Table {
    //     let func_elements = Some(vec![]);
    //     self.tables.push(TableData {
    //         ty,
    //         func_elements,
    //         initial,
    //         max,
    //     })
    // }

    // pub fn from_wasm_bytes(bytes: &'a [u8], options: &FrontendOptions) -> Result<Self> {
    //     frontend::wasm_to_ir(bytes, options)
    // }

    pub fn to_wasm_bytes(&self) -> Result<Vec<u8>> {
        backend::compile(self).map(|a| a.finish())
    }
    pub fn to_encoded_module(&self) -> Result<wasm_encoder::Module> {
        backend::compile(self)
    }

    pub fn per_func_body<F: Fn(&mut FunctionBody)>(&mut self, f: F) {
        for func_decl in self.funcs.values_mut() {
            if let Some(body) = func_decl.body_mut() {
                f(body);
            }
        }
    }

    pub fn take_per_func_body<F: FnMut(&mut Self, &mut FunctionBody)>(&mut self, mut f: F) {
        for func_decl in self.funcs.iter().collect::<Vec<_>>() {
            let mut x = std::mem::take(&mut self.funcs[func_decl]);
            if let Some(body) = x.body_mut() {
                f(self, body);
            }
            self.funcs[func_decl] = x;
        }
    }

    pub fn try_per_func_body<F: FnMut(&mut FunctionBody) -> Result<(), E>, E>(
        &mut self,
        mut f: F,
    ) -> Result<(), E> {
        for func_decl in self.funcs.values_mut() {
            if let Some(body) = func_decl.body_mut() {
                f(body)?;
            }
        }
        Ok(())
    }

    pub fn try_take_per_func_body<F: FnMut(&mut Self, &mut FunctionBody) -> Result<(), E>, E>(
        &mut self,
        mut f: F,
    ) -> Result<(), E> {
        for func_decl in self.funcs.iter().collect::<Vec<_>>() {
            let mut x = std::mem::take(&mut self.funcs[func_decl]);
            let mut y = None;
            if let Some(body) = x.body_mut() {
                y = Some(f(self, body));
            }
            self.funcs[func_decl] = x;
            if let Some(z) = y {
                z?;
            }
        }
        Ok(())
    }

    /// Expand a function body, parsing its lazy reference to original
    /// bytecode into IR if needed.
    pub fn expand_func<'b>(&'b mut self, id: Func) -> Result<&'b mut FuncDecl<'a>> {
        if let FuncDecl::Lazy(..) = self.funcs[id] {
            // End the borrow. This is cheap (a slice copy).
            let mut func = self.funcs[id].clone();
            func.parse(self)?;
            self.funcs[id] = func;
        }
        Ok(&mut self.funcs[id])
    }

    /// Clone a function body *without* expanding it, and return a
    /// *new* function body with IR expanded. Useful when a tool
    /// appends new functions that are processed versions of an
    /// original function (which itself must remain as well).
    pub fn clone_and_expand_body(&self, id: Func) -> Result<FunctionBody> {
        let mut body = self.funcs[id].clone();
        body.parse(self)?;
        Ok(match body {
            FuncDecl::Body(_, _, body) => body,
            _ => unreachable!(),
        })
    }

    /// For all functions that are lazy references to initial
    /// bytecode, expand them into IR.
    pub fn expand_all_funcs(&mut self) -> Result<()> {
        for id in 0..self.funcs.len() {
            let id = Func::new(id);
            self.expand_func(id)?;
        }
        Ok(())
    }

    /// Return a wrapper that implements Display on this module,
    /// pretty-printing it as textual IR.
    pub fn display<'b>(&'b self) -> ModuleDisplay<'b>
    where
        'b: 'a,
    {
        ModuleDisplay { module: self }
    }

    /// Internal (used during parsing): create an empty module, with
    /// the given slice of original Wasm bytecode. Used during parsing
    /// and meant to be filled in as the Wasm bytecode is processed.
    pub(crate) fn with_orig_bytes(orig_bytes: &'a [u8]) -> Module<'a> {
        Module {
            orig_bytes: Some(orig_bytes),
            funcs: EntityVec::default(),
            signatures: EntityVec::default(),
            globals: EntityVec::default(),
            tables: EntityVec::default(),
            imports: vec![],
            exports: vec![],
            memories: EntityVec::default(),
            start_func: None,
            debug: Debug::default(),
            debug_map: DebugMap::default(),
            custom_sections: BTreeMap::default(),
            control_tags: EntityVec::default(),
        }
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
