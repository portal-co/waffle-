use super::{Block, FunctionBodyDisplay, Local, Module, Signature, Type, Value, ValueDef};
use crate::backend::WasmFuncBackend;
use crate::cfg::CFGInfo;
use crate::entity::{EntityRef, EntityVec, PerEntity};
use crate::frontend::parse_body;
use crate::ir::SourceLoc;
use crate::passes::basic_opt::OptOptions;
use crate::pool::{ListPool, ListRef};
use crate::{Func, Operator, Table};
use anyhow::Result;
use either::Either;
use fxhash::FxHashMap;
use ssa_traits::{Term, Val};
use std::collections::HashSet;
use std::iter::{empty, once};

/// A declaration of a function: there is one `FuncDecl` per `Func`
/// index.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub enum FuncDecl<'a> {
    /// An imported function.
    Import(Signature, String),
    /// An un-expanded body that can be lazily expanded if needed.
    #[serde(skip)]
    Lazy(Signature, String, wasmparser::FunctionBody<'a>),
    /// A modified or new function body that requires compilation.
    Body(Signature, String, FunctionBody),
    /// A compiled function body (was IR, has been collapsed back to bytecode).
    Compiled(Signature, String, Vec<u8>),
    /// A placeholder.
    #[default]
    None,
}

impl<'a> FuncDecl<'a> {
    pub fn sig(&self) -> Signature {
        match self {
            FuncDecl::Import(sig, ..) => *sig,
            FuncDecl::Lazy(sig, ..) => *sig,
            FuncDecl::Body(sig, ..) => *sig,
            FuncDecl::Compiled(sig, ..) => *sig,
            FuncDecl::None => panic!("No signature for FuncDecl::None"),
        }
    }

    pub fn parse(&mut self, module: &Module) -> Result<()> {
        match self {
            FuncDecl::Lazy(sig, name, body) => {
                let body = parse_body(module, *sig, body)?;
                *self = FuncDecl::Body(*sig, name.clone(), body);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    pub fn optimize(&mut self, opts: &OptOptions) {
        match self {
            FuncDecl::Body(_, _, body) => {
                body.optimize(opts);
            }
            _ => {}
        }
    }

    pub fn convert_to_max_ssa(&mut self, cut_blocks: Option<HashSet<Block>>) {
        match self {
            FuncDecl::Body(_, _, body) => {
                body.convert_to_max_ssa(cut_blocks);
            }
            _ => {}
        }
    }

    pub fn body(&self) -> Option<&FunctionBody> {
        match self {
            FuncDecl::Body(_, _, body) => Some(body),
            _ => None,
        }
    }

    pub fn body_mut(&mut self) -> Option<&mut FunctionBody> {
        match self {
            FuncDecl::Body(_, _, body) => Some(body),
            _ => None,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            FuncDecl::Body(_, name, _)
            | FuncDecl::Lazy(_, name, _)
            | FuncDecl::Import(_, name)
            | FuncDecl::Compiled(_, name, _) => &name[..],
            FuncDecl::None => panic!("No name for FuncDecl::None"),
        }
    }

    pub fn set_name(&mut self, new_name: &str) {
        match self {
            FuncDecl::Body(_, name, _)
            | FuncDecl::Lazy(_, name, _)
            | FuncDecl::Import(_, name)
            | FuncDecl::Compiled(_, name, _) => *name = new_name.to_owned(),
            FuncDecl::None => panic!("No name for FuncDecl::None"),
        }
    }

    pub fn without_orig_bytes(self) -> FuncDecl<'static> {
        match self {
            FuncDecl::Body(sig, name, body) => FuncDecl::Body(sig, name, body),
            FuncDecl::Import(sig, name) => FuncDecl::Import(sig, name),
            FuncDecl::Compiled(sig, name, func) => FuncDecl::Compiled(sig, name, func),
            FuncDecl::None => FuncDecl::None,
            FuncDecl::Lazy(..) => panic!("Trying to strip lifetime from lazy decl"),
        }
    }
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct FunctionBody {
    /// How many parameters the function has. (Their types are the
    /// first `n_params` values in `locals`.)
    pub n_params: usize,
    /// Return types of the function.
    pub rets: Vec<Type>,
    /// Local types, *including* args.
    pub locals: EntityVec<Local, Type>,
    /// Entry block.
    pub entry: Block,
    /// Block bodies.
    pub blocks: EntityVec<Block, BlockDef>,
    /// Value definitions, indexed by `Value`.
    pub values: EntityVec<Value, ValueDef>,
    /// Pool of types for ValueDefs' result type lists.
    pub type_pool: ListPool<Type>,
    /// Deduplication for type-lists of single types.
    pub single_type_dedup: FxHashMap<Type, ListRef<Type>>,
    /// Pool of values for ValueDefs' arg lists.
    pub arg_pool: ListPool<Value>,
    /// Blocks in which values are computed. Each may be `Block::invalid()` if not placed.
    pub value_blocks: PerEntity<Value, Block>,
    /// Wasm locals that values correspond to, if any.
    pub value_locals: PerEntity<Value, Option<Local>>,
    /// Debug source locations of each value.
    pub source_locs: PerEntity<Value, SourceLoc>,
}

impl FunctionBody {
    pub fn new(module: &Module, sig: Signature) -> FunctionBody {
        let locals = EntityVec::from(module.signatures[sig].params.clone());
        let n_params = locals.len();
        let rets = module.signatures[sig].returns.clone();
        let mut blocks = EntityVec::default();
        let entry = blocks.push(BlockDef::default());
        let mut values = EntityVec::default();
        let mut value_blocks = PerEntity::default();
        for (i, &arg_ty) in locals.values().enumerate() {
            let value = values.push(ValueDef::BlockParam(entry, i as u32, arg_ty));
            blocks[entry].params.push((arg_ty, value));
            value_blocks[value] = entry;
        }
        FunctionBody {
            n_params,
            rets,
            locals,
            entry,
            blocks,
            values,
            type_pool: ListPool::default(),
            arg_pool: ListPool::default(),
            single_type_dedup: FxHashMap::default(),
            value_blocks,
            value_locals: PerEntity::default(),
            source_locs: PerEntity::default(),
        }
    }

    pub fn optimize(&mut self, opts: &OptOptions) {
        let cfg = crate::cfg::CFGInfo::new(self);
        crate::passes::basic_opt::basic_opt(self, &cfg, opts);
        crate::passes::empty_blocks::run(self);
    }

    pub fn convert_to_max_ssa(&mut self, cut_blocks: Option<HashSet<Block>>) {
        let cfg = crate::cfg::CFGInfo::new(self);
        crate::passes::maxssa::run(self, cut_blocks, &cfg);
    }

    pub fn add_block(&mut self) -> Block {
        let id = self.blocks.push(BlockDef::default());
        log::trace!("add_block: block {}", id);
        id
    }

    pub fn single_type_list(&mut self, ty: Type) -> ListRef<Type> {
        let type_pool = &mut self.type_pool;
        *self
            .single_type_dedup
            .entry(ty)
            .or_insert_with(|| type_pool.single(ty))
    }

    pub fn add_edge(&mut self, from: Block, to: Block) {
        let succ_pos = self.blocks[from].succs.len();
        let pred_pos = self.blocks[to].preds.len();
        self.blocks[from].succs.push(to);
        self.blocks[to].preds.push(from);
        self.blocks[from].pos_in_succ_pred.push(pred_pos);
        self.blocks[to].pos_in_pred_succ.push(succ_pos);
        log::trace!("add_edge: from {} to {}", from, to);
    }

    pub fn split_edge(&mut self, from: Block, to: Block, succ_idx: usize) -> Block {
        assert_eq!(self.blocks[from].succs[succ_idx], to);
        let pred_idx = self.blocks[from].pos_in_succ_pred[succ_idx];
        assert_eq!(self.blocks[to].preds[pred_idx], from);

        // Create the block itself.
        let edge_block = self.add_block();

        // Add blockparams.
        let mut blockparams = vec![];
        for i in 0..self.blocks[to].params.len() {
            let ty = self.blocks[to].params[i].0;
            blockparams.push(self.add_blockparam(edge_block, ty));
        }

        // Create an unconditional-branch terminator in the edge block.
        self.blocks[edge_block].terminator = Terminator::Br {
            target: BlockTarget {
                block: to,
                args: blockparams,
            },
        };

        // Update target of from-block.
        self.blocks[from]
            .terminator
            .update_target(succ_idx, |target| target.block = edge_block);

        // Fill in succ/pred links on edge block.
        self.blocks[edge_block].succs.push(to);
        self.blocks[edge_block].pos_in_succ_pred.push(pred_idx);
        self.blocks[edge_block].preds.push(from);
        self.blocks[edge_block].pos_in_pred_succ.push(succ_idx);

        // Update `succs` in `from`, `preds` in `to`.
        self.blocks[from].succs[succ_idx] = edge_block;
        self.blocks[from].pos_in_succ_pred[succ_idx] = 0;
        self.blocks[to].preds[pred_idx] = edge_block;
        self.blocks[to].pos_in_pred_succ[pred_idx] = 0;

        edge_block
    }

    pub fn recompute_edges(&mut self) {
        for block in self.blocks.values_mut() {
            block.preds.clear();
            block.succs.clear();
            block.pos_in_succ_pred.clear();
            block.pos_in_pred_succ.clear();
        }

        for block in 0..self.blocks.len() {
            let block = Block::new(block);
            let terminator = self.blocks[block].terminator.clone();
            terminator.visit_successors(|succ| {
                self.add_edge(block, succ);
            });
        }
    }

    pub fn add_value(&mut self, value: ValueDef) -> Value {
        log::trace!("add_value: def {:?}", value);
        let value = self.values.push(value);
        log::trace!(" -> {}", value);
        value
    }

    pub fn set_alias(&mut self, value: Value, to: Value) {
        log::trace!("set_alias: value {:?} to {:?}", value, to);
        // Resolve the `to` value through all existing aliases.
        let to = self.resolve_and_update_alias(to);
        // Disallow cycles.
        if to == value {
            panic!("Cannot create an alias cycle");
        }
        self.values[value] = ValueDef::Alias(to);
    }

    pub fn resolve_alias(&self, value: Value) -> Value {
        if value.is_invalid() {
            return value;
        }

        let mut result = value;
        loop {
            if let &ValueDef::Alias(to) = &self.values[result] {
                result = to;
            } else {
                break;
            }
        }
        result
    }

    pub fn add_blockparam(&mut self, block: Block, ty: Type) -> Value {
        let index = self.blocks[block].params.len();
        let value = self.add_value(ValueDef::BlockParam(block, index as u32, ty));
        self.blocks[block].params.push((ty, value));
        self.value_blocks[value] = block;
        value
    }

    pub fn add_placeholder(&mut self, ty: Type) -> Value {
        self.add_value(ValueDef::Placeholder(ty))
    }

    pub fn replace_placeholder_with_blockparam(&mut self, block: Block, value: Value) {
        let index = self.blocks[block].params.len();
        let ty = match &self.values[value] {
            &ValueDef::Placeholder(ty) => ty,
            _ => unreachable!(),
        };
        self.blocks[block].params.push((ty, value));
        self.values[value] = ValueDef::BlockParam(block, index as u32, ty);
    }

    pub fn mark_value_as_local(&mut self, value: Value, local: Local) {
        self.value_locals[value] = Some(local);
    }

    pub fn resolve_and_update_alias(&mut self, value: Value) -> Value {
        let to = self.resolve_alias(value);
        // Short-circuit the chain, union-find-style.
        if let &ValueDef::Alias(orig_to) = &self.values[value] {
            if orig_to != to {
                self.values[value] = ValueDef::Alias(to);
            }
        }
        to
    }

    pub fn append_to_block(&mut self, block: Block, value: Value) {
        self.blocks[block].insts.push(value);
        self.value_blocks[value] = block;
    }

    pub fn set_terminator(&mut self, block: Block, terminator: Terminator) {
        debug_assert_eq!(&self.blocks[block].terminator, &Terminator::None);
        log::trace!("block {} terminator {:?}", block, terminator);
        terminator.visit_successors(|succ| {
            self.add_edge(block, succ);
        });
        self.blocks[block].terminator = terminator;
    }

    pub fn add_local(&mut self, ty: Type) -> Local {
        self.locals.push(ty)
    }

    pub fn display<'a>(
        &'a self,
        indent: &'a str,
        module: Option<&'a Module>,
    ) -> FunctionBodyDisplay<'a> {
        FunctionBodyDisplay {
            body: self,
            indent,
            verbose: false,
            module,
        }
    }

    pub fn display_verbose<'a>(
        &'a self,
        indent: &'a str,
        module: Option<&'a Module>,
    ) -> FunctionBodyDisplay<'a> {
        FunctionBodyDisplay {
            body: self,
            indent,
            verbose: true,
            module,
        }
    }

    pub fn validate(&self) -> anyhow::Result<()> {
        // Verify that every block's succs are accurate.
        for (block, block_def) in self.blocks.entries() {
            let mut actual_succs = vec![];
            block_def
                .terminator
                .visit_successors(|succ| actual_succs.push(succ));
            if &actual_succs[..] != &block_def.succs[..] {
                anyhow::bail!(
                    "Incorrect successors on {}: actual {:?}, stored {:?}",
                    block,
                    actual_succs,
                    block_def.succs
                );
            }
        }

        // Compute the location where every value is defined.
        let mut block_inst: PerEntity<Value, Option<(Block, Option<usize>)>> = PerEntity::default();
        for (block, block_def) in self.blocks.entries() {
            for &(_, param) in &block_def.params {
                block_inst[param] = Some((block, None));
            }
            for (i, &inst) in block_def.insts.iter().enumerate() {
                block_inst[inst] = Some((block, Some(i)));
            }
        }

        // Verify that every instruction uses args at legal locations
        // (same block but earlier, or a dominating block).
        let cfg = CFGInfo::new(self);
        let mut bad = vec![];
        for (block, block_def) in self.blocks.entries() {
            // If block isn't reachable, skip it.
            if cfg.rpo_pos[block].is_none() {
                continue;
            }
            let mut visit_use = |u: Value, i: Option<usize>, inst: Option<Value>| {
                let u = self.resolve_alias(u);
                if block_inst[u].is_none() {
                    bad.push(format!(
                        "Use of arg {} at {:?} in {} illegal: not defined",
                        u, inst, block
                    ));
                    return;
                }
                let (def_block, def_idx) = block_inst[u].unwrap();
                if def_block == block {
                    if def_idx >= i {
                        bad.push(format!(
                            "Use of arg {} by {:?} does not dominate location",
                            u, inst
                        ));
                    }
                } else {
                    if !cfg.dominates(def_block, block) {
                        bad.push(format!(
                            "Use of arg {} defined in {} by {:?} in {}: def does not dominate",
                            u, def_block, inst, block
                        ));
                    }
                }
            };

            for (i, &inst) in block_def.insts.iter().enumerate() {
                match &self.values[inst] {
                    &ValueDef::Operator(_, args, _) => {
                        for &arg in &self.arg_pool[args] {
                            visit_use(arg, Some(i), Some(inst));
                        }
                    }
                    &ValueDef::PickOutput(val, _, _) => {
                        visit_use(val, Some(i), Some(inst));
                    }
                    _ => {}
                }
            }
            let terminator_idx = block_def.insts.len();
            block_def.terminator.visit_uses(|u| {
                visit_use(u, Some(terminator_idx), None);
            });
        }
        if bad.len() > 0 {
            anyhow::bail!(
                "Body is:\n{}\nError(s) in SSA: {:?}",
                self.display_verbose(" | ", None),
                bad
            );
        }

        Ok(())
    }

    pub fn verify_reducible(&self) -> Result<()> {
        let cfg = CFGInfo::new(self);
        for (rpo, &block) in cfg.rpo.entries() {
            for &succ in &self.blocks[block].succs {
                let succ_rpo = cfg.rpo_pos[succ].unwrap();
                if succ_rpo.index() <= rpo.index() && !cfg.dominates(succ, block) {
                    anyhow::bail!(
                        "Irreducible edge from {} ({}) to {} ({})",
                        block,
                        rpo,
                        succ,
                        succ_rpo
                    );
                }
            }
        }
        Ok(())
    }

    pub fn compile(&self) -> Result<wasm_encoder::Function> {
        let backend = WasmFuncBackend::new(self)?;
        backend.compile()
    }
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct BlockDef {
    /// Instructions in this block.
    pub insts: Vec<Value>,
    /// Terminator: branch or return.
    pub terminator: Terminator,
    /// Successor blocks.
    pub succs: Vec<Block>,
    /// For each successor block, our index in its `preds` array.
    pub pos_in_succ_pred: Vec<usize>,
    /// Predecessor blocks.
    pub preds: Vec<Block>,
    /// For each predecessor block, our index in its `succs` array.
    pub pos_in_pred_succ: Vec<usize>,
    /// Type and Value for each blockparam.
    pub params: Vec<(Type, Value)>,
    /// Descriptive name for the block, if any.
    pub desc: String,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BlockTarget {
    pub block: Block,
    pub args: Vec<Value>,
}

impl std::fmt::Display for BlockTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let args = self
            .args
            .iter()
            .map(|arg| format!("{}", arg))
            .collect::<Vec<_>>();
        write!(f, "{}({})", self.block, args.join(", "))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Terminator {
    Br {
        target: BlockTarget,
    },
    CondBr {
        cond: Value,
        if_true: BlockTarget,
        if_false: BlockTarget,
    },
    Select {
        value: Value,
        targets: Vec<BlockTarget>,
        default: BlockTarget,
    },
    Return {
        values: Vec<Value>,
    },
    ReturnCall {
        func: Func,
        args: Vec<Value>,
    },
    ReturnCallIndirect {
        sig: Signature,
        table: Table,
        args: Vec<Value>,
    },
    ReturnCallRef {
        sig: Signature,
        args: Vec<Value>,
    },
    Unreachable,
    None,
}

impl std::default::Default for Terminator {
    fn default() -> Self {
        Terminator::None
    }
}

impl std::fmt::Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Terminator::None => write!(f, "no_terminator")?,
            Terminator::Br { target } => write!(f, "br {}", target)?,
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => write!(f, "if {}, {}, {}", cond, if_true, if_false)?,
            Terminator::Select {
                value,
                targets,
                default,
            } => write!(
                f,
                "select {}, [{}], {}",
                value,
                targets
                    .iter()
                    .map(|target| format!("{}", target))
                    .collect::<Vec<_>>()
                    .join(", "),
                default
            )?,
            Terminator::Return { values } => write!(
                f,
                "return {}",
                values
                    .iter()
                    .map(|val| format!("{}", val))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?,
            Terminator::Unreachable => write!(f, "unreachable")?,
            Terminator::ReturnCall { func, args } => write!(
                f,
                "return_call {}({})",
                func,
                args.iter()
                    .map(|val| format!("{}", val))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?,
            Terminator::ReturnCallIndirect { sig, table, args } => write!(
                f,
                "return_call_indirect ({};{})({})",
                sig,
                table,
                args.iter()
                    .map(|val| format!("{}", val))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?,
            Terminator::ReturnCallRef { sig, args } => write!(
                f,
                "return_call_ref ({})({})",
                sig,
                // table,
                args.iter()
                    .map(|val| format!("{}", val))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?,
        }
        Ok(())
    }
}

impl Terminator {
    pub fn visit_targets<F: FnMut(&BlockTarget)>(&self, mut f: F) {
        match self {
            Terminator::Return { .. } => {}
            Terminator::Br { ref target, .. } => f(target),
            Terminator::CondBr {
                ref if_true,
                ref if_false,
                ..
            } => {
                f(if_true);
                f(if_false);
            }
            Terminator::Select {
                ref targets,
                ref default,
                ..
            } => {
                f(default);
                for target in targets {
                    f(target);
                }
            }
            Terminator::None => {}
            Terminator::Unreachable => {}
            Terminator::ReturnCall { func, args } => {}
            Terminator::ReturnCallIndirect { sig, table, args } => {}
            Terminator::ReturnCallRef { sig, args } => {}
        }
    }

    pub fn update_targets<F: FnMut(&mut BlockTarget)>(&mut self, mut f: F) {
        match self {
            Terminator::Return { .. } => {}
            Terminator::Br { ref mut target, .. } => f(target),
            Terminator::CondBr {
                ref mut if_true,
                ref mut if_false,
                ..
            } => {
                f(if_true);
                f(if_false);
            }
            Terminator::Select {
                ref mut targets,
                ref mut default,
                ..
            } => {
                f(default);
                for target in targets {
                    f(target);
                }
            }
            Terminator::None => {}
            Terminator::Unreachable => {}
            Terminator::ReturnCall { func, args } => {}
            Terminator::ReturnCallIndirect { sig, table, args } => {}
            Terminator::ReturnCallRef { sig, args } => {}
        }
    }

    pub fn visit_target<R, F: FnMut(&BlockTarget) -> R>(&self, index: usize, mut f: F) -> R {
        match (index, self) {
            (0, Terminator::Br { ref target, .. }) => f(target),
            (0, Terminator::CondBr { ref if_true, .. }) => f(if_true),
            (1, Terminator::CondBr { ref if_false, .. }) => f(if_false),
            (0, Terminator::Select { ref default, .. }) => f(default),
            (i, Terminator::Select { ref targets, .. }) if i <= targets.len() => f(&targets[i - 1]),
            _ => panic!("out of bounds"),
        }
    }

    pub fn update_target<F: FnMut(&mut BlockTarget)>(&mut self, index: usize, mut f: F) {
        match (index, self) {
            (0, Terminator::Br { ref mut target, .. }) => f(target),
            (
                0,
                Terminator::CondBr {
                    ref mut if_true, ..
                },
            ) => {
                f(if_true);
            }
            (
                1,
                Terminator::CondBr {
                    ref mut if_false, ..
                },
            ) => {
                f(if_false);
            }
            (
                0,
                Terminator::Select {
                    ref mut default, ..
                },
            ) => {
                f(default);
            }
            (
                i,
                Terminator::Select {
                    ref mut targets, ..
                },
            ) if i <= targets.len() => {
                f(&mut targets[i - 1]);
            }
            (i, this) => panic!("out of bounds: index {} term {:?}", i, this),
        }
    }

    pub fn visit_successors<F: FnMut(Block)>(&self, mut f: F) {
        self.visit_targets(|target| f(target.block));
    }

    pub fn visit_uses<F: FnMut(Value)>(&self, mut f: F) {
        self.visit_targets(|target| {
            for &arg in &target.args {
                f(arg);
            }
        });
        match self {
            &Terminator::CondBr { cond, .. } => f(cond),
            &Terminator::Select { value, .. } => f(value),
            &Terminator::Return { ref values, .. } => {
                for &value in values {
                    f(value);
                }
            }
            &Terminator::ReturnCall { func, ref args } => {
                for value in args {
                    f(*value);
                }
            }
            &Terminator::ReturnCallIndirect {
                sig,
                table,
                ref args,
            } => {
                for value in args {
                    f(*value);
                }
            }
            _ => {}
        }
    }

    pub fn update_uses<F: FnMut(&mut Value)>(&mut self, mut f: F) {
        self.update_targets(|target| {
            for arg in &mut target.args {
                f(arg);
            }
        });
        match self {
            &mut Terminator::CondBr { ref mut cond, .. } => f(cond),
            &mut Terminator::Select { ref mut value, .. } => f(value),
            &mut Terminator::Return { ref mut values, .. } => {
                for value in values {
                    f(value);
                }
            }
            &mut Terminator::ReturnCall { func, ref mut args } => {
                for value in args {
                    f(value);
                }
            }
            &mut Terminator::ReturnCallIndirect {
                sig,
                table,
                ref mut args,
            } => {
                for value in args {
                    f(value);
                }
            }
            &mut Terminator::ReturnCallRef { sig, ref mut args } => {
                for value in args {
                    f(value);
                }
            }
            _ => {}
        }
    }
}

impl ssa_traits::Func for FunctionBody {
    type Value = Value;

    type Block = Block;

    type Values = EntityVec<Value, ValueDef>;

    type Blocks = EntityVec<Block, BlockDef>;

    fn values(&self) -> &Self::Values {
        &self.values
    }

    fn blocks(&self) -> &Self::Blocks {
        &self.blocks
    }

    fn values_mut(&mut self) -> &mut Self::Values {
        &mut self.values
    }

    fn blocks_mut(&mut self) -> &mut Self::Blocks {
        &mut self.blocks
    }

    fn entry(&self) -> Self::Block {
        self.entry
    }
}
impl ssa_traits::HasValues<FunctionBody> for ListRef<Value> {
    fn values(
        &self,
        f: &FunctionBody,
    ) -> impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> {
        f.arg_pool[*self].iter().cloned()
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> impl Iterator<Item = &'a mut <FunctionBody as ssa_traits::Func>::Value>
    where
        FunctionBody: 'a,
    {
        g.arg_pool[*self].iter_mut()
    }
}
impl ssa_traits::Value<FunctionBody> for ValueDef {}
impl ssa_traits::HasValues<FunctionBody> for ValueDef {
    fn values(
        &self,
        f: &FunctionBody,
    ) -> impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> {
        match self {
            ValueDef::BlockParam(_, _, _) => Either::Left(None.into_iter()),
            ValueDef::Operator(_, l, _) => Either::Right(f.arg_pool[*l].iter().cloned()),
            ValueDef::PickOutput(a, _, _) => Either::Left(Some(*a).into_iter()),
            ValueDef::Alias(w) => Either::Left(Some(*w).into_iter()),
            ValueDef::Placeholder(_) => todo!(),
            // ValueDef::Trace(_, _) => todo!(),
            ValueDef::None => Either::Left(None.into_iter()),
        }
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> impl Iterator<Item = &'a mut <FunctionBody as ssa_traits::Func>::Value>
    where
        FunctionBody: 'a,
    {
        match self {
            ValueDef::BlockParam(_, _, _) => Either::Left(None.into_iter()),
            ValueDef::Operator(_, l, _) => Either::Right(g.arg_pool[*l].iter_mut()),
            ValueDef::PickOutput(a, _, _) => Either::Left(Some(a).into_iter()),
            ValueDef::Alias(w) => Either::Left(Some(w).into_iter()),
            ValueDef::Placeholder(_) => todo!(),
            // ValueDef::Trace(_, _) => todo!(),
            ValueDef::None => Either::Left(None.into_iter()),
        }
    }
}
impl ssa_traits::op::OpValue<FunctionBody, Operator> for ValueDef {
    type Residue = ValueDef;

    type Capture = ListRef<Value>;
    type Spit = Vec<Type>;

    fn disasm(
        self,
        f: &mut FunctionBody,
    ) -> std::result::Result<(Operator, Self::Capture, Self::Spit), Self::Residue> {
        match self {
            ValueDef::Operator(a, b, c) => Ok((a, b, f.type_pool[c].to_owned())),
            s => Err(s),
        }
    }

    fn of(f: &mut FunctionBody, o: Operator, c: Self::Capture, s: Self::Spit) -> Option<Self> {
        Some(Self::Operator(o, c, f.type_pool.from_iter(s.into_iter())))
    }

    fn lift(f: &mut FunctionBody, r: Self::Residue) -> Option<Self> {
        Some(r)
    }
}
impl ssa_traits::op::OpValue<FunctionBody,u32> for ValueDef{
    type Residue = ValueDef;

    type Capture = Val<FunctionBody>;

    type Spit = Type;

    fn disasm(self, f: &mut FunctionBody) -> std::result::Result<(u32, Self::Capture, Self::Spit), Self::Residue> {
        match self{
            ValueDef::PickOutput(a,b,c) => Ok((b,Val(a),c)),
            s => Err(s)
        }
    }

    fn of(f: &mut FunctionBody, o: u32, c: Self::Capture, s: Self::Spit) -> Option<Self> {
        Some(Self::PickOutput(c.0,o,s))
    }

    fn lift(f: &mut FunctionBody, r: Self::Residue) -> Option<Self> {
        Some(r)
    }
}
impl ssa_traits::Block<FunctionBody> for BlockDef {
    fn insts(&self) -> impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> {
        self.insts.iter().cloned()
    }

    type Terminator = Terminator;

    fn term(&self) -> &Self::Terminator {
        &self.terminator
    }

    fn term_mut(&mut self) -> &mut Self::Terminator {
        &mut self.terminator
    }

    fn add_inst(
        func: &mut FunctionBody,
        key: <FunctionBody as ssa_traits::Func>::Block,
        v: <FunctionBody as ssa_traits::Func>::Value,
    ) {
        func.append_to_block(key, v)
    }
}

impl ssa_traits::Target<FunctionBody> for BlockTarget {
    fn block(&self) -> <FunctionBody as ssa_traits::Func>::Block {
        self.block
    }

    fn block_mut(&mut self) -> &mut <FunctionBody as ssa_traits::Func>::Block {
        &mut self.block
    }

    fn push_value(&mut self, v: <FunctionBody as ssa_traits::Func>::Value) {
        self.args.push(v)
    }

    fn from_values_and_block(
        a: impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value>,
        k: <FunctionBody as ssa_traits::Func>::Block,
    ) -> Self {
        BlockTarget {
            block: k,
            args: a.collect(),
        }
    }
}
impl ssa_traits::Term<FunctionBody> for BlockTarget {
    type Target = BlockTarget;

    fn targets<'a>(&'a self) -> impl Iterator<Item = &'a Self::Target>
    where
        FunctionBody: 'a,
    {
        std::iter::once(self)
    }

    fn targets_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Target>
    where
        FunctionBody: 'a,
    {
        std::iter::once(self)
    }
}
impl ssa_traits::HasValues<FunctionBody> for BlockTarget {
    fn values(
        &self,
        f: &FunctionBody,
    ) -> impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> {
        self.args.iter().cloned()
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> impl Iterator<Item = &'a mut <FunctionBody as ssa_traits::Func>::Value>
    where
        FunctionBody: 'a,
    {
        self.args.iter_mut()
    }
}
impl ssa_traits::Term<FunctionBody> for Terminator {
    type Target = BlockTarget;

    fn targets<'a>(&'a self) -> impl Iterator<Item = &'a Self::Target>
    where
        FunctionBody: 'a,
    {
        match self {
            Terminator::Br { target } => Either::Left(Some(target).into_iter()),
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Left(once(if_true).chain(once(if_false)))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(targets.iter().chain(once(default)))),
            Terminator::Return { values } => Either::Left(None.into_iter()),
            Terminator::ReturnCall { func, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallIndirect { sig, table, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallRef { sig, args } => Either::Left(None.into_iter()),
            Terminator::Unreachable => Either::Left(None.into_iter()),
            Terminator::None => Either::Left(None.into_iter()),
        }
    }

    fn targets_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Target>
    where
        FunctionBody: 'a,
    {
        match self {
            Terminator::Br { target } => Either::Left(Some(target).into_iter()),
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Left(once(if_true).chain(once(if_false)))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(targets.iter_mut().chain(once(default)))),
            Terminator::Return { values } => Either::Left(None.into_iter()),
            Terminator::ReturnCall { func, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallIndirect { sig, table, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallRef { sig, args } => Either::Left(None.into_iter()),
            Terminator::Unreachable => Either::Left(None.into_iter()),
            Terminator::None => Either::Left(None.into_iter()),
        }
    }
}
impl ssa_traits::HasValues<FunctionBody> for Terminator {
    fn values(
        &self,
        f: &FunctionBody,
    ) -> impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> {
        match self {
            Terminator::Br { target } => {
                Either::Right(Either::Right(Either::Left(target.values(f))))
            }
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Right(Either::Right(Either::Left(
                once(*cond).chain(if_true.values(f).chain(if_false.values(f))),
            )))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(Either::Right(Either::Right(
                once(*value).chain(
                    default
                        .values(f)
                        .chain(targets.iter().flat_map(move |x| x.values(f))),
                ),
            )))),
            Terminator::Return { values } => Either::Right(Either::Left(values.iter().cloned())),
            Terminator::ReturnCall { func, args } => {
                Either::Right(Either::Left(args.iter().cloned()))
            }
            Terminator::ReturnCallIndirect { sig, table, args } => {
                Either::Right(Either::Left(args.iter().cloned()))
            }
            Terminator::ReturnCallRef { sig, args } => {
                Either::Right(Either::Left(args.iter().cloned()))
            }
            Terminator::Unreachable => Either::Left(empty()),
            Terminator::None => Either::Left(empty()),
        }
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> impl Iterator<Item = &'a mut <FunctionBody as ssa_traits::Func>::Value>
    where
        FunctionBody: 'a,
    {
        match self {
            Terminator::Br { target } => {
                Either::Right(Either::Right(Either::Left(target.values_mut(g))))
            }
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Right(Either::Right(Either::Left(
                once(cond).chain(if_true.args.iter_mut().chain(if_false.values_mut(g))),
            )))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(Either::Right(Either::Right(
                once(value).chain(
                    default
                        .values_mut(g)
                        .chain(targets.iter_mut().flat_map(|x| x.args.iter_mut())),
                ),
            )))),
            Terminator::Return { values } => Either::Right(Either::Left(values.iter_mut())),
            Terminator::ReturnCall { func, args } => Either::Right(Either::Left(args.iter_mut())),
            Terminator::ReturnCallIndirect { sig, table, args } => {
                Either::Right(Either::Left(args.iter_mut()))
            }
            Terminator::ReturnCallRef { sig, args } => Either::Right(Either::Left(args.iter_mut())),
            Terminator::Unreachable => Either::Left(empty()),
            Terminator::None => Either::Left(empty()),
        }
    }
}
