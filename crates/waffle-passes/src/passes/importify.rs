use crate::{
    cfg::CFGInfo, waffle_passes_shared::value_is_pure, util::new_sig, util::results_ref_2, Block,
    BlockTarget, Export, Func, FuncDecl, FunctionBody, Import, ImportKind, Module, Operator, Type,
    Value, ValueDef,
};
use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use anyhow::Context;
use waffle_passes_shared::maxssa;
use core::{
    default,
    mem::{replace, take},
    sync::atomic::AtomicUsize,
};
fn manifest_of(
    m: &Module,
    name: &str,
    src: &FunctionBody,
    k: Block,
) -> BTreeMap<Value, (String, Vec<Type>)> {
    return src.blocks[k]
        .insts
        .iter()
        .filter_map(|a| a.pure_core())
        .filter_map(|a| {
            let ValueDef::Operator(Operator::Call { function_index }, _, types) = &src.values[a]
            else {
                return None;
            };
            let function_index = *function_index;
            for i in m.imports.iter() {
                if i.module == name {
                    if i.kind == ImportKind::Func(function_index) {
                        return Some((a, (i.name.clone(), src.type_pool[*types].to_owned())));
                    }
                }
            }
            None
        })
        .collect();
}
// #[derive(Default)]
pub struct Importify<'a> {
    blocks: BTreeMap<Block, Block>,
    pub name: String,
    manifest: BTreeMap<Value, (String, Vec<Type>)>,
    funcs: &'a mut BTreeMap<Block, Func>,
    ids: Arc<AtomicUsize>,
}
impl<'a> Importify<'a> {
    pub fn to_ids(self) -> Arc<AtomicUsize> {
        self.ids
    }
    pub fn new(ids: Arc<AtomicUsize>, name: String, funcs: &'a mut BTreeMap<Block, Func>) -> Self {
        Self {
            blocks: Default::default(),
            manifest: Default::default(),
            funcs,
            ids: ids,
            name,
        }
    }
    pub fn translate_f(
        &mut self,
        module: &mut Module,
        // dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Func> {
        match self.funcs.get(&k) {
            None => {
                // let k = *k;
                let sig = new_sig(
                    module,
                    crate::SignatureData::Func {
                        params: manifest_of(&module, &self.name, src, k)
                            .values()
                            .map(|a| &a.1)
                            .flatten()
                            .cloned()
                            .chain(src.blocks[k].params.iter().map(|a| a.0))
                            .collect(),
                        returns: src.rets.clone(),
                        shared: true,
                    },
                );
                let mut dst = FunctionBody::new(module, sig);
                dst.entry = Importify {
                    blocks: Default::default(),
                    manifest: manifest_of(&module, &self.name, src, k),
                    funcs: &mut *self.funcs,
                    ids: self.ids.clone(),
                    name: self.name.clone(),
                }
                .translate(module, &mut dst, src, k)?;
                dst.recompute_edges();
                let f = module.funcs.push(crate::FuncDecl::Body(
                    sig,
                    format!("synthetic import/export"),
                    dst,
                ));
                self.funcs.insert(k, f);
                Ok(f)
            }
            Some(a) => Ok(*a),
        }
        // .try_insert(k, |k| {
        // .map(|a| *a)
    }
    /// Allocates a destination block for `k` without processing its body.
    fn alloc_block(&mut self, dst: &mut FunctionBody, k: Block) -> Block {
        if let Some(&b) = self.blocks.get(&k) {
            return b;
        }
        let new = dst.add_block();
        self.blocks.insert(k, new);
        new
    }

    pub fn translate(
        &mut self,
        module: &mut Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        start: Block,
    ) -> anyhow::Result<Block> {
        let start_dst = self.alloc_block(dst, start);
        let mut queue: VecDeque<Block> = VecDeque::new();
        let mut processed: BTreeSet<Block> = BTreeSet::new();
        queue.push_back(start);
        while let Some(k) = queue.pop_front() {
            if !processed.insert(k) {
                continue;
            }
            self.process_block(module, dst, src, k, &mut queue)?;
        }
        Ok(start_dst)
    }

    fn process_block(
        &mut self,
        module: &mut Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        queue: &mut VecDeque<Block>,
    ) -> anyhow::Result<()> {
        let new = *self.blocks.get(&k).unwrap();
        if self.manifest.is_empty() && !manifest_of(&module, &self.name, src, k).is_empty() {
            let vals = src.blocks[k].params.iter().map(|a| a.0).collect::<Vec<_>>();
            let vtys = vals
                .iter()
                .cloned()
                .map(|a| dst.add_blockparam(new, a))
                .collect();
            let proper = self.translate_f(module, src, k)?;
            let mut chain = proper;
            let mut m2 = manifest_of(&module, &self.name, src, k);
            loop {
                let Some((_, (ky, ts))) = m2.pop_first() else {
                    break;
                };
                let siga = new_sig(
                    module,
                    crate::SignatureData::Func {
                        params: m2
                            .values()
                            .map(|a| &a.1)
                            .flatten()
                            .cloned()
                            .chain(src.blocks[k].params.iter().map(|a| a.0))
                            .collect(),
                        returns: src.rets.clone(),
                        shared: true,
                    },
                );
                let i = module
                    .funcs
                    .push(crate::FuncDecl::Import(siga, format!("{ky}/import")));
                let n = self.ids.fetch_and(1, core::sync::atomic::Ordering::SeqCst);
                let n = format!("$${n}");
                module.imports.push(Import {
                    module: ky,
                    name: n.clone(),
                    kind: ImportKind::Func(i),
                });
                let x = replace(&mut chain, i);
                module.exports.push(Export {
                    name: n,
                    kind: crate::ExportKind::Func(x),
                });
            }
            dst.set_terminator(
                k,
                crate::Terminator::ReturnCall {
                    func: chain,
                    args: vtys,
                },
            );
            return Ok(());
        }
        let mut manifest = take(&mut self.manifest)
            .into_iter()
            .map(|(a, (b, c))| {
                (
                    a,
                    (
                        b,
                        c.into_iter()
                            .map(|d| dst.add_blockparam(new, d))
                            .collect::<Vec<_>>(),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut state = src.blocks[k]
            .params
            .iter()
            .map(|(k, v)| (*v, vec![dst.add_blockparam(new, *k)]))
            .collect::<BTreeMap<_, _>>();
        'a: for i in src.blocks[k].insts.iter().cloned() {
            let Some(i) = i.pure_core() else {
                anyhow::bail!("non-core value")
            };
            if value_is_pure(i, src) {
                let mut unused = true;
                for j in src.blocks[k].insts.iter().cloned() {
                    src.values[j.value].visit_uses(&src.arg_pool, |u| {
                        if u == i {
                            unused = false;
                        }
                    });
                }
                src.blocks[k].terminator.visit_uses(|u| {
                    if u == i {
                        unused = false;
                    }
                });
                if unused {
                    continue 'a;
                }
            }
            let v = match manifest.remove(&i) {
                None => match &src.values[i] {
                    crate::ValueDef::BlockParam(block, _, _) => todo!(),
                    crate::ValueDef::Operator(operator, list_ref, list_ref1) => {
                        let args = src.arg_pool[*list_ref]
                            .iter()
                            .filter_map(|a| state.get(a))
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        let tys = &src.type_pool[*list_ref1];
                        let c = dst.add_op(new, operator.clone(), &args, tys);
                        results_ref_2(dst, c)
                    }
                    crate::ValueDef::PickOutput(value, a, b) => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        vec![value[*a as usize]]
                    }
                    crate::ValueDef::Alias(value) => state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?,
                    crate::ValueDef::Placeholder(_) => todo!(),
                    crate::ValueDef::None => vec![],
                },
                Some((_, vs)) => vs,
            };
            state.insert(i, v);
        }
        // Allocate successor block (if needed), enqueue, and remap args.
        let mut ensure_target =
            |this: &mut Self,
             dst: &mut FunctionBody,
             target: &BlockTarget|
             -> anyhow::Result<BlockTarget> {
                let block = this.alloc_block(dst, target.block);
                queue.push_back(target.block);
                let args = target
                    .args
                    .iter()
                    .filter_map(|b| state.get(b))
                    .flatten()
                    .cloned()
                    .collect();
                anyhow::Ok(BlockTarget { args, block })
            };
        let t = match &src.blocks[k].terminator {
            crate::Terminator::Br { target } => crate::Terminator::Br {
                target: ensure_target(self, dst, target)?,
            },
            crate::Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => {
                let if_true = ensure_target(self, dst, if_true)?;
                let if_false = ensure_target(self, dst, if_false)?;
                let cond = state
                    .get(cond)
                    .cloned()
                    .context("in getting the referenced value")?;
                crate::Terminator::CondBr {
                    cond: cond[0],
                    if_true,
                    if_false,
                }
            }
            crate::Terminator::Select {
                value,
                targets,
                default,
            } => {
                let value = state
                    .get(value)
                    .cloned()
                    .context("in getting the referenced value")?;
                let default = ensure_target(self, dst, default)?;
                let targets = targets
                    .iter()
                    .map(|t| ensure_target(self, dst, t))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                crate::Terminator::Select {
                    value: value[0],
                    targets,
                    default,
                }
            }
            crate::Terminator::Return { values } => crate::Terminator::Return {
                values: values
                    .iter()
                    .filter_map(|b| state.get(b))
                    .flatten()
                    .cloned()
                    .collect(),
            },
            crate::Terminator::ReturnCall { func, args } => crate::Terminator::ReturnCall {
                func: *func,
                args: args
                    .iter()
                    .filter_map(|b| state.get(b))
                    .flatten()
                    .cloned()
                    .collect(),
            },
            crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                crate::Terminator::ReturnCallIndirect {
                    sig: *sig,
                    table: *table,
                    args: args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                }
            }
            crate::Terminator::ReturnCallRef { sig, args } => {
                crate::Terminator::ReturnCallRef {
                    sig: *sig,
                    args: args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                }
            }
            crate::Terminator::Unreachable => crate::Terminator::Unreachable,
            _ => crate::Terminator::None,
        };
        dst.set_terminator(new, t);
        Ok(())
    }
}
pub fn importify_mod(m: &mut Module, ids: Arc<AtomicUsize>, name: String) -> anyhow::Result<()> {
    for f in m.funcs.iter().collect::<BTreeSet<_>>() {
        let mut g = take(&mut m.funcs[f]);
        if let FuncDecl::Body(s, _, b) = &mut g {
            let cfg = CFGInfo::new(b);
            maxssa::run(b, None, &cfg);
            let s = *s;
            let mut new = FunctionBody::new(&m, s);
            new.entry = match (Importify::new(ids.clone(), name.clone(), &mut BTreeMap::new()))
                .translate(
                    m, &mut new, &*b,
                    b.entry,
                    // b.blocks[b.entry].params.iter().map(|_| None).collect(),
                ) {
                Ok(a) => a,
                Err(e) => {
                    m.funcs[f] = g;
                    return Err(e);
                }
            };
            new.recompute_edges();
            *b = new;
        }
        m.funcs[f] = g;
    }
    Ok(())
}
