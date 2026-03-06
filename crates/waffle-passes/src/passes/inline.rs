use alloc::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
    vec,
    vec::Vec,
};
use anyhow::Context;
use core::{default, mem::take, usize};
// use arena_traits::IndexAlloc;
use crate::{
    CFGInfo, const_eval, EntityRef, waffle_passes_shared::value_is_pure, util::new_sig,
    util::results_ref_2, Block, BlockTarget, ConstVal, Func, FuncCollector, FuncDecl, FunctionBody,
    ImportKind, Module, Operator, SignatureData, Terminator, Type, Value, ValueDef,
};
// use crate::FuncCollector;
#[derive(Clone)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
pub struct InlineCfg {
    pub funcs: BTreeSet<Func>,
}
impl FuncCollector for InlineCfg {
    fn collect_func(&mut self, f: Func) {
        self.funcs.insert(f);
    }
}
// impl FuncCollector for InlineCfg {
//     fn add_func(&mut self, f: Func) {
//         self.funcs.insert(f);
//     }
// }
pub struct Inline {
    blocks: BTreeMap<Block, Block>,
    return_to: Option<Block>,
    inline_funcs: Arc<InlineCfg>,
    stack: BTreeMap<Func, Block>,
}
pub fn inline_mod(m: &mut Module, mut cfg: InlineCfg) -> anyhow::Result<()> {
    crate::td::ix(m, &mut cfg);
    for f in m.funcs.iter().collect::<BTreeSet<_>>() {
        let mut g = take(&mut m.funcs[f]);
        if let FuncDecl::Body(s, _, b) = &mut g {
            // Convert to max SSA
            let b_cfg = CFGInfo::new(b);
            crate::waffle_passes_shared::maxssa::run(b, None, &b_cfg);
            
            let s = *s;
            let mut new = FunctionBody::new(&m, s);
            new.entry = match (Inline::new(cfg.clone())).translate(
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
            // Optimize
            let new_cfg = CFGInfo::new(&new);
            crate::passes::basic_opt::basic_opt(&mut new, &new_cfg, &Default::default());
            crate::passes::empty_blocks::run(&mut new);
            *b = new;
        }
        m.funcs[f] = g;
    }
    Ok(())
}
impl Inline {
    pub fn new(a: InlineCfg) -> Self {
        Self {
            blocks: BTreeMap::new(),
            return_to: None,
            inline_funcs: Arc::new(a),
            stack: Default::default(),
        }
    }
    /// Allocates a destination block for `k` without processing its body.
    /// If already allocated, returns the existing block.
    fn alloc_block(&mut self, dst: &mut FunctionBody, k: Block) -> Block {
        if let Some(&b) = self.blocks.get(&k) {
            return b;
        }
        let new = dst.add_block();
        // Patch any forward-reference sentinels inserted by the recursion guard.
        for v in self.blocks.values_mut() {
            if v.is_invalid() {
                *v = new;
            }
        }
        self.blocks.insert(k, new);
        new
    }

    pub fn translate(
        &mut self,
        module: &Module,
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
        module: &Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        queue: &mut VecDeque<Block>,
    ) -> anyhow::Result<()> {
        let mut new = *self.blocks.get(&k).unwrap();
        let mut state = src.blocks[k]
            .params
            .iter()
            .map(|(k, v)| (*v, vec![dst.add_blockparam(new, *k)]))
            .collect::<BTreeMap<_, _>>();
        'a: for i in src.blocks[k].insts.iter().cloned() {
            let i = i.value;
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
            let v = match &src.values[i] {
                crate::ValueDef::BlockParam(block, _, _) => todo!(),
                crate::ValueDef::Operator(operator, list_ref, list_ref1) => match operator {
                    Operator::Call { function_index }
                        if self.inline_funcs.funcs.contains(function_index)
                            && !self.stack.contains_key(function_index)
                            && module.funcs[*function_index].body().is_some() =>
                    {
                        let Some(b) = module.funcs[*function_index].body() else {
                            unreachable!()
                        };
                        let k2 = dst.add_block();
                        let tys = &src.type_pool[*list_ref1];
                        let args = src.arg_pool[*list_ref]
                            .iter()
                            .filter_map(|a| state.get(a))
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        let ke = Inline {
                            blocks: Default::default(),
                            return_to: Some(k2),
                            inline_funcs: self.inline_funcs.clone(),
                            stack: {
                                let mut a = self.stack.clone();
                                a.insert(*function_index, Block::invalid());
                                a
                            },
                        }
                        .translate(module, dst, b, b.entry)?;
                        dst.set_terminator(
                            new,
                            crate::Terminator::Br {
                                target: BlockTarget {
                                    block: ke,
                                    args: args,
                                },
                            },
                        );
                        new = k2;
                        tys.iter()
                            .cloned()
                            .map(|a| dst.add_blockparam(new, a))
                            .collect()
                    }
                    operator => {
                        let args = src.arg_pool[*list_ref]
                            .iter()
                            .filter_map(|a| state.get(a))
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        let tys = &src.type_pool[*list_ref1];
                        let v = dst.add_op(new, operator.clone(), &args, tys);
                        results_ref_2(dst, v)
                    }
                },
                crate::ValueDef::PickOutput(value, a, b) => {
                    let value = state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?;
                    let new_value = value[*a as usize];
                    dst.append_to_block(new, new_value);
                    vec![new_value]
                }
                crate::ValueDef::Alias(value) => state
                    .get(value)
                    .cloned()
                    .context("in getting the referenced value")?,
                crate::ValueDef::Placeholder(_) => todo!(),
                crate::ValueDef::None => vec![],
            };
            state.insert(i, v);
        }
        // Helper: allocate successor block (if needed) and enqueue for processing.
        let mut ensure_succ = |this: &mut Self, dst: &mut FunctionBody, succ: Block| -> Block {
            let b = this.alloc_block(dst, succ);
            queue.push_back(succ);
            b
        };
        let remap_args = |target: &BlockTarget, state: &BTreeMap<_, Vec<_>>| -> Vec<_> {
            target
                .args
                .iter()
                .filter_map(|b| state.get(b))
                .flatten()
                .cloned()
                .collect()
        };
        let t = match &src.blocks[k].terminator.terminator {
            &crate::Terminator::UB => crate::Terminator::UB,
            crate::Terminator::Br { target } => {
                let args = remap_args(target, &state);
                let block = ensure_succ(self, dst, target.block);
                crate::Terminator::Br {
                    target: BlockTarget { block, args },
                }
            }
            crate::Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => {
                let true_args = remap_args(if_true, &state);
                let true_block = ensure_succ(self, dst, if_true.block);
                let false_args = remap_args(if_false, &state);
                let false_block = ensure_succ(self, dst, if_false.block);
                let cond = state
                    .get(cond)
                    .cloned()
                    .context("in getting the referenced value")?;
                crate::Terminator::CondBr {
                    cond: cond[0],
                    if_true: BlockTarget { block: true_block, args: true_args },
                    if_false: BlockTarget { block: false_block, args: false_args },
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
                let default_args = remap_args(default, &state);
                let default_block = ensure_succ(self, dst, default.block);
                let targets = targets
                    .iter()
                    .map(|t| {
                        let args = remap_args(t, &state);
                        let block = ensure_succ(self, dst, t.block);
                        anyhow::Ok(BlockTarget { block, args })
                    })
                    .collect::<anyhow::Result<Vec<_>>>()?;
                crate::Terminator::Select {
                    value: value[0],
                    targets,
                    default: BlockTarget { block: default_block, args: default_args },
                }
            }
            crate::Terminator::Return { values } => match self.return_to {
                None => crate::Terminator::Return {
                    values: values
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                },
                Some(ret) => crate::Terminator::Br {
                    target: BlockTarget {
                        block: ret,
                        args: values
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                },
            },
            crate::Terminator::ReturnCall { func, args } => match self.return_to {
                None => crate::Terminator::ReturnCall {
                    func: *func,
                    args: args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                },
                Some(ret) => {
                    if self.inline_funcs.funcs.contains(func)
                        && module.funcs[*func].body().is_some()
                    {
                        match self.stack.get(func) {
                            None => {
                                let Some(b) = module.funcs[*func].body() else {
                                    unreachable!()
                                };
                                let call_args = args
                                    .iter()
                                    .filter_map(|a| state.get(a))
                                    .flatten()
                                    .cloned()
                                    .collect::<Vec<_>>();
                                let ke = Inline {
                                    blocks: Default::default(),
                                    return_to: Some(ret),
                                    inline_funcs: self.inline_funcs.clone(),
                                    stack: {
                                        let mut a = self.stack.clone();
                                        a.insert(*func, Block::invalid());
                                        a
                                    },
                                }
                                .translate(module, dst, b, b.entry)?;
                                Terminator::Br {
                                    target: BlockTarget {
                                        block: ke,
                                        args: call_args,
                                    },
                                }
                            }
                            Some(&k2) => {
                                let call_args = args
                                    .iter()
                                    .filter_map(|a| state.get(a))
                                    .flatten()
                                    .cloned()
                                    .collect::<Vec<_>>();
                                Terminator::Br {
                                    target: BlockTarget { block: k2, args: call_args },
                                }
                            }
                        }
                    } else {
                        let tys = match &module.signatures[module.funcs[*func].sig()] {
                            SignatureData::Func { returns, .. } => returns,
                            _ => todo!(),
                        };
                        let call_args = args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        let values = dst.add_op(
                            new,
                            Operator::Call { function_index: *func },
                            &call_args,
                            tys,
                        );
                        let values = results_ref_2(dst, values);
                        crate::Terminator::Br {
                            target: BlockTarget {
                                block: ret,
                                args: values,
                            },
                        }
                    }
                }
            },
            crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                match self.return_to {
                    None => crate::Terminator::ReturnCallIndirect {
                        sig: *sig,
                        table: *table,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(ret) => {
                        let tys = match &module.signatures[*sig] {
                            SignatureData::Func { returns, .. } => returns,
                            _ => todo!(),
                        };
                        let call_args = args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        let values = dst.add_op(
                            new,
                            Operator::CallIndirect {
                                sig_index: *sig,
                                table_index: *table,
                            },
                            &call_args,
                            tys,
                        );
                        let values = results_ref_2(dst, values);
                        crate::Terminator::Br {
                            target: BlockTarget {
                                block: ret,
                                args: values,
                            },
                        }
                    }
                }
            }
            crate::Terminator::ReturnCallRef { sig, args } => match self.return_to {
                None => crate::Terminator::ReturnCallRef {
                    sig: *sig,
                    args: args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                },
                Some(ret) => {
                    let tys = match &module.signatures[*sig] {
                        SignatureData::Func { returns, .. } => returns,
                        _ => todo!(),
                    };
                    let call_args = args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect::<Vec<_>>();
                    let values =
                        dst.add_op(new, Operator::CallRef { sig_index: *sig }, &call_args, tys);
                    let values = results_ref_2(dst, values);
                    crate::Terminator::Br {
                        target: BlockTarget {
                            block: ret,
                            args: values,
                        },
                    }
                }
            },
            crate::Terminator::Unreachable => crate::Terminator::Unreachable,
            _ => crate::Terminator::None,
        };
        dst.set_terminator(new, t);
        Ok(())
    }
}
