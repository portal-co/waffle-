use crate::{
    CFGInfo, Block, BlockTarget, Func, FunctionBody,
    HeapType, Operator, Type, ValueDef, WithNullable,
};
use alloc::borrow::ToOwned;
use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Context;
use waffle_passes_shared::value_is_pure;
use crate::arena_traits::IndexAlloc;
use core::default;
#[derive(Default)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
pub struct Frint {
    pub blocks: BTreeMap<(Block, Vec<Option<Func>>), Block>,
}
impl Frint {
    pub fn translate_base(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        let params = src.blocks[k]
            .params
            .iter()
            .filter_map(|a| match &a.0 {
                Type::Heap(WithNullable {
                    value: HeapType::FuncRef | HeapType::Sig { .. },
                    ..
                }) => Some(None),
                _ => None,
            })
            .collect();
        return self.translate(dst, src, k, params);
    }
    /// Allocates a destination block for `(k, params)` without processing its body.
    fn alloc_block(
        &mut self,
        dst: &mut FunctionBody,
        k: Block,
        params: Vec<Option<Func>>,
    ) -> Block {
        if let Some(&b) = self.blocks.get(&(k, params.clone())) {
            return b;
        }
        let new = dst.add_block();
        self.blocks.insert((k, params), new);
        new
    }

    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        start: Block,
        start_params: Vec<Option<Func>>,
    ) -> anyhow::Result<Block> {
        let start_dst = self.alloc_block(dst, start, start_params.clone());
        // Queue items are (src_block, params_for_that_block).
        let mut queue: VecDeque<(Block, Vec<Option<Func>>)> = VecDeque::new();
        let mut processed: BTreeSet<(Block, Vec<Option<Func>>)> = BTreeSet::new();
        queue.push_back((start, start_params));
        while let Some((k, params)) = queue.pop_front() {
            if !processed.insert((k.clone(), params.clone())) {
                continue;
            }
            self.process_block(dst, src, k, params, &mut queue)?;
        }
        Ok(start_dst)
    }

    fn process_block(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        params: Vec<Option<Func>>,
        queue: &mut VecDeque<(Block, Vec<Option<Func>>)>,
    ) -> anyhow::Result<()> {
        let new = *self.blocks.get(&(k, params.clone())).unwrap();
        let mut p = params.iter();
        let mut state = src.blocks[k]
            .params
            .iter()
            .filter_map(|(ty, v)| match ty {
                Type::Heap(WithNullable {
                    value: HeapType::FuncRef | HeapType::Sig { .. },
                    ..
                }) => match p.next()? {
                    Some(f) => Some((
                        *v,
                        dst.add_op(
                            new,
                            Operator::RefFunc { func_index: *f },
                            &[],
                            &[ty.clone()],
                        ),
                    )),
                    None => Some((*v, dst.add_blockparam(new, *ty))),
                },
                _ => Some((*v, dst.add_blockparam(new, *ty))),
            })
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
                crate::ValueDef::Operator(operator, list_ref, list_ref1) => {
                    let args = src.arg_pool[*list_ref]
                        .iter()
                        .filter_map(|a| state.get(a))
                        .cloned()
                        .collect::<Vec<_>>();
                    let tys = &src.type_pool[*list_ref1];
                    dst.add_op(new, operator.clone(), &args, tys)
                }
                crate::ValueDef::PickOutput(value, a, b) => {
                    let value = state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?;
                    let new_value = dst.values.alloc(ValueDef::PickOutput(value, *a, *b));
                    dst.append_to_block(new, new_value);
                    new_value
                }
                crate::ValueDef::Alias(value) => state
                    .get(value)
                    .cloned()
                    .context("in getting the referenced value")?,
                crate::ValueDef::Placeholder(_) => todo!(),
                crate::ValueDef::None => dst.add_op(new, Operator::Nop, &[], &[]),
            };
            state.insert(i, v);
        }
        // Compute the successor (block, funcs) key for a target, allocate it, and enqueue.
        let mut ensure_target =
            |this: &mut Self,
             dst: &mut FunctionBody,
             target: &BlockTarget|
             -> anyhow::Result<BlockTarget> {
                let mut funcs = vec![];
                let args: Vec<_> = target
                    .args
                    .iter()
                    .filter_map(|b| state.get(b))
                    .filter_map(|b| {
                        if let Some(Type::Heap(WithNullable {
                            value: HeapType::FuncRef | HeapType::Sig { .. },
                            ..
                        })) = dst.values[*b].ty(&dst.type_pool)
                        {
                            match &dst.values[*b] {
                                ValueDef::Operator(Operator::RefFunc { func_index }, _, _) => {
                                    funcs.push(Some(*func_index));
                                    return None;
                                }
                                _ => {
                                    funcs.push(None);
                                    return Some(b);
                                }
                            }
                        }
                        Some(b)
                    })
                    .cloned()
                    .collect();
                let block = this.alloc_block(dst, target.block, funcs.clone());
                queue.push_back((target.block, funcs));
                anyhow::Ok(BlockTarget { args, block })
            };
        let t = match &src.blocks[k].terminator.terminator {
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
                    cond,
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
                    value,
                    targets,
                    default,
                }
            }
            crate::Terminator::Return { values } => crate::Terminator::Return {
                values: values
                    .iter()
                    .filter_map(|b| state.get(b))
                    .cloned()
                    .collect(),
            },
            crate::Terminator::ReturnCall { func, args } => crate::Terminator::ReturnCall {
                func: *func,
                args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
            },
            crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                crate::Terminator::ReturnCallIndirect {
                    sig: *sig,
                    table: *table,
                    args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                }
            }
            crate::Terminator::ReturnCallRef { sig, args } => {
                crate::Terminator::ReturnCallRef {
                    sig: *sig,
                    args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                }
            }
            crate::Terminator::Unreachable => crate::Terminator::Unreachable,
            crate::Terminator::None => crate::Terminator::None,
            &crate::Terminator::UB => crate::Terminator::UB,
            _ => todo!("Unknown terminator kind"),
        };
        dst.set_terminator(new, t);
        Ok(())
    }
}
