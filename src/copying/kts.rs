use std::{collections::BTreeMap, default};

use anyhow::Context;
use arena_traits::IndexAlloc;

use crate::{
    cfg::CFGInfo, passes::basic_opt::value_is_pure, Block, BlockTarget, FunctionBody, Operator,
    ValueDef,
};
#[derive(Default)]
pub struct Kts {
    pub blocks: BTreeMap<Block, Block>,
}
impl Kts {
    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let new = dst.add_block();
            let mut state = src.blocks[k]
                .params
                .iter()
                .map(|(k, v)| (*v, dst.add_blockparam(new, *k)))
                .collect::<BTreeMap<_, _>>();
            self.blocks.insert(k, new);
            'a: for i in src.blocks[k].insts.iter().cloned() {
                if value_is_pure(i, src) {
                    let mut unused = true;
                    for j in src.blocks[k].insts.iter().cloned() {
                        src.values[j].visit_uses(&src.arg_pool, |u| {
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
            let mut target_ = |k: &BlockTarget| {
                anyhow::Ok(BlockTarget {
                    args: k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .collect(),
                    block: self.translate(dst, src, k.block)?,
                })
            };
            let t = match &src.blocks[k].terminator {
                crate::Terminator::Br { target } => crate::Terminator::Br {
                    target: target_(target)?,
                },
                crate::Terminator::CondBr {
                    cond,
                    if_true,
                    if_false,
                } => {
                    let if_true = target_(if_true)?;
                    let if_false = target_(if_false)?;
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
                    let default = target_(default)?;
                    let targets = targets
                        .iter()
                        .map(target_)
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
            };
            dst.set_terminator(new, t);
        });
    }
}
