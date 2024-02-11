use std::{
    array, backtrace,
    collections::{BTreeMap, BTreeSet},
    default,
    ops::{Deref, DerefMut},
};

use crate::copying::block::{clone_block, locals, values};
use rand::{seq::SliceRandom, Rng};
use crate::{
    cfg::CFGInfo, passes::maxssa, pool::ListRef, Block, BlockTarget, Func, FunctionBody, Module,
    Operator, Signature, SignatureData, Terminator, Type, Value, ValueDef,
};
pub fn flat_map<T, E, D: Deref<Target = crate::FunctionBody> + DerefMut>(
    f: &mut D,
    b: Block,
    mut go: impl FnMut(&mut D, Block, Value) -> Result<T, E>,
) -> Result<Vec<T>, E> {
    let mut r = vec![];
    for v in f
        .blocks
        .get_mut(b)
        .unwrap()
        .insts
        .drain(..)
        .collect::<Vec<_>>()
    {
        r.push(go(f, b, v)?);
    }
    return Ok(r);
}

pub fn split_blocks(f: &mut FunctionBody, r: &mut Rand<impl Rng>) {
    f.convert_to_max_ssa(None);
    split_blocks_internal(f, r);
}
// #[tailcall::tailcall]
fn split_blocks_internal(f: &mut FunctionBody, r: &mut Rand<impl Rng>) {
    loop {
        let mut i = f.blocks.entries();
        let b = loop {
            let Some((j, k)) = i.next() else {
                drop(i);
                f.recompute_edges();
                // f.convert_to_max_ssa(None);
                f.validate().unwrap();
                return;
            };
            if let Terminator::Br { target } = &k.terminator {
                break j;
            }
        };
        drop(i);
        let k = f.blocks.get_mut(b).unwrap();
        let Terminator::Br { target } = &k.terminator else {
            // break j;
            panic!("invalid")
        };
        let target = target.clone();
        let mut v = vec![];

        let mut t2 = target.clone();
        drop(k);
        t2.block = clone_block(f, t2.block.clone());
        while r.0.gen() {
            v.push(t2.clone());
            t2.block = clone_block(f, t2.block.clone());
        }
        let k = f.blocks.get_mut(b).unwrap();
        let cond = r.fake(f, b, Type::I32);
        let t = if v.len() == 0 {
            Terminator::CondBr {
                cond: cond,
                if_true: target.clone(),
                if_false: t2,
            }
        } else {
            Terminator::Select {
                value: cond,
                targets: v,
                default: target.clone(),
            }
        };
        f.blocks[b].terminator = Terminator::None;
        f.set_terminator(b, t);
    }
}
// pub fn snip_block(f: &mut FunctionBody, b: Block) {
//     let mut d = f.blocks.get(b).unwrap().clone();
//     let t = d.terminator.clone();
//     let mut e = b;
//     let mut v = vec![];
//     for w in d.insts {
//         if let ValueDef::BlockParam(a, b, c) = f.values.get(w).unwrap() {
//             v.push(w);
//             continue;
//         }
//         let n = f.add_block();
//         f.append_to_block(n, w);
//         f.set_terminator(
//             e,
//             Terminator::Br {
//                 target: BlockTarget {
//                     block: n,
//                     args: vec![],
//                 },
//             },
//         );
//         e = n;
//     }
//     f.set_terminator(e, t);
//     for w in v {
//         f.append_to_block(b, w);
//     }
//     maxssa::run(f, None, &CFGInfo::new(&*f));
// }
// pub fn snip_blocks(f: &mut FunctionBody) {
//     for b in f.blocks.entries().map(|a| a.0).collect::<Vec<_>>() {
//         snip_block(f, b);
//     }
// }
// pub fn bar(m: BTreeMap<u8, u8>) -> [u8; 256] {
//     array::from_fn(|i| *m.get(&(i as u8)).unwrap())
// }
pub fn vecify<T>(mut a: BTreeMap<usize, T>) -> Vec<T> {
    let mut v = vec![];
    loop {
        let Some(b) = a.remove(&v.len()) else {
            return v;
        };
        v.push(b);
    }
}
pub fn sbox(x: &mut impl Rng, size: usize) -> BTreeMap<usize, usize> {
    let mut m = BTreeMap::new();
    let mut v = BTreeSet::new();
    let mut w = BTreeSet::new();
    while m.len() != size {
        let mut a = x.gen_range(0..size);
        while v.contains(&a) {
            a = x.gen_range(0..size);
        }
        v.insert(a);
        let mut b = x.gen_range(0..size);
        while w.contains(&b) {
            b = x.gen_range(0..size);
        }
        w.insert(b);
        m.insert(a, b);
    }
    return m;
}
pub fn invert<T: Eq + Ord, U: Eq + Ord>(s: BTreeMap<T, U>) -> BTreeMap<U, T> {
    let mut v = BTreeMap::new();
    for (a, b) in s {
        v.insert(b, a);
    }
    return v;
}
pub fn render(a: BTreeMap<usize, usize>, m: &mut Module, t: Type) -> Func {
    let s = m.signatures.push(SignatureData {
        params: vec![t],
        returns: vec![t],
    });
    let mut f = FunctionBody::new(m, s);
    let mut k = BTreeMap::new();
    for (d, c) in a.clone() {
        let e = f.add_block();
        let to = f.single_type_list(t);
        let ai = f.arg_pool.from_iter(vec![].into_iter());
        let v = f.add_value(ValueDef::Operator(
            match t {
                crate::Type::I32 => Operator::I32Const { value: c as u32 },
                crate::Type::I64 => Operator::I64Const { value: c as u64 },
                crate::Type::F32 => Operator::F32Const { value: c as u32 },
                crate::Type::F64 => Operator::F64Const { value: c as u64 },
                crate::Type::V128 => todo!(),
                crate::Type::FuncRef => todo!(),
            },
            ai.clone(),
            to,
        ));
        f.append_to_block(e, v);
        f.set_terminator(e, Terminator::Return { values: vec![v] });
        k.insert(
            d,
            BlockTarget {
                block: e,
                args: vec![],
            },
        );
    }
    let a = f.blocks[f.entry].params[0].1.clone();
    f.set_terminator(
        f.entry,
        Terminator::Select {
            value: a,
            targets: vecify(k),
            default: BlockTarget {
                block: f.entry,
                args: vec![a],
            },
        },
    );
    return m
        .funcs
        .push(crate::FuncDecl::Body(s, format!("{:?}", a), f));
}

pub struct Rand<T>(pub T);
pub trait FakeValBehavior {
    fn fake(&mut self, f: &mut FunctionBody, b: Block, t: Type) -> Value;
}
impl<R: Rng> FakeValBehavior for Rand<R> {
    fn fake(&mut self, f: &mut FunctionBody, b: Block, t: Type) -> Value {
        loop {
            if self.0.gen_bool(0.1) {
                let to = f.single_type_list(t);
                let ai = f.arg_pool.from_iter(vec![].into_iter());
                let v = f.add_value(ValueDef::Operator(
                    match t {
                        crate::Type::I32 => Operator::I32Const {
                            value: self.0.gen(),
                        },
                        crate::Type::I64 => Operator::I64Const {
                            value: self.0.gen(),
                        },
                        crate::Type::F32 => Operator::F32Const {
                            value: self.0.gen(),
                        },
                        crate::Type::F64 => Operator::F64Const {
                            value: self.0.gen(),
                        },
                        crate::Type::V128 => todo!(),
                        crate::Type::FuncRef => todo!(),
                    },
                    ai.clone(),
                    to,
                ));
                f.append_to_block(b, v);
                return v;
            } else {
                // for v in values(f, b){
                //     if self.0.gen_bool(0.75){
                //         continue;
                //     }
                loop {
                    if let Some(v) = locals(f, b)
                        .into_iter()
                        .collect::<Vec<_>>()
                        .choose(&mut self.0)
                    {
                        if f.values[v.clone()].ty(&f.type_pool) == Some(t) {
                            // dbg!(&v);
                            return v.clone();
                        }
                        if self.0.gen_bool(0.1) {
                            break;
                        }
                    } else {
                        // dbg!("not found");
                        break;
                    };
                }
            }
        }
    }
}
pub struct JustNormalCFF {}
impl FakeValBehavior for JustNormalCFF {
    fn fake(&mut self, f: &mut FunctionBody, b: Block, t: Type) -> Value {
        let to = f.single_type_list(t);
        let ai = f.arg_pool.from_iter(vec![].into_iter());
        let v = f.add_value(ValueDef::Operator(
            match t {
                crate::Type::I32 => Operator::I32Const { value: 0 },
                crate::Type::I64 => Operator::I64Const { value: 0 },
                crate::Type::F32 => Operator::F32Const { value: 0 },
                crate::Type::F64 => Operator::F64Const { value: 0 },
                crate::Type::V128 => todo!(),
                crate::Type::FuncRef => todo!(),
            },
            ai.clone(),
            to,
        ));
        f.append_to_block(b, v);
        return v;
    }
}
impl CFFSpecial for JustNormalCFF {
    fn choose(&mut self, b: BTreeSet<usize>) -> usize {
        return b.into_iter().next().unwrap();
    }

    fn warp(&mut self, a: Vec<Block>) -> Option<Vec<Block>> {
        None
    }
}
pub trait CFFSpecial {
    fn choose(&mut self, b: BTreeSet<usize>) -> usize;
    fn warp(&mut self, a: Vec<Block>) -> Option<Vec<Block>>;
}
impl<R: Rng> CFFSpecial for Rand<R> {
    fn choose(&mut self, b: BTreeSet<usize>) -> usize {
        return *b
            .into_iter()
            .collect::<Vec<_>>()
            .choose(&mut self.0)
            .unwrap();
    }

    fn warp(&mut self, mut a: Vec<Block>) -> Option<Vec<Block>> {
        if self.0.gen_bool(0.35) {
            return None;
        }
        a.shuffle(&mut self.0);
        return Some(a);
    }
}
pub fn cff(f: &mut FunctionBody, h: &mut (impl FakeValBehavior + CFFSpecial)) {
    f.convert_to_max_ssa(None);
    let mut params = BTreeMap::new();
    let mut ids: BTreeMap<Block, BTreeSet<usize>> = BTreeMap::new();
    let mut swc = vec![];
    let new = f.add_block();
    let fr = f.add_blockparam(new, crate::Type::I32);
    let k = f
        .blocks
        .entries()
        .map(|a| a.0)
        .filter(|b| *b != new)
        // .enumerate()
        .collect::<Vec<_>>();
    let mut ms = BTreeMap::new();
    let mut ns = BTreeMap::new();
    for b in k.iter() {
        let mut m = vec![];
        let mut n = ns.clone();
        for (pk, (pt, pv)) in f.blocks[*b]
            .clone()
            .params
            .iter()
            .map(|(a, b)| (a.clone(), b.clone()))
            .enumerate()
        {
            let hpv = match n.entry(pt.clone()).or_insert(vec![]).pop() {
                None => {
                    let hpv = f.add_blockparam(new, pt.clone());
                    ns.entry(pt.clone()).or_insert(vec![]).push(hpv);
                    hpv
                },
                Some(a) => a,
            };
            m.push(hpv);
            let ValueDef::BlockParam(_, i, _) = f.values[hpv] else {
                unreachable!()
            };
            params.insert((*b, pk), i);
        }
        ms.insert(*b, m);
    }
    let mut k = Some(k);
    while let Some(l) = k.take() {
        for b in l.iter() {
            // let mut m = vec![];
            // for (pk, (pt, pv)) in f.blocks[*b]
            //     .clone()
            //     .params
            //     .iter()
            //     .map(|(a, b)| (a.clone(), b.clone()))
            //     .enumerate()
            // {
            //     let hpv = f.add_blockparam(new, pt.clone());
            //     m.push(hpv);
            //     let ValueDef::BlockParam(_, i, _) = f.values[hpv] else {
            //         unreachable!()
            //     };
            //     params.insert((*b, pk), i);
            // }
            ids.entry(*b).or_default().insert(swc.len());
            swc.push(BlockTarget {
                block: *b,
                args: ms.get(b).unwrap().clone(),
            });
        }
        k = h.warp(l);
    }
    f.set_terminator(
        new,
        Terminator::Select {
            value: fr,
            targets: swc,
            default: BlockTarget {
                block: new,
                args: f.blocks[new]
                    .params
                    .clone()
                    .into_iter()
                    .map(|a| a.1)
                    .collect(),
            },
        },
    );
    let mut warp = |f: &mut FunctionBody, a: BlockTarget, b: Block| -> BlockTarget {
        let ai = f.arg_pool.from_iter(vec![].into_iter());
        let ti = f.single_type_list(Type::I32);
        let mut np = f.blocks[new]
            .params
            .clone()
            .into_iter()
            .map(|a| {
                // let to = f.single_type_list(a.0);
                // f.add_value(ValueDef::Operator(
                //     match a.0 {
                //         crate::Type::I32 => Operator::I32Const { value: 0 },
                //         crate::Type::I64 => Operator::I64Const { value: 0 },
                //         crate::Type::F32 => Operator::F32Const { value: 0 },
                //         crate::Type::F64 => Operator::F64Const { value: 0 },
                //         crate::Type::V128 => todo!(),
                //         crate::Type::FuncRef => todo!(),
                //     },
                //     ai.clone(),
                //     to,
                // ))
                h.fake(f, b, a.0)
            })
            .collect::<Vec<_>>();
        // for m in np.clone() {
        //     f.append_to_block(b, m);
        // }
        for p in a.args.iter().enumerate() {
            // dbg!(&a, &p);
            np[*params.get(&(a.block, p.0)).unwrap() as usize] = *p.1
        }
        np[0] = f.add_value(ValueDef::Operator(
            Operator::I32Const {
                value: h.choose(ids.get(&a.block).unwrap().clone()) as u32,
            },
            ai,
            ti,
        ));
        f.append_to_block(b, np[0]);
        return BlockTarget {
            block: new,
            args: np,
        };
    };
    for (k, d) in f
        .blocks
        .entries()
        .map(|(a, b)| (a, b.clone()))
        .collect::<Vec<_>>()
    {
        if k == new {
            continue;
        }
        f.blocks[k].terminator = Terminator::None;
        match &d.terminator {
            Terminator::Br { target } => {
                let target = warp(f, target.clone(), k);
                f.set_terminator(k, Terminator::Br { target: target })
            }
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => {
                let if_true = warp(f, if_true.clone(), k);
                let if_false = warp(f, if_false.clone(), k);
                f.set_terminator(
                    k,
                    Terminator::CondBr {
                        cond: cond.clone(),
                        if_true,
                        if_false,
                    },
                )
            }
            Terminator::Select {
                value,
                targets,
                default,
            } => {
                let default = warp(f, default.clone(), k);
                let targets = targets.clone().into_iter().map(|a| warp(f, a, k)).collect();
                f.set_terminator(
                    k,
                    Terminator::Select {
                        value: value.clone(),
                        targets,
                        default,
                    },
                );
            }
            Terminator::Return { values } => f.set_terminator(
                k,
                Terminator::Return {
                    values: values.clone(),
                },
            ),
            Terminator::Unreachable => f.set_terminator(k, Terminator::Unreachable),
            Terminator::None => {},
            _ => f.set_terminator(k, d.terminator.clone())
        }
    }
    f.recompute_edges();
}
#[cfg(test)]
mod tests {
    use super::*;
}
