use std::{collections::BTreeMap, iter::empty};

use anyhow::Context;
use libc::name_t;

use crate::more::append_before;
use crate::{
    entity::{EntityRef, EntityVec},
    ExportKind, Func, FuncDecl, FunctionBody, Memory, Module, Operator, Type, ValueDef,
};
use itertools::Itertools;

pub struct Fuse {
    pub resolve: Func,
    pub grow: Func,
    pub size: Func,
}
pub fn get_exports(m: &Module) -> BTreeMap<String, ExportKind> {
    let mut b = BTreeMap::new();
    for e in m.exports.iter() {
        let e = e.clone();
        b.insert(e.name, e.kind);
    }
    return b;
}
pub fn finalize(m: &mut Module) {
    let mem = m.memories[Memory::new(0)].clone();
    m.memories = EntityVec::default();
    m.memories.push(mem);
}
impl Fuse {
    pub fn new(m: &Module) -> Option<Self> {
        let e = get_exports(m);
        let Some(ExportKind::Func(a)) = e.get("sk%resolve") else {
            return None;
        };
        let a = *a;
        let Some(ExportKind::Func(b)) = e.get("sk%grow") else {
            return None;
        };
        let b = *b;
        let Some(ExportKind::Func(c)) = e.get("sk%size") else {
            return None;
        };
        let c = *c;
        return Some(Fuse {
            resolve: a,
            grow: b,
            size: c,
        });
    }
    pub fn finalize(self, m: &mut Module) {
        let mem = m.memories[Memory::new(0)].clone();
        let l = m.memories.len() - 1;
        m.memories = EntityVec::default();
        m.memories.push(mem);
        let v = vec![self.resolve, self.grow, self.size];
        let mut new = vec![];
        for f in v.clone() {
            let n = m.funcs[f].clone();
            let s = n.sig();
            let name = n.name().to_owned();
            // let n = m.funcs.push(n);
            let mut b = FunctionBody::new(&m, s);
            let mut p = b.blocks[b.entry].params.iter().map(|a| a.1).collect_vec();
            let vz = b.arg_pool.from_iter(empty());
            let tz = b.type_pool.from_iter(empty());
            let ti = b.type_pool.from_iter(vec![Type::I32].into_iter());
            let i = b.add_value(ValueDef::Operator(
                Operator::I32Const { value: l as u32 },
                vz,
                ti,
            ));
            b.append_to_block(b.entry, i);
            let i = b.arg_pool.from_iter(vec![p[p.len() - 1], i].into_iter());
            let i = b.add_value(ValueDef::Operator(Operator::I32Add, i, ti));
            let l = p.len();
            p[l - 1] = i;
            b.append_to_block(b.entry, i);
            b.set_terminator(b.entry, crate::Terminator::ReturnCall { func: f, args: p });
            let n = FuncDecl::Body(s, name, b);
            let n = m.funcs.push(n);
            new.push(n);
        }
        for x in m.exports.iter_mut() {
            let ExportKind::Func(xf) = &mut x.kind else {
                continue;
            };
            for (o, n) in v.iter().zip(new.iter()) {
                if xf == o {
                    *xf = *n
                }
            }
        }
    }
    pub fn process(&self, f: &mut FunctionBody) {
        let vz = f.arg_pool.from_iter(empty());
        let tz = f.type_pool.from_iter(empty());
        let ti = f.type_pool.from_iter(vec![Type::I32].into_iter());
        let mut ka = BTreeMap::new();
        for v in f.values.iter().collect::<Vec<_>>() {
            // eprintln!("dbg: {v}");
            let k = f.value_blocks[v];
            let mut w = f.values[v].clone();
            let vi = v;
            if let ValueDef::Operator(a, b, c) = &mut w {
                let mut bp = f.arg_pool[*b].to_vec();
                match a.clone() {
                    Operator::MemorySize { mem } => {
                        if mem.index() != 0 {
                            let ia = f.add_value(ValueDef::Operator(
                                Operator::I32Const {
                                    value: mem.index() as u32 - 1,
                                },
                                vz,
                                ti,
                            ));
                            append_before(f, ia, vi, k);
                            *a = Operator::Call {
                                function_index: self.size,
                            };
                            bp.push(ia);
                        }
                    }
                    Operator::MemoryGrow { mem } => {
                        if mem.index() != 0 {
                            let ia = f.add_value(ValueDef::Operator(
                                Operator::I32Const {
                                    value: mem.index() as u32 - 1,
                                },
                                vz,
                                ti,
                            ));
                            append_before(f, ia, vi, k);
                            *a = Operator::Call {
                                function_index: self.grow,
                            };
                            bp.push(ia);
                        }
                    }
                    _ => crate::more::rewrite_mem(a, &mut bp, |m, v| {
                        if m.index() != 0 {
                            let ia = f.add_value(ValueDef::Operator(
                                Operator::I32Const {
                                    value: m.index() as u32 - 1,
                                },
                                vz,
                                ti,
                            ));
                            append_before(f, ia, vi, k);
                            if let Some(v) = v {
                                let w = f.arg_pool.from_iter(vec![*v, ia].into_iter());
                                let x = f.add_value(ValueDef::Operator(
                                    Operator::Call {
                                        function_index: self.resolve,
                                    },
                                    w,
                                    ti,
                                ));
                                crate::more::append_before(f, x, vi, k);
                                *v = x;
                            }
                            *m = Memory::new(0);
                        }
                    }),
                }
                *b = *ka
                    .entry(bp.clone())
                    .or_insert_with(|| f.arg_pool.from_iter(bp.into_iter()));
            }
            f.values[v] = w;
        }
    }
}
pub fn fuse(m: &mut Module) -> anyhow::Result<()> {
    let f = Fuse::new(m).context("in getting the fuse funcs")?;
    crate::passes::unmem::metafuse_all(m);
    crate::passes::splice::splice_module(m)?;
    m.per_func_body(|b| f.process(b));
    f.finalize(m);
    return Ok(());
}
