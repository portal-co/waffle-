use alloc::borrow::ToOwned;
use alloc::vec;
use alloc::vec::Vec;
use alloc::{collections::BTreeMap, string::String};
use anyhow::Context;
use core::{
    convert::Infallible,
    iter::{empty, once},
};
use waffle_passes::{
    entity::{EntityRef, EntityVec},
    ExportKind, Func, FuncDecl, FunctionBody, Memory, Module, Operator, Type, ValueDef,
};
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
pub struct Fuse {
    pub resolve: Func,
    pub grow: Func,
    pub size: Func,
    pub target: Memory,
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
        let Some(ExportKind::Memory(d)) = e.get("memory") else {
            return None;
        };
        let d = *d;
        return Some(Fuse {
            resolve: a,
            grow: b,
            size: c,
            target: d,
        });
    }
    pub fn finalize(self, m: &mut Module) -> Memory {
        let mem = m.memories[self.target].clone();
        m.memories = EntityVec::default();
        let new = m.memories.push(mem);
        let mut fs = BTreeMap::new();
        fs.insert(self.target, new);
        waffle_passes::passes::reorder_funs::reorder_mems(m, &fs);
        return new;
    }
    pub fn process(&self, m: &mut Module, f: &mut FunctionBody) {
        let vz = f.arg_pool.from_iter(empty());
        let tz = f.type_pool.from_iter(empty());
        let ti = f.type_pool.from_iter(vec![Type::I32].into_iter());
        let mut ka = BTreeMap::new();
        for k in f.blocks.iter().collect::<Vec<_>>() {
            for v in core::mem::take(&mut f.blocks[k].insts) {
                let mut w = f.values[v.value].clone();
                if let ValueDef::Operator(a, b, c) = &mut w {
                    let mut bp = f.arg_pool[*b].to_vec();
                    fn g(
                        a: impl for<'a> FnMut(
                            &mut Module,
                            &mut FunctionBody,
                            Memory,
                            &'a mut waffle_passes::Value,
                        ),
                    ) -> impl for<'a> FnMut(&mut Module, &mut FunctionBody, Memory, &'a mut waffle_passes::Value)
                    {
                        return a;
                    }
                    let mut p = g(|m: &mut Module, f, mem, v| {
                        match (m.memories[mem].memory64, m.memories[self.target].memory64) {
                            (true, true) => {}
                            (true, false) => {
                                let ti = f.type_pool.from_iter(once(Type::I32));
                                let w = f.arg_pool.from_iter(vec![*v].into_iter());
                                let x =
                                    f.add_value(ValueDef::Operator(Operator::I32WrapI64, w, ti));
                                f.append_to_block(k, x);
                                *v = x;
                            }
                            (false, true) => {
                                let ti = f.type_pool.from_iter(once(Type::I64));
                                let w = f.arg_pool.from_iter(vec![*v].into_iter());
                                let x =
                                    f.add_value(ValueDef::Operator(Operator::I64ExtendI32U, w, ti));
                                f.append_to_block(k, x);
                                *v = x;
                            }
                            (false, false) => {}
                        }
                    });
                    match a.clone() {
                        Operator::MemorySize { mem } => {
                            if mem != self.target {
                                let ia = f.add_value(ValueDef::Operator(
                                    Operator::I32Const {
                                        value: mem.index() as u32,
                                    },
                                    vz,
                                    ti,
                                ));
                                f.append_to_block(k, ia);
                                *a = Operator::Call {
                                    function_index: self.size,
                                };
                                bp.push(ia);
                                p(m, f, mem, &mut bp[0]);
                            }
                        }
                        Operator::MemoryGrow { mem } => {
                            if mem != self.target {
                                let ia = f.add_value(ValueDef::Operator(
                                    Operator::I32Const {
                                        value: mem.index() as u32,
                                    },
                                    vz,
                                    ti,
                                ));
                                f.append_to_block(k, ia);
                                *a = Operator::Call {
                                    function_index: self.grow,
                                };
                                bp.push(ia);
                                p(m, f, mem, &mut bp[0]);
                            }
                        }
                        _ => waffle_passes::op_traits::rewrite_mem(a, &mut bp, |mem, v| {
                            if *mem != self.target {
                                let ia = f.add_value(ValueDef::Operator(
                                    Operator::I32Const {
                                        value: mem.index() as u32,
                                    },
                                    vz,
                                    ti,
                                ));
                                f.append_to_block(k, ia);
                                if let Some(v) = v {
                                    p(m, f, *mem, &mut *v);
                                    let w = f.arg_pool.from_iter(vec![*v, ia].into_iter());
                                    let x = f.add_value(ValueDef::Operator(
                                        Operator::Call {
                                            function_index: self.resolve,
                                        },
                                        w,
                                        ti,
                                    ));
                                    f.append_to_block(k, x);
                                    *v = x;
                                }
                                *mem = self.target;
                            }
                            Ok::<(), Infallible>(())
                        })
                        .unwrap(),
                    }
                    *b = *ka
                        .entry(bp.clone())
                        .or_insert_with(|| f.arg_pool.from_iter(bp.into_iter()));
                }
                f.values[v.value] = w;
                f.append_to_block(k, v.value);
            }
        }
    }
}
pub fn fuse(m: &mut Module) -> anyhow::Result<()> {
    let f = Fuse::new(m).context("in getting the fuse funcs")?;
    crate::unmem::metafuse_all(m, &mut crate::unmem::All {});
    m.take_per_func_body(|m, b| f.process(m, b));
    f.finalize(m);
    return Ok(());
}
