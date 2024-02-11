use std::{collections::{BTreeMap, BTreeSet}, ops::{Deref, DerefMut}};

use crate::{
    cfg::CFGInfo, pool::ListRef, Block, BlockTarget, FrontendOptions, Func, FunctionBody, Memory,
    MemoryArg, Module, Operator, Signature, SignatureData, Terminator, Type, Value, ValueDef,
};

use crate::more::Flix;


pub fn tweak_value(
    f: &mut FunctionBody,
    x: &mut ValueDef,
    mut m: impl FnMut(&mut Value),
    b: Block,
) {
    match x {
        ValueDef::BlockParam(a, _, _) => *a = b,
        ValueDef::Operator(_, l, _) => {
            *l = f.arg_pool.deep_clone(l.clone());
            for v in &mut f.arg_pool[l.clone()] {
                m(v)
            }
        }
        ValueDef::PickOutput(v, _, _) => m(v),
        ValueDef::Alias(v) => m(v),
        ValueDef::Placeholder(_) => todo!(),
        ValueDef::Trace(_, l) => {
            *l = f.arg_pool.deep_clone(l.clone());
            for v in &mut f.arg_pool[l.clone()] {
                m(v)
            }
        }
        ValueDef::None => todo!(),
    }
}
pub fn tweak_target(f: &mut FunctionBody, x: &mut BlockTarget, mut m: impl FnMut(&mut Value)) {
    for a in &mut x.args {
        m(a)
    }
}
pub fn tweak_terminator(f: &mut FunctionBody, x: &mut Terminator, mut m: impl FnMut(&mut Value)) {
    match x {
        Terminator::Br { target } => tweak_target(f, target, m),
        Terminator::CondBr {
            cond,
            if_true,
            if_false,
        } => {
            m(cond);
            tweak_target(f, if_true, &mut m);
            tweak_target(f, if_false, m);
        }
        Terminator::Select {
            value,
            targets,
            default,
        } => {
            m(value);
            for target in targets {
                tweak_target(f, target, &mut m)
            }
            tweak_target(f, default, m)
        }
        Terminator::Return { values } => {
            for a in values {
                m(a)
            }
        }
        Terminator::ReturnCall { func, args } =>             for a in args {
            m(a)
        },
        Terminator::ReturnCallIndirect { sig, table, args } =>             for a in args {
            m(a)
        },
        Terminator::Unreachable => {}
        Terminator::None => {}
    }
}
pub fn clone_value(
    f: &mut FunctionBody,
    mut m: impl FnMut(&mut Value),
    v: Value,
    b: Block,
) -> Value {
    let mut w = f.values.get(v).unwrap().clone();
    tweak_value(f, &mut w, m, b);
    return f.add_value(w);
}
pub fn clone_block(f: &mut FunctionBody, b: Block) -> Block {
    let mut d = f.blocks.get(b).unwrap().clone();
    let mut m: BTreeMap<Value, Value> = BTreeMap::new();
    let r = f.add_block();
    for (pt, pv) in d.params.clone() {
        m.insert(pv, f.add_blockparam(r, pt));
    }
    for v in &mut d.insts {
        let n = clone_value(
            f,
            |a| {
                *a = match m.get(&a) {
                    None => a.clone(),
                    Some(b) => b.clone(),
                }
            },
            v.clone(),
            r,
        );
        m.insert((*v).clone(), n.clone());
        *v = n;
        f.append_to_block(r, n);
    }
    tweak_terminator(f, &mut d.terminator, |a| {
        *a = match m.get(&a) {
            None => a.clone(),
            Some(b) => b.clone(),
        }
    });
    // let mut c = f.blocks.get_mut(r).unwrap();
    // for a in d.insts.clone(){
    //     f.append_to_block(r, a);
    // }
    f.set_terminator(r, d.terminator.clone());
    return r;
}

pub fn values(f: &FunctionBody, b: Block) -> BTreeSet<Value> {
    let c = CFGInfo::new(f);
    let mut s = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut v = vec![b];
    while let Some(w) = v.pop() {
        if visited.contains(&w) {
            continue;
        }
        visited.insert(w.clone());
        s.extend(f.blocks.get(w).unwrap().insts.clone());
        for (k, _) in f.blocks.entries() {
            if c.dominates(k, w) && k != w && !visited.contains(&k) {
                // dbg!(&k);
                v.push(k)
            }
        }
    }
    // dbg!(&s);
    return s;
}

pub fn locals(f: &FunctionBody, b: Block) -> BTreeSet<Value> {
    return f.blocks[b]
        .params
        .iter()
        .map(|a| a.1)
        .chain(f.blocks[b].insts.clone())
        .collect();
}
pub fn sop_i32(f: &mut FunctionBody, b: Block, x: Value, y: u32, o: Operator) -> Value {
    let t = f.single_type_list(Type::I32);
    let vi = f.add_value(ValueDef::Operator(
        Operator::I32Const { value: y },
        ListRef::default(),
        t,
    ));
    f.append_to_block(b, vi);
    let v = f.arg_pool.double(x, vi);
    let w = f.add_value(ValueDef::Operator(o, v, t));
    f.append_to_block(b, w);
    return w;
}
pub fn results<T: Deref<Target = Module<'static>> + DerefMut>(f: &mut Flix<T>, c: Value) -> Option<Vec<Value>>{
    let c = f.resolve_and_update_alias(c);
    let b = f.value_blocks[c];
    let ValueDef::Operator(Operator::Call { function_index }, _1, _2) = f.values[c] else{
        return None;
    };
    let mut v = vec![];
    let s = f.mo.funcs[function_index].sig();
    for (s,i) in f.mo.signatures[s].returns.clone().into_iter().enumerate(){
        let w = f.add_value(ValueDef::PickOutput(c, s as u32, i));
        f.append_to_block(b, w);
        v.push(w);
    };

    return Some(v);
}
pub fn make_memcpy(m: &mut Module, _1: Memory, _2: Memory, swizzle: bool) -> Func {
    let mut b = FunctionBody::default();
    let e = b.entry.clone();
    let k = make_memcpy_body(&mut b, e, _1, _2, swizzle);
    b.set_terminator(k, Terminator::Return { values: vec![] });
    let s = m.signatures.push(SignatureData {
        params: vec![Type::I32, Type::I32, Type::I32],
        returns: vec![],
    });
    return m
        .funcs
        .push(crate::FuncDecl::Body(s,format!("memcpy_{_1}_{_2}_swizzle_{swizzle}"), b));
}
pub fn make_memcpy_body(
    f: &mut FunctionBody,
    b: Block,
    _1: Memory,
    _2: Memory,
    swizzle: bool,
) -> Block {
    let k = f.add_block();
    let a = f.add_blockparam(b, Type::I32);
    let c = f.add_blockparam(b, Type::I32);
    let d = f.add_blockparam(b, Type::I32);

    let ra = f.arg_pool.single(a);
    let rc = f.arg_pool.single(c);
    let t = f.single_type_list(Type::I32);
    let l = f.add_value(ValueDef::Operator(
        crate::Operator::I32Load8U {
            memory: MemoryArg {
                align: 1,
                offset: 0,
                memory: _1,
            },
        },
        ra,
        t,
    ));
    f.append_to_block(b, l);
    let m = if swizzle {
        let l = f.add_value(ValueDef::Operator(
            crate::Operator::I32Load8U {
                memory: MemoryArg {
                    align: 1,
                    offset: 0,
                    memory: _2,
                },
            },
            rc,
            t,
        ));
        f.append_to_block(b, l);
        Some(l)
    } else {
        None
    };
    let rc = f.arg_pool.double(c, l);
    let ra = m.map(|l| f.arg_pool.double(a, l));
    // let u = f.type_pool.allocate(0, Type::I32);
    let m = f.add_value(ValueDef::Operator(
        crate::Operator::I32Store8 {
            memory: MemoryArg {
                align: 1,
                offset: 0,
                memory: _2,
            },
        },
        rc,
        ListRef::default(),
    ));
    f.append_to_block(b, m);
    if let Some(ra) = ra {
        let m = f.add_value(ValueDef::Operator(
            crate::Operator::I32Store8 {
                memory: MemoryArg {
                    align: 1,
                    offset: 0,
                    memory: _1,
                },
            },
            ra,
            ListRef::default(),
        ));
        f.append_to_block(b, m);
    }
    let mut r = vec![];
    r.push(sop_i32(f, b, a, 1, Operator::I32Add));
    r.push(sop_i32(f, b, c, 1, Operator::I32Add));
    r.push(sop_i32(f, b, d, 1, Operator::I32Sub));
    f.set_terminator(
        b,
        Terminator::Select {
            value: d,
            targets: vec![BlockTarget {
                block: k,
                args: vec![],
            }],
            default: BlockTarget { block: b, args: r },
        },
    );
    return k;
}
