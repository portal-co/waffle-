use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{
    cfg::CFGInfo, pool::ListRef, Block, BlockTarget, FrontendOptions, Func, FunctionBody, Memory,
    MemoryArg, Module, Operator, Signature, SignatureData, Terminator, Type, Value, ValueDef, entity::EntityRef,
};

pub fn tweak_value(
    f: &mut FunctionBody,
    ba: &FunctionBody,
    x: &mut ValueDef,
    mut m: impl FnMut(&mut Value),
    b: Block,
) {
    match x {
        ValueDef::BlockParam(a, _, _) => *a = b,
        ValueDef::Operator(o, l, t) => {
            let mut ls = ba.arg_pool[*l].to_vec();
            // eprintln!("l={ls:?};o={o}");
            for v in ls.iter_mut() {
                // eprintln!("l={v}");
                m(v)
            }
            *l = f.arg_pool.from_iter(ls.into_iter());
            *t = f.type_pool.from_iter(ba.type_pool[*t].iter().map(|a|a.clone()));
        }
        ValueDef::PickOutput(v, _, _) => m(v),
        ValueDef::Alias(v) => m(v),
        ValueDef::Placeholder(_) => todo!(),
        ValueDef::Trace(_, l) => {
            let mut ls = ba.arg_pool[*l].to_vec();
            for v in ls.iter_mut() {
                m(v)
            }
            *l = f.arg_pool.from_iter(ls.into_iter());
        }
        ValueDef::None => {}
    }
}
pub fn tweak_target(
    f: &mut FunctionBody,
    x: &mut BlockTarget,
    mut m: impl FnMut(&mut Value),
    mut k: impl FnMut(&mut Block),
) {
    k(&mut x.block);
    for a in &mut x.args {
        m(a)
    }
}
pub fn tweak_terminator(
    f: &mut FunctionBody,
    x: &mut Terminator,
    mut m: impl FnMut(&mut Value),
    mut k: impl FnMut(&mut Block),
) {
    match x {
        Terminator::Br { target } => tweak_target(f, target, m, k),
        Terminator::CondBr {
            cond,
            if_true,
            if_false,
        } => {
            m(cond);
            tweak_target(f, if_true, &mut m, &mut k);
            tweak_target(f, if_false, m, k);
        }
        Terminator::Select {
            value,
            targets,
            default,
        } => {
            m(value);
            for target in targets {
                tweak_target(f, target, &mut m, &mut k)
            }
            tweak_target(f, default, m, k)
        }
        Terminator::Return { values } => {
            for a in values {
                m(a)
            }
        }
        Terminator::Unreachable => {}
        Terminator::None => {}
        Terminator::ReturnCall { func, args } =>             for a in args {
            m(a)
        },
        Terminator::ReturnCallIndirect { sig, table, args } =>             for a in args {
            m(a)
        },
    }
}
pub fn clone_value(
    basis: &FunctionBody,
    f: &mut FunctionBody,
    mut m: impl FnMut(&mut Value),
    v: Value,
    b: Block,
) -> Value {
    let mut w = basis
        .values
        .get(v)
        .map(|b| b.clone())
        .unwrap();
    tweak_value(f,basis, &mut w, m, b);
    return f.add_value(w);
}
pub fn clone_value_in(
    basis: &FunctionBody,
    f: &mut FunctionBody,
    m: &mut HashMap<Value, Value>,
    v: &mut Value,
    b: Block,
    o: Block,
    depth: usize,
) -> Value {
    if depth == 0 {
        let mut p = String::new();
        if let ValueDef::Operator(a, b, c) = basis.values[*v] {
            p = format!("{p};params={:?}", &basis.arg_pool[b])
        }
        panic!("exceeded depth: {} ({:?} {p})", *v, basis.values[*v]);
    }
    let n = f.add_value(ValueDef::None);
    // if let ValueDef::BlockParam(_, p, _) = basis.values[*v]{
    //     *v = f.blocks[b].params[p as usize].1;
    //     return *v;
    // }
    // loop {
    if let Some(n) = m.get(&*v) {
        // *v = *n;
        return *v;
    }
    let g = f as *mut FunctionBody;
    // let mut r = vec![];
    let n = clone_value(
        basis,
        f,
        |a| {
            *a = match m.get(&a) {
                None => {
                    // if basis.value_blocks[*a] == Block::invalid() {
                    //     *a = n;
                    //     return;
                    // }
                    // clone_value_in(basis, unsafe { &mut *g }, m, a, b, o, depth - 1);
                    eprintln!("{}", basis.display("", None));
                    eprintln!("{}; {}", o, b);
                    let mut p = format!("block={};m={:?};in={}", basis.value_blocks[*a], m.clone(),*v);
                    if let ValueDef::Operator(a, b, c) = basis.values[*a] {
                        p = format!("{p};params={:?}", &basis.arg_pool[b])
                    }
                    panic!("value not found: {a} ({:?} {p})", basis.values[*a]);
                    // r.push(*a);
                    // *a
                    *a
                }
                Some(b) => b.clone(),
            }
        },
        v.clone(),
        b,
    );
    // eprintln!("{v} => {n}");
    m.insert((*v).clone(), n.clone());
    *v = n;
    f.append_to_block(b, n);
    return n;
    // }
}
pub fn clone_block(
    f: &mut FunctionBody,
    basis: &FunctionBody,
    b: Block,
    new: Block,
    mut k: impl FnMut(&mut Block),
) {
    let mut d = basis.blocks.get(b).unwrap().clone();
    let mut m: HashMap<Value, Value> = HashMap::new();
    let mut c = BTreeSet::new();
    let r = new;
    for (pt, pv) in d.params.iter_mut() {
        let npv = f.add_blockparam(r, *pt);
        m.insert(*pv, npv);
        *pv = npv;
    }
    // eprintln!("insts={:?}",d.insts);
    for v in &mut d.insts {
        if let Some(_) = m.get(v) {
            continue;
        }
        if c.contains(v){
            continue;
        }
        c.insert(*v);
        // eprintln!("b={b},v={v}");
        if basis.value_blocks[*v] != b {
            panic!("inconsistent block value: {}", *v);
        }
        clone_value_in(basis, f, &mut m, v, r, b, 100);
    }
    tweak_terminator(
        f,
        &mut d.terminator,
        |a| {
            *a = match m.get(&a) {
                None => a.clone(),
                Some(b) => b.clone(),
            }
        },
        k,
    );
    // let mut c = f.blocks.get_mut(r).unwrap();
    // for a in d.insts.clone(){
    //     f.append_to_block(r, a);
    // }
    f.set_terminator(r, d.terminator.clone());
}
pub struct FunCloneRes {
    pub all: BTreeMap<Block, Block>,
}
pub fn clone_fn(f: &mut FunctionBody, basis: &FunctionBody) -> FunCloneRes {
    let mut basis = basis.clone();
    // basis.convert_to_max_ssa(None);
    let mut all = BTreeMap::new();
    for k in basis.blocks.entries().map(|a| a.0) {
        all.insert(k, f.add_block());
    }
    for (a, b) in all.clone() {
        clone_block(f, &basis, a, b, |k| *k = *all.get(k).unwrap());
    }
    return FunCloneRes { all };
}
