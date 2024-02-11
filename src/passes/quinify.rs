use std::{iter::empty, collections::BTreeMap};

use crate::{
    more::{add_start, new_sig}, wasmparser::types::KebabStr, Block, ExportKind, Func, FuncDecl, FunctionBody, Import, ImportKind, Memory, MemoryArg, MemoryData, Module, Operator, Signature, SignatureData, Table, Type, Value, ValueDef
};

pub fn quin_iter(m: &mut Module, x: impl Iterator<Item = (u8)>, q: Func) {
    let null = new_sig(
        m,
        SignatureData {
            params: vec![],
            returns: vec![],
        },
    );
    let mut b = FunctionBody::new(m, null);
    let vz = b.arg_pool.from_iter(empty());
    let tz = b.type_pool.from_iter(empty());
    let ti = b.type_pool.from_iter(vec![Type::I32].into_iter());
    let ia = b.add_value(ValueDef::Operator(Operator::I32Const { value: 0 }, vz, ti));
    b.append_to_block(b.entry, ia);
    for c in x {
        // let ia = b.add_value(ValueDef::Operator(Operator::I32Const { value: a as u32 }, vz, ti));
        // b.append_to_block(b.entry, ia);
        let ic = b.add_value(ValueDef::Operator(
            Operator::I32Const { value: c as u32 },
            vz,
            ti,
        ));
        b.append_to_block(b.entry, ic);
        let vs = b.arg_pool.from_iter(vec![ia, ic].into_iter());
        let j = b.add_value(ValueDef::Operator(
            Operator::Call { function_index: q },
            vs,
            tz,
        ));
        b.append_to_block(b.entry, j);
    }
    b.set_terminator(b.entry, crate::Terminator::Return { values: vec![] });
    let f = m.funcs.push(FuncDecl::Body(null, format!("z"), b));
    add_start(m, f);
}
pub fn metaquin_iter(m: &mut Module, x: &[(u8)], q: Func){
    for w in x.chunks(4096){
        quin_iter(m, w.iter().map(|a|*a), q);
    }
}