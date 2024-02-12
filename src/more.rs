use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    ops::{Deref, DerefMut},
};

use env_logger::Target;

use crate::{
    cfg::CFGInfo, pool::ListRef, Block, BlockTarget, ExportKind, Func, FunctionBody, ImportKind,
    Memory, MemoryArg, Module, Operator, Signature, SignatureData, Table, Terminator, Type, Value,
    ValueDef,
};
pub struct Flix<T> {
    pub mo: T,
    pub fun: crate::Func,
}
impl<T: Deref<Target = crate::Module<'static>>> Deref for Flix<T> {
    type Target = crate::FunctionBody;

    fn deref(&self) -> &Self::Target {
        return self.mo.funcs[self.fun].body().unwrap();
    }
}
impl<T: Deref<Target = crate::Module<'static>> + DerefMut> DerefMut for Flix<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        return self.mo.funcs[self.fun].body_mut().unwrap();
    }
    // type Target = crate::FunctionBody;
}

pub fn new_sig(m: &mut Module, s: SignatureData) -> Signature {
    for (a, b) in m.signatures.entries() {
        if *b == s {
            return a;
        }
    }
    return m.signatures.push(s);
}
// pub fn results<T: Deref<Target = Module<'static>> + DerefMut>(f: &mut Flix<T>, c: Value) -> Option<Vec<Value>>{
//     let c = f.resolve_and_update_alias(c);
//     let b = f.value_blocks[c];
//     let ValueDef::Operator(Operator::Call { function_index }, _1, _2) = f.values[c] else{
//         return None;
//     };
//     let mut v = vec![];
//     let s = f.mo.funcs[function_index].sig();
//     for (s,i) in f.mo.signatures[s].returns.clone().into_iter().enumerate(){
//         let w = f.add_value(ValueDef::PickOutput(c, s as u32, i));
//         f.append_to_block(b, w);
//         v.push(w);
//     };

//     return Some(v);
// }
pub fn results_ref(m: &mut Module, f: &mut FunctionBody, c: Value) -> Option<Vec<Value>> {
    let c = f.resolve_and_update_alias(c);
    let b = f.value_blocks[c];
    let mut v = vec![];
    let s = match f.values[c] {
        ValueDef::Operator(Operator::Call { function_index }, _1, _2) => {
            m.funcs[function_index].sig()
        }
        ValueDef::Operator(
            Operator::CallIndirect {
                sig_index,
                table_index,
            },
            _1,
            _2,
        ) => sig_index,
        _ => return None,
    };
    for (s, i) in m.signatures[s].returns.clone().into_iter().enumerate() {
        let w = f.add_value(ValueDef::PickOutput(c, s as u32, i));
        f.append_to_block(b, w);
        v.push(w);
    }

    return Some(v);
}

pub fn rewrite_mem<V>(
    o: &mut Operator,
    v: &mut [V],
    mut go: impl FnMut(&mut Memory, Option<&mut V>),
) {
    match o {
        Operator::I32Load { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::F32Load { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::F64Load { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Load8S { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Load8U { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Load16S { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Load16U { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load8S { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load8U { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load16S { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load16U { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load32S { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Load32U { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Store { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Store { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::F32Store { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::F64Store { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Store8 { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I32Store16 { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Store8 { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Store16 { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::I64Store32 { memory } => go(&mut memory.memory, Some(&mut v[0])),
        Operator::MemorySize { mem } => go(mem, None),
        Operator::MemoryGrow { mem } => go(mem, None),
        Operator::MemoryCopy { dst_mem, src_mem } => {
            go(dst_mem, Some(&mut v[0]));
            go(src_mem, Some(&mut v[1]));
        }
        Operator::MemoryFill { mem } => go(mem, Some(&mut v[0])),

        _ => {}
    }
}
pub fn mem_count(o: &Operator) -> usize {
    match o {
        Operator::I32Load { memory } => 1,
        Operator::I64Load { memory } => 1,
        Operator::F32Load { memory } => 1,
        Operator::F64Load { memory } => 1,
        Operator::I32Load8S { memory } => 1,
        Operator::I32Load8U { memory } => 1,
        Operator::I32Load16S { memory } => 1,
        Operator::I32Load16U { memory } => 1,
        Operator::I64Load8S { memory } => 1,
        Operator::I64Load8U { memory } => 1,
        Operator::I64Load16S { memory } => 1,
        Operator::I64Load16U { memory } => 1,
        Operator::I64Load32S { memory } => 1,
        Operator::I64Load32U { memory } => 1,
        Operator::I32Store { memory } => 1,
        Operator::I64Store { memory } => 1,
        Operator::F32Store { memory } => 1,
        Operator::F64Store { memory } => 1,
        Operator::I32Store8 { memory } => 1,
        Operator::I32Store16 { memory } => 1,
        Operator::I64Store8 { memory } => 1,
        Operator::I64Store16 { memory } => 1,
        Operator::I64Store32 { memory } => 1,
        Operator::MemorySize { mem } => 1,
        Operator::MemoryGrow { mem } => 1,
        Operator::MemoryCopy { dst_mem, src_mem } => 2,
        Operator::MemoryFill { mem } => 1,

        _ => 0,
    }
}
pub fn append_before(f: &mut FunctionBody, v: Value, before: Value, block: Block) {
    f.append_to_block(block, v);
    let t = std::mem::take(&mut f.blocks[block].insts);
    for t in t {
        if t != v {
            if t == before {
                f.blocks[block].insts.push(v)
            }
            f.blocks[block].insts.push(t)
        }
    }
}
pub fn append_to_table(m: &mut Module, t: Table, f: Func) -> usize {
    let s = m.tables[t].func_elements.as_mut().unwrap();
    for (i, x) in s.iter().enumerate() {
        if *x == f {
            return i;
        }
    }
    let l = s.len();
    s.push(f);
    return l;
}
pub fn x2i(x: ExportKind) -> ImportKind {
    match x {
        crate::ExportKind::Table(t) => ImportKind::Table(t),
        crate::ExportKind::Func(f) => ImportKind::Func(f),
        crate::ExportKind::Global(g) => ImportKind::Global(g),
        crate::ExportKind::Memory(m) => ImportKind::Memory(m),
    }
}

pub fn add_start(m: &mut Module, tf: Func) {
    let s = SignatureData {
        params: vec![],
        returns: vec![],
    };
    let s = new_sig(m, s);
    let mut f = FunctionBody::new(&m, s);
    let vz = f.arg_pool.from_iter(std::iter::empty());
    let t = m.funcs[tf].sig();
    let t = m.signatures[t].clone().returns;
    let tz = f.type_pool.from_iter(t.into_iter());
    let v = f.add_value(ValueDef::Operator(
        Operator::Call { function_index: tf },
        vz,
        tz,
    ));
    f.append_to_block(f.entry, v);
    f.set_terminator(
        f.entry,
        match m.start_func {
            Some(a) => crate::Terminator::ReturnCall {
                func: a,
                args: vec![],
            },
            None => crate::Terminator::Return { values: vec![] },
        },
    );
    let f = m.funcs.push(crate::FuncDecl::Body(s, format!("start"), f));
    m.start_func = Some(f);
}
