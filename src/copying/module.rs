use crate::op_traits::rewrite_mem;
use crate::util::{add_start, new_sig};
use paste::paste;
use std::mem::{replace, take};
use std::{
    backtrace,
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, HashMap},
    hash::Hash,
    iter::empty,
    ops::{Deref, DerefMut},
};
pub fn x2i(x: ExportKind) -> ImportKind {
    match x {
        ExportKind::Table(a) => ImportKind::Table(a),
        ExportKind::Func(a) => ImportKind::Func(a),
        ExportKind::Global(a) => ImportKind::Global(a),
        ExportKind::Memory(a) => ImportKind::Memory(a),
    }
}
pub fn i2x(x: ImportKind) -> ExportKind {
    match x {
        ImportKind::Table(a) => ExportKind::Table(a),
        ImportKind::Func(a) => ExportKind::Func(a),
        ImportKind::Global(a) => ExportKind::Global(a),
        ImportKind::Memory(a) => ExportKind::Memory(a),
    }
}
use crate::{
    entity::EntityRef, ExportKind, Func, FuncDecl, FunctionBody, Global, ImportKind, Memory,
    Module, Operator, Signature, SignatureData, Table, TableData, Type, ValueDef,
};
#[derive(Eq, PartialEq, Clone)]
pub struct IKW(pub ImportKind);
impl Hash for IKW {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.0 {
            ImportKind::Table(a) => {
                state.write_usize(0);
                a.hash(state);
            }
            ImportKind::Func(a) => {
                state.write_usize(1);
                a.hash(state);
            }
            ImportKind::Global(a) => {
                state.write_usize(2);
                a.hash(state);
            }
            ImportKind::Memory(a) => {
                state.write_usize(3);
                a.hash(state);
            }
        }
    }
}

pub struct State<I> {
    cache: HashMap<IKW, ImportKind>,
    fun_cache: BTreeMap<Func, Func>,
    table_cache: BTreeMap<Table, Table>,
    pub importmap: I,
    pub tables: BTreeSet<Table>,
}
impl<I> State<I> {
    pub fn new(importmap: I, tables: BTreeSet<Table>) -> Self {
        return Self {
            importmap,
            cache: Default::default(),
            fun_cache: Default::default(),
            table_cache: Default::default(),
            tables,
        };
    }
}
pub struct Copier<A, B, S> {
    pub src: A,
    pub dest: B,
    pub state: S,
}
macro_rules! translator {
    ($a:tt) => {
        paste! {
            pub fn [<translate_ $a>](&mut self, m: $a) -> anyhow::Result<$a>{
                let ImportKind::$a(n) = self.translate_import(ImportKind::$a(m))? else{
                    anyhow::bail!("not the right item")
                };
                return Ok(n);
            }
        }
    };
}
pub fn tree_shake(m: &mut Module) -> anyhow::Result<()> {
    let n = replace(m, Module::empty());
    let mut s = Copier::new(
        &n,
        m,
        Box::new(State::new(
            Box::new(import_fn(|_, m, n| {
                Ok(Some(ImportBehavior::Passthrough(m, n)))
            })),
            BTreeSet::new(),
        )),
    );
    for x in n.exports.iter() {
        let i = x2i(x.kind.clone());
        let i = s.translate_import(i)?;
        let mut x = x.clone();
        x.kind = i2x(i);
        s.dest.exports.push(x);
    }
    Ok(())
}
pub trait Imports {
    fn get_import(
        &mut self,
        a: &mut Module<'_>,
        m: String,
        n: String,
    ) -> anyhow::Result<Option<ImportBehavior>>;
}
#[repr(transparent)]
#[derive(Clone, Debug, Copy)]
pub struct ImportFn<F>(pub F);

pub fn import_fn(
    a: impl FnMut(&mut Module<'_>, String, String) -> anyhow::Result<Option<ImportBehavior>>,
) -> impl Imports {
    ImportFn(a)
}

impl<F: FnMut(&mut Module<'_>, String, String) -> anyhow::Result<Option<ImportBehavior>>> Imports
    for ImportFn<F>
{
    fn get_import(
        &mut self,
        a: &mut Module<'_>,
        m: String,
        n: String,
    ) -> anyhow::Result<Option<ImportBehavior>> {
        return (self.0)(a, m, n);
    }
}

pub enum ImportBehavior {
    Bind(ImportKind),
    Passthrough(String, String),
}
impl<
        'a: 'b,
        'b,
        A: Deref<Target = crate::Module<'a>>,
        B: Deref<Target = crate::Module<'b>> + DerefMut,
        S: Deref<Target = State<I>> + DerefMut,
        I: Deref<Target = J> + DerefMut,
        J: Imports + ?Sized,
    > Copier<A, B, S>
{
    // pub fn collect(&mut self) -> anyhow::Result<BTreeMap<String, ExportKind>> {
    //     let e = get_exports(&self.src);
    //     // let mut m = HashMap::new();
    //     let mut m = BTreeMap::new();
    //     for (s, e) in e {
    //         let e = x2i(e);
    //         let r = self.translate_import(e.clone())?;
    //         m.insert(s, i2x(r));
    //     }
    //     return Ok(m);
    // }
    pub fn new(
        src: A,
        dest: B,
        // importmap: BTreeMap<(String, String), ImportKind>,
        cache: S,
    ) -> Self {
        return Self {
            src,
            dest,
            // importmap,
            state: cache,
        };
    }
    pub fn resolve_import(&mut self, a: &ImportKind) -> anyhow::Result<Option<ImportBehavior>> {
        for i in self.src.imports.iter() {
            if i.kind == *a {
                return self.state.importmap.get_import(
                    &mut self.dest,
                    i.module.clone(),
                    i.name.clone(),
                );
            }
        }
        return Ok(None);
    }
    pub fn internal_translate_mem(&mut self, a: crate::Memory) -> anyhow::Result<crate::Memory> {
        let d = self.src.memories[a].clone();
        return Ok(self.dest.memories.push(d));
    }
    pub fn internal_translate_global(&mut self, a: crate::Global) -> anyhow::Result<crate::Global> {
        let d = self.src.globals[a].clone();
        return Ok(self.dest.globals.push(d));
    }
    pub fn translate_import(&mut self, a: ImportKind) -> anyhow::Result<ImportKind> {
        let i = match self.resolve_import(&a)? {
            None => None,
            Some(ImportBehavior::Bind(b)) => return Ok(b),
            Some(ImportBehavior::Passthrough(a, b)) => Some((a, b)),
        };
        if let Some(j) = i.clone() {
            for m in self.dest.imports.iter() {
                if m.module == j.0 && m.name == j.1 {
                    return Ok(m.kind.clone());
                }
            }
        }
        if let Some(b) = self.state.cache.get(&IKW(a.clone())) {
            return Ok(b.clone());
        }
        let c = match a {
            ImportKind::Table(t) => ImportKind::Table(self.internal_translate_table(t)?),
            ImportKind::Func(f) => ImportKind::Func(self.internal_translate_func(f)?),
            ImportKind::Global(g) => ImportKind::Global(self.internal_translate_global(g)?),
            ImportKind::Memory(m) => ImportKind::Memory(self.internal_translate_mem(m)?),
        };
        self.state.cache.insert(IKW(a.clone()), c.clone());
        if let Some(j) = i {
            self.dest.imports.push(crate::Import {
                module: j.0,
                name: j.1,
                kind: c.clone(),
            })
        }
        return Ok(c);
    }
    pub fn internal_translate_table(&mut self, tk: Table) -> anyhow::Result<Table> {
        // if let Some(c) = self.state.table_cache.get(&tk) {
        //     return Ok(*c);
        // }
        let mut t = self.src.tables[tk].clone();
        if let Type::TypedFuncRef { sig_index, .. } = &mut t.ty {
            *sig_index = self.translate_sig(*sig_index)?;
        }
        // let nt = self.dest.tables.push(t.clone());
        // self.state.table_cache.insert(tk, nt);
        if let Some(u) = t.func_elements.as_mut() {
            for w in u.iter_mut() {
                *w = self.translate_Func(*w)?;
            }
        }
        // self.dest.tables[nt] = t;
        return Ok(self.dest.tables.push(t));
    }
    pub fn translate_sig(&mut self, s: Signature) -> anyhow::Result<Signature> {
        let mut d = self.src.signatures[s].clone();
        for x in d.params.iter_mut().chain(d.returns.iter_mut()) {
            if let Type::TypedFuncRef { sig_index, .. } = x {
                *sig_index = self.translate_sig(*sig_index)?;
            }
        }
        return Ok(new_sig(&mut *self.dest, d));
    }
    pub fn internal_translate_func(&mut self, f: Func) -> anyhow::Result<Func> {
        if f == Func::invalid() {
            return Ok(f);
        }
        if let Some(x) = self.state.fun_cache.get(&f) {
            return Ok(*x);
        }
        let a = self.dest.funcs.push(crate::FuncDecl::None);
        self.state.fun_cache.insert(f, a);
        for t in &self.state.tables {
            self.dest.tables[*t]
                .func_elements
                .get_or_insert(vec![])
                .push(a);
        }
        if Some(f) == self.src.start_func {
            add_start(&mut self.dest, a);
        }
        let mut f = self.src.funcs[f].clone();
        if let Some(b) = f.body_mut() {
            for v in b.values.iter() {
                let mut k = b.values[v].clone();
                if let ValueDef::BlockParam(_, _, x) = &mut k {
                    if let Type::TypedFuncRef { sig_index, .. } = x {
                        *sig_index = self.translate_sig(*sig_index)?;
                    }
                }
                if let ValueDef::PickOutput(_, _, x) = &mut k {
                    if let Type::TypedFuncRef { sig_index, .. } = x {
                        *sig_index = self.translate_sig(*sig_index)?;
                    }
                }
                if let ValueDef::Operator(a, vs, c) = &mut k {
                    let mut w = b.arg_pool[*vs].to_vec();
                    let mut e = None;
                    rewrite_mem(a, &mut w, |m, _| {
                        *m = self.translate_Memory(*m)?;
                        Ok::<_, anyhow::Error>(())
                    })?;
                    if let Some(e) = e {
                        return Err(e);
                    }
                    match a {
                        crate::Operator::Call { function_index } => {
                            *function_index = self.translate_Func(*function_index)?;
                        }
                        crate::Operator::RefFunc { func_index } => {
                            *func_index = self.translate_Func(*func_index)?;
                        }
                        crate::Operator::RefNull { ty } => {
                            if let Type::TypedFuncRef { sig_index, .. } = ty {
                                *sig_index = self.translate_sig(*sig_index)?;
                            }
                        }
                        crate::Operator::TypedSelect { ty } => {
                            if let Type::TypedFuncRef { sig_index, .. } = ty {
                                *sig_index = self.translate_sig(*sig_index)?;
                            }
                        }
                        Operator::CallRef { sig_index } => {
                            *sig_index = self.translate_sig(*sig_index)?;
                        }
                        crate::Operator::CallIndirect {
                            sig_index,
                            table_index,
                        } => {
                            *sig_index = self.translate_sig(*sig_index)?;
                            *table_index = self.translate_Table(*table_index)?;
                        }
                        crate::Operator::GlobalGet { global_index } => {
                            *global_index = self.translate_Global(*global_index)?;
                        }
                        crate::Operator::GlobalSet { global_index } => {
                            *global_index = self.translate_Global(*global_index)?;
                        }
                        crate::Operator::TableGet { table_index } => {
                            *table_index = self.translate_Table(*table_index)?;
                        }
                        crate::Operator::TableSet { table_index } => {
                            *table_index = self.translate_Table(*table_index)?;
                        }
                        crate::Operator::TableGrow { table_index } => {
                            *table_index = self.translate_Table(*table_index)?;
                        }
                        crate::Operator::TableSize { table_index } => {
                            *table_index = self.translate_Table(*table_index)?;
                        }
                        _ => {}
                    }
                    *vs = b.arg_pool.from_iter(w.into_iter());
                }
                b.values[v] = k;
            }
            for k in b.blocks.iter() {
                let mut kv = b.blocks[k].clone();
                match &mut kv.terminator {
                    crate::Terminator::ReturnCall { func, args } => {
                        *func = self.translate_Func(*func)?;
                    }
                    crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                        *sig = self.translate_sig(*sig)?;
                        *table = self.translate_Table(*table)?;
                    }
                    crate::Terminator::ReturnCallRef { sig, args } => {
                        *sig = self.translate_sig(*sig)?;
                        // *table = self.translate_Table(*table)?;
                    }
                    _ => {}
                }
                b.blocks[k] = kv;
            }
            for x in b.type_pool.storage.iter_mut() {
                if let Type::TypedFuncRef { sig_index, .. } = x {
                    *sig_index = self.translate_sig(*sig_index)?;
                }
            }
            // (self.state.instrument)(&mut self.dest,b)?;
        }
        match &mut f {
            crate::FuncDecl::Import(a, _) => {
                *a = self.translate_sig(*a)?;
            }
            crate::FuncDecl::Lazy(_, _, _) => todo!(),
            crate::FuncDecl::Body(a, _, _) => {
                *a = self.translate_sig(*a)?;
            }
            crate::FuncDecl::Compiled(_, _, _) => todo!(),
            crate::FuncDecl::None => {}
        }
        self.dest.funcs[a] = f;
        return Ok(a);
    }
    translator!(Memory);
    translator!(Table);
    translator!(Global);
    translator!(Func);
}

#[cfg(test)]
mod tests {
    use super::*;
}
