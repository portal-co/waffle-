use crate::*;
pub fn add_start(m: &mut Module, tf: Func) {
    let s = SignatureData::Func {
        params: vec![],
        returns: vec![],
    };
    let s = new_sig(m, s);
    let mut f = FunctionBody::new(&m, s);
    let vz = f.arg_pool.from_iter(std::iter::empty());
    let t = m.funcs[tf].sig();
    let SignatureData::Func { params, returns } = m.signatures[t].clone() else{
        todo!()
    };
    let t = returns;
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
            Some(a) => Terminator::ReturnCall {
                func: a,
                args: vec![],
            },
            None => Terminator::Return { values: vec![] },
        },
    );
    let f = m.funcs.push(FuncDecl::Body(s, format!("start"), f));
    m.start_func = Some(f);
}
pub fn new_sig(m: &mut Module, s: SignatureData) -> Signature {
    for (a, b) in m.signatures.entries() {
        if *b == s {
            return a;
        }
    }
    return m.signatures.push(s);
}