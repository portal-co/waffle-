use std::collections::{BTreeMap, HashMap};

use crate::{
    more::new_sig,
    op_traits::{op_inputs, op_outputs},
    Func, FunctionBody, Module, Operator, SignatureData, ValueDef,
};

pub fn splice_op(m: &mut Module, x: Operator) -> anyhow::Result<Func> {
    let ins = op_inputs(&m, None, &x)?;
    let outs = op_outputs(&m, None, &x)?;
    let sig = SignatureData {
        params: ins.to_vec(),
        returns: outs.to_vec(),
    };
    let sig = new_sig(m, sig);
    let mut body = FunctionBody::new(&m, sig);
    match x {
        Operator::Call { function_index } => body.set_terminator(
            body.entry,
            crate::Terminator::ReturnCall {
                func: function_index,
                args: body.blocks[body.entry].params.iter().map(|a| a.1).collect(),
            },
        ),
        Operator::CallIndirect {
            sig_index,
            table_index,
        } => body.set_terminator(
            body.entry,
            crate::Terminator::ReturnCallIndirect {
                sig: sig_index,
                table: table_index,
                args: body.blocks[body.entry].params.iter().map(|a| a.1).collect(),
            },
        ),
        _ => {
            let vs = body
                .arg_pool
                .from_iter(body.blocks[body.entry].params.iter().map(|a| a.1));
            let ts = body.type_pool.from_iter(outs.iter().map(|a| *a));
            let a = body.add_value(crate::ValueDef::Operator(x, vs, ts));
            let mut b = vec![a];
            if let Some(r) = crate::more::results_ref(m, &mut body, a) {
                b = r
            }
            body.set_terminator(body.entry, crate::Terminator::Return { values: b });
            body.append_to_block(body.entry, a);
        }
    }
    return Ok(m
        .funcs
        .push(crate::FuncDecl::Body(sig, x.to_string(), body)));
}
pub type SpliceCache = HashMap<Operator, Func>;
pub fn splice_func(
    m: &mut Module,
    f: &mut FunctionBody,
    k: &mut SpliceCache,
) -> anyhow::Result<()> {
    for v in f.values.values_mut() {
        let ValueDef::Operator(o, _, _) = v else {
            continue;
        };
        if let Operator::Select = o {
            continue;
        }
        if crate::op_traits::op_rematerialize(o){
            continue;
        }
        if let Operator::Call { function_index } = o{
            continue;
        }
        let f = k.get(&*o);
        let f = match f {
            Some(f) => *f,
            None => {
                let s = splice_op(m, o.clone())?;
                k.insert(o.clone(), s);
                s
            }
        };
        *o = Operator::Call { function_index: f };
    }
    return Ok(());
}
pub fn splice_module(m: &mut Module) -> anyhow::Result<()> {
    let mut b = BTreeMap::new();
    let mut cache = SpliceCache::new();
    for (f, d) in m.funcs.entries() {
        if let Some(d) = d.body() {
            let d = d.clone();
            b.insert(f, d);
        }
    }
    //let c = b.clone();
    for (k, v) in b.iter_mut() {
        splice_func(m, v, &mut cache)?;
    }
    for (k, v) in b {
        *m.funcs[k].body_mut().unwrap() = v;
    }
    return Ok(());
}
