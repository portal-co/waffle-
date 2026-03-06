use alloc::collections::btree_set::BTreeSet;
use waffle_ir::{Func, FunctionBody, Operator, ValueDef};

pub fn func_rocket(f: &mut FunctionBody, map: &[(Func, Func)]) {
    'a: loop {
        for v in f.values.iter().collect::<BTreeSet<_>>() {
            if let ValueDef::Operator(Operator::Call { function_index }, args, tys) = &f.values[v] {
                for to in map.iter().filter_map(|(from, to)| {
                    if from == function_index {
                        Some(*to)
                    } else {
                        None
                    }
                }) {
                    let args = &f.arg_pool[*args];
                    if let ValueDef::Operator(Operator::Call { function_index, .. }, args2, _) =
                        &f.values[args[0]]
                    {
                        if *function_index == to {
                            let args2 = &f.arg_pool[*args2];
                            f.values[v] = ValueDef::Alias(args2[0]);
                            continue 'a;
                        }
                    }
                }
            }
        }
        return;
    }
}
