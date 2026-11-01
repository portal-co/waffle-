//! Treeification: placing some values "under" others if only used
//! once, to generate more AST-like Wasm code.
use crate::EntityRef;
use crate::{Block, FunctionBody, Value, ValueDef};
use crate::Operator;
use alloc::vec;
use alloc::vec::Vec;
use core::convert::TryFrom;
use crate::backend::{DeterministicMap as HashMap, DeterministicSet as HashSet};
/// One "argument slot" of an operator defining a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueArg(Value, u16);
#[derive(Clone, Debug)]
pub struct Trees {
    /// Is a value placed "under" the given arg slot of the given
    /// other value?
    pub owner: HashMap<Value, ValueArg>,
    /// For a given value that is defined by an operator, which
    /// Values, if any, live at each slot?
    pub owned: HashMap<ValueArg, Value>,
    /// Values that are regenerated every time they are used.
    pub remat: HashSet<Value>,
}
fn is_remat(op: &Operator) -> bool {
    // Only ops with no args can be always-rematerialized.
    match op {
        Operator::I32Const { .. }
        | Operator::I64Const { .. }
        | Operator::F32Const { .. }
        | Operator::F64Const { .. } => true,
        _ => false,
    }
}
impl Trees {
    pub fn compute(body: &FunctionBody) -> Trees {
        let mut owner = HashMap::default();
        let mut owned = HashMap::default();
        let mut remat = HashSet::default();
        let mut multi_use: HashSet<Value> = HashSet::default();
        // A treeified ("owned") value is re-emitted as a nested
        // sub-expression directly at its single use site, relying on the
        // Wasm value stack to carry it there instead of a local. That is
        // only sound when the use site is in the *same block* as the
        // definition: the value stack doesn't survive a branch, so
        // ownership across a block boundary would either silently move a
        // side-effecting computation (e.g. a call) to a different point in
        // the control-flow graph than the source program placed it, or
        // reference operands that were never computed on that path at
        // all. Record each value's defining block up front so the
        // ownership checks below can require same-block placement.
        let mut def_block: HashMap<Value, Block> = HashMap::default();
        // IR position (a global counter over blocks in order) for each
        // value, so the *latest* side effect inside an owned tree can be
        // found by comparison.
        let mut position: HashMap<Value, u32> = HashMap::default();
        let mut next_position: u32 = 0;
        for (block_id, block_def) in body.blocks.entries() {
            for &(_, param) in &block_def.params {
                def_block.insert(param, block_id);
                position.insert(param, next_position);
                next_position += 1;
            }
            for inst in &block_def.insts {
                def_block.insert(inst.value, block_id);
                position.insert(inst.value, next_position);
                next_position += 1;
            }
        }
        // For each value, the latest (by IR position) side-effecting op
        // inside the owned tree rooted at that value, or no entry if that
        // tree is entirely pure. An owned value is re-emitted at its
        // owner's position, so every side effect in its tree moves with
        // it; tracking only the op's own purity (the old `is_movable`
        // check) let a pure wrapper (e.g. an arithmetic op) carry a call
        // in its subtree past another call, reordering side effects.
        let mut tree_last_non_pure: HashMap<Value, Value> = HashMap::default();
        for (block_id, block_def) in body.blocks.entries() {
            let mut last_non_pure = None;
            for value in &block_def.insts {
                match &body.values[value.value] {
                    &ValueDef::Operator(op, args, _) => {
                        // Ignore operators with invalid args: these must
                        // always be unreachable.
                        if body.arg_pool[args].iter().any(|arg| arg.is_invalid()) {
                            continue;
                        }
                        // If this is an always-rematerialized operator,
                        // mark it as such and continue.
                        if is_remat(&op) {
                            remat.insert(value.value);
                            continue;
                        }
                        // For each of the args, if the value is produced
                        // by a single-output op and is movable, and is
                        // not already recorded in `multi_use`, place it
                        // in the arg slot. Otherwise if owned already
                        // somewhere else, undo that and put in
                        // `multi_use`.
                        for (i, &arg) in body.arg_pool[args].iter().enumerate() {
                            let arg = body.resolve_alias(arg);
                            let same_block = def_block.get(&arg) == Some(&block_id);
                            if multi_use.contains(&arg) {
                                continue;
                            } else if let Some(old_owner) = owner.remove(&arg) {
                                owned.remove(&old_owner);
                                multi_use.insert(arg);
                            } else if same_block
                                && match tree_last_non_pure.get(&arg) {
                                    // No side effects in the arg's owned
                                    // subtree: freely movable iff the arg
                                    // itself is pure.
                                    None => Self::is_movable(body, arg),
                                    // The arg's tree has side effects:
                                    // absorb it only when its latest side
                                    // effect is the most recent one before
                                    // this op, so absorbing it cannot move
                                    // it past any other side effect.
                                    Some(tail) => Some(*tail) == last_non_pure,
                                }
                            {
                                let pos = u16::try_from(i).unwrap();
                                let value_arg = ValueArg(value.value, pos);
                                owner.insert(arg, value_arg);
                                owned.insert(value_arg, arg);
                            }
                        }
                        let tail = if !op.is_pure() {
                            last_non_pure = Some(value.value);
                            Some(value.value)
                        } else {
                            // A pure op's tree tail is the latest tail of
                            // the args this op just absorbed (an unowned
                            // arg emits at its own position, outside this
                            // tree, so it does not count).
                            body.arg_pool[args]
                                .iter()
                                .filter_map(|&arg| {
                                    let arg = body.resolve_alias(arg);
                                    match owner.get(&arg) {
                                        Some(&ValueArg(owner_value, _))
                                            if owner_value == value.value =>
                                        {
                                            tree_last_non_pure.get(&arg).copied()
                                        }
                                        _ => None,
                                    }
                                })
                                .max_by_key(|tail| position[tail])
                        };
                        if let Some(tail) = tail {
                            tree_last_non_pure.insert(value.value, tail);
                        }
                    }
                    &ValueDef::PickOutput(..) => {
                        // Can ignore use: multi-arity values are never treeified.
                    }
                    &ValueDef::BlockParam(..)
                    | &ValueDef::Alias(..)
                    | &ValueDef::Placeholder(..)
                    | &ValueDef::None => {}
                }
            }
        }
        for block in body.blocks.values() {
            block.terminator.visit_uses(|u| {
                let u = body.resolve_alias(u);
                if let Some(old_owner) = owner.remove(&u) {
                    owned.remove(&old_owner);
                }
            });
        }
        Trees {
            owner,
            owned,
            remat,
        }
    }
    fn is_single_output_op(body: &FunctionBody, value: Value) -> Option<Operator> {
        match &body.values[value] {
            &ValueDef::Operator(op, _, ref tys) if tys.len() == 1 => Some(op),
            _ => None,
        }
    }
    fn is_movable(body: &FunctionBody, value: Value) -> bool {
        Self::is_single_output_op(body, value)
            .map(|op| op.is_pure())
            .unwrap_or(false)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{FuncDecl, Module, ModuleExt, Operator, SignatureData, Terminator, Type};
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::vec::Vec;

    /// Regression test: a pure operator whose single use is separated from
    /// its definition by another side effect must not be treeified when its
    /// owned subtree itself contains a side effect. Otherwise the subtree's
    /// side effect is re-emitted at the pure op's (later) root position,
    /// reordering calls: `c1*100 + c2*10 + c3` evaluated the calls in the
    /// order c3, c1, c2 (jsaw#16).
    #[test]
    fn treeify_does_not_reorder_side_effects_across_pure_ops() {
        let mut module = Module::empty();
        // bump: () -> f64, increments a mutable global and returns it.
        let bump_sig = module.signatures.push(SignatureData::Func {
            params: vec![],
            returns: vec![Type::F64],
            shared: false,
        });
        // ident: (f64) -> f64 (identity, kept opaque so its call is a side
        // effect boundary).
        let ident_sig = module.signatures.push(SignatureData::Func {
            params: vec![Type::F64],
            returns: vec![Type::F64],
            shared: false,
        });
        // main: () -> f64.
        let main_sig = module.signatures.push(SignatureData::Func {
            params: vec![],
            returns: vec![Type::F64],
            shared: false,
        });
        let global = module.globals.push(crate::GlobalData {
            ty: Type::F64,
            value: Some(0),
            mutable: true,
        });

        let bump = module
            .funcs
            .push(FuncDecl::Body(bump_sig, "bump".to_string(), {
                let mut body = FunctionBody::new(&module, bump_sig);
                let entry = body.entry;
                let g = body.add_op(entry, Operator::GlobalGet { global_index: global }, &[], &[Type::F64]);
                let one = body.add_op(entry, Operator::F64Const { value: 1.0f64.to_bits() }, &[], &[Type::F64]);
                let next = body.add_op(entry, Operator::F64Add, &[g, one], &[Type::F64]);
                body.add_op(entry, Operator::GlobalSet { global_index: global }, &[next], &[]);
                body.set_terminator(entry, Terminator::Return { values: vec![next] });
                body
            }));
        let ident = module
            .funcs
            .push(FuncDecl::Body(ident_sig, "ident".to_string(), {
                let mut body = FunctionBody::new(&module, ident_sig);
                let entry = body.entry;
                let arg = body.blocks[entry].params[0].1;
                body.set_terminator(entry, Terminator::Return { values: vec![arg] });
                body
            }));

        // main: a = bump()*100 + bump()*10; w1 = ident(a); c3 = bump();
        // w2 = ident(c3); return w1 + w2.
        let main = module
            .funcs
            .push(FuncDecl::Body(main_sig, "main".to_string(), {
                let mut body = FunctionBody::new(&module, main_sig);
                let entry = body.entry;
                let c1 = body.add_op(entry, Operator::Call { function_index: bump }, &[], &[Type::F64]);
                let k100 = body.add_op(entry, Operator::F64Const { value: 100.0f64.to_bits() }, &[], &[Type::F64]);
                let m1 = body.add_op(entry, Operator::F64Mul, &[c1, k100], &[Type::F64]);
                let c2 = body.add_op(entry, Operator::Call { function_index: bump }, &[], &[Type::F64]);
                let k10 = body.add_op(entry, Operator::F64Const { value: 10.0f64.to_bits() }, &[], &[Type::F64]);
                let m2 = body.add_op(entry, Operator::F64Mul, &[c2, k10], &[Type::F64]);
                let a = body.add_op(entry, Operator::F64Add, &[m1, m2], &[Type::F64]);
                let c3 = body.add_op(entry, Operator::Call { function_index: bump }, &[], &[Type::F64]);
                // The tree root for the `a` chain sits *after* `c3`: under
                // the bug, `a` (pure) is absorbed into `x` carrying `c1` and
                // `c2` with it, while `c3` stays a root at its own earlier
                // position — so `c3` runs first.
                let x = body.add_op(entry, Operator::Call { function_index: ident }, &[a], &[Type::F64]);
                let y = body.add_op(entry, Operator::Call { function_index: ident }, &[c3], &[Type::F64]);
                let r = body.add_op(entry, Operator::F64Add, &[x, y], &[Type::F64]);
                body.set_terminator(entry, Terminator::Return { values: vec![r] });
                body
            }));
        module.exports.push(crate::Export {
            name: "main".to_string(),
            kind: crate::ExportKind::Func(main),
        });
        let _ = (bump, ident);

        let bytes = module.to_wasm_bytes().expect("encodes");
        let engine = wasmtime::Engine::default();
        let compiled = wasmtime::Module::new(&engine, &bytes).expect("validates");
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &compiled, &[]).expect("instantiates");
        let main_fn = instance
            .get_typed_func::<(), f64>(&mut store, "main")
            .expect("main export");
        // Correct left-to-right evaluation: bump() -> 1, 2, 3, so
        // (1*100 + 2*10) + 3 = 123.
        assert_eq!(main_fn.call(&mut store, ()).expect("runs"), 123.0);
    }
}
