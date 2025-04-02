use core::mem::take;

use alloc::collections::btree_set::BTreeSet;

use crate::{FunctionBody, Terminator};

pub fn vaccum(f: &mut FunctionBody) {
    let mut work = true;
    while work {
        work = false;
        for k in f.blocks.iter().collect::<BTreeSet<_>>() {
            let mut t = take(&mut f.blocks[k].terminator);
            if let Terminator::Br { target } = &t {
                if let Terminator::UB = f.blocks[target.block].terminator {
                    t = Terminator::UB;
                    work = true;
                }
            }
            if let Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } = &t
            {
                if let Terminator::UB = f.blocks[if_true.block].terminator {
                    t = Terminator::Br {
                        target: if_false.clone(),
                    };
                    work = true;
                    continue;
                }
                if let Terminator::UB = f.blocks[if_false.block].terminator {
                    t = Terminator::Br {
                        target: if_true.clone(),
                    };
                    work = true;
                    continue;
                }
            }
            f.set_terminator(k, t);
        }
    }
}
