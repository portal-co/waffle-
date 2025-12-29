use super::inline::{inline_mod, InlineCfg};
use crate::{CFGInfo, FunctionBody, Module, Terminator};
use alloc::collections::btree_set::BTreeSet;
use core::mem::take;
pub fn vaccum(f: &mut FunctionBody) {
    let mut work = true;
    while work {
        work = false;
        for k in f.blocks.iter().collect::<BTreeSet<_>>() {
            let mut t = take(&mut f.blocks[k].terminator);
            if let Terminator::Br { target } = &t.terminator {
                if let Terminator::UB = f.blocks[target.block].terminator.terminator {
                    t.terminator = Terminator::UB;
                    work = true;
                }
            }
            if let Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } = &t.terminator
            {
                if let Terminator::UB = f.blocks[if_true.block].terminator.terminator {
                    t.terminator = Terminator::Br {
                        target: if_false.clone(),
                    };
                    f.set_terminator(k, t.terminator);
                    work = true;
                    continue;
                }
                if let Terminator::UB = f.blocks[if_false.block].terminator.terminator {
                    t.terminator = Terminator::Br {
                        target: if_true.clone(),
                    };
                    f.set_terminator(k, t.terminator);
                    work = true;
                    continue;
                }
            }
            f.set_terminator(k, t.terminator);
        }
    }
}
pub fn gvc(m: &mut Module) -> anyhow::Result<()> {
    let mut work = true;
    let mut save = BTreeSet::new();
    while work {
        work = false;
        for f in m.funcs.iter().collect::<BTreeSet<_>>() {
            let mut b = take(&mut m.funcs[f]);
            'a: {
                if let Some(b) = b.body_mut() {
                    if let Terminator::UB = b.blocks[b.entry].terminator.terminator {
                        break 'a;
                    }
                    vaccum(b);
                    // Optimize
                    let b_cfg = CFGInfo::new(b);
                    crate::passes::basic_opt::basic_opt(b, &b_cfg, &Default::default());
                    crate::passes::empty_blocks::run(b);
                    if let Terminator::UB = b.blocks[b.entry].terminator.terminator {
                        save.insert(f);
                        // if !save.insert(f){
                        work = true
                        // }
                    }
                }
            }
            m.funcs[f] = b;
        }
        inline_mod(
            m,
            InlineCfg {
                funcs: save.clone(),
            },
        )?;
    }
    Ok(())
}
