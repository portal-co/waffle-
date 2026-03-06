//! Simple framework for a domtree-based pass.
use crate::CFGInfo;
use crate::{Block, FunctionBody};
use alloc::vec::Vec;
pub trait DomtreePass {
    fn enter(&mut self, _block: Block, _body: &mut FunctionBody) {}
    fn leave(&mut self, _block: Block, _body: &mut FunctionBody) {}
}
pub fn dom_pass<P: DomtreePass>(body: &mut FunctionBody, cfg: &CFGInfo, pass: &mut P) {
    // Iterative DFS over the dominator tree.
    // Each stack entry is (block, leave): false = call enter then push children,
    // true = call leave.
    let mut stack: Vec<(Block, bool)> = vec![(body.entry, false)];
    while let Some((block, leave)) = stack.pop() {
        if leave {
            pass.leave(block, body);
        } else {
            pass.enter(block, body);
            stack.push((block, true));
            let children: Vec<Block> = cfg.dom_children(block).collect();
            for child in children.into_iter().rev() {
                stack.push((child, false));
            }
        }
    }
}
