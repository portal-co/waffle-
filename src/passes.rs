//! Passes.

pub mod basic_opt;
pub mod dom_pass;
pub mod empty_blocks;
pub mod maxssa;
pub mod resolve_aliases;
// pub mod ssa;
// pub mod trace;
pub mod mem_fusing;
pub mod unmem;
pub mod reorder_funs;
// pub mod fixup_rets;
pub mod tcore;
pub mod frint;