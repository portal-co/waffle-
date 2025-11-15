//! Passes.
pub mod basic_opt;
pub mod dom_pass;
pub mod empty_blocks;
// pub mod ssa;
// pub mod trace;
pub mod mem_fusing;
pub mod reorder_funs;
pub mod unmem;
// pub mod fixup_rets;
pub mod frint;
#[cfg(feature = "importify")]
pub mod importify;
pub mod inline;

pub mod ub_vaccum;
