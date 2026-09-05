//! Characterization coverage for the 0.2 CFG/SSA adapter on frontend-produced IR.
use waffle_frontend::{from_wasm_bytes, expand_func, FrontendOptions};

fn frontend_body(wat: &str) -> waffle_ir::FunctionBody {
    let bytes = wat::parse_str(wat).expect("valid test WAT");
    let mut module = from_wasm_bytes(&bytes, &FrontendOptions::default())
        .expect("frontend should parse the module");
    let func = module.funcs.iter().next().expect("defined function");
    let decl = expand_func(&mut module, func).expect("frontend should expand the function");
    decl.body().expect("defined function should have an IR body").clone()
}

#[test]
fn frontend_body_exposes_cfg_targets_through_terminator_record() {
    use cfg_traits::{Block as _, Func as _, Term as _};

    let body = frontend_body(
        r#"(module
            (func (param i32) (result i32)
                local.get 0
                if (result i32)
                    i32.const 1
                else
                    i32.const 2
                end))"#,
    );

    let target_count: usize = body
        .blocks()
        .iter()
        .map(|block| body.blocks()[block].term().targets().count())
        .sum();
    assert!(target_count > 0, "the frontend CFG should contain branch targets");
}

#[test]
fn frontend_body_exposes_terminator_values_through_terminator_record() {
    use cfg_traits::{Block as _, Func as _};
    use ssa_traits::HasValues as _;

    let body = frontend_body(
        r#"(module
            (func (param i32) (result i32)
                local.get 0
                if
                    i32.const 7
                    return
                end
                i32.const 9))"#,
    );

    let value_count: usize = body
        .blocks()
        .iter()
        .map(|block| body.blocks()[block].term().values(&body).count())
        .sum();
    assert!(value_count > 0, "terminators should retain their frontend operands");
}