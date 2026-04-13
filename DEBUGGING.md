# Debugging Notes

## `FuncDecl::Lazy` missing (backend feature)

**Symptom:** Enabling `features = ["backend"]` on `portal-pc-waffle` fails to compile
`portal-pc-waffle-backend` with:

```
error[E0599]: no variant or associated item named `Lazy` found for enum
`portal_pc_waffle_ir::FuncDecl<'a>` in the current scope
```

**Location:** `crates/waffle-backend/src/backend/mod.rs` — references `FuncDecl::Lazy`
and `FuncDecl::Compiled` variants that no longer exist in `waffle-ir`.

**Root cause:** `waffle-backend` was written against an older version of `waffle-ir`
where `FuncDecl` had `Lazy` and `Compiled` variants. These were removed or renamed in
the current `waffle-ir`, creating a version mismatch.

**Workaround (used in `pit-patch`):** Enable both `frontend` AND `backend` features
together — the `frontend` feature appears to gate the code paths that hit the missing
variant, allowing the crate to compile. This was discovered empirically on 2026-03-27.

**Access pattern:** With `frontend + backend` features enabled, `to_wasm_bytes` is
accessible via `portal_pc_waffle::backend::ModuleExt`. The path
`portal_pc_waffle::portal_pc_waffle_backend::ModuleExt` (suggested by rustc diagnostics)
does not resolve; use `portal_pc_waffle::backend::ModuleExt` instead.

## `to_wasm_bytes` not in scope

**Symptom:** `m.to_wasm_bytes()` fails with "method not found" even when features are
correct.

**Fix:** Explicitly import the trait:
```rust
use portal_pc_waffle::backend::ModuleExt as _;
```

This is needed because the local re-definition of `portal_pc_waffle::ModuleExt`
(a supertrait combining backend + frontend) shadows the `waffle_backend::ModuleExt`
re-export, but does not itself define `to_wasm_bytes` — that method lives on the
`backend::ModuleExt` supertrait and must be imported directly.
