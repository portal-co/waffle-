# WAFFLE: Wasm Analysis Framework for Lightweight Experimentation

A Wasm-to-Wasm compiler framework in Rust, built around an SSA IR. This is a fork of the original [waffle](https://github.com/cfallin/waffle) by Chris Fallin, maintained under the `portal-co` organization and published as the `portal-pc-waffle` family of crates.

## What it does

WAFFLE reads WebAssembly bytecode, converts it to an SSA (Static Single Assignment) intermediate representation, optionally transforms or optimizes it, and compiles it back to valid Wasm bytecode. The round-trip (Wasm -> IR -> Wasm) is the core operation. All other features (optimization passes, hooking, copying, lowering) are built on top of that.

The IR is a CFG of basic blocks where dataflow is explicit SSA values. Wasm locals are eliminated during parsing and replaced with SSA values and block parameters. All Wasm operators remain at the Wasm abstraction level — memories, tables, and reference types are first-class IR concepts rather than being lowered into implementation details.

## Status

Version 0.6.0-alpha.1. The codebase has been refactored from a single crate into a Cargo workspace of smaller crates (see `crates/`). The round-trip pass is working and has been fuzzed. The IR supports Wasm MVP plus multivalue, SIMD, reference types (including non-nullable funcrefs and typed funcrefs), and GC proposals (arrays, structs). There is a built-in interpreter used for fuzzing differential testing.

The codebase compiles with `#![no_std]` (using `alloc`) in most crates and has `#![forbid(unsafe_code)]` in all library crates.

## Repository

https://github.com/portal-co/waffle-

## Crate structure

The workspace is split into the following crates, all published under the `portal-pc-` prefix:

| Crate | Published name | Purpose |
|---|---|---|
| `.` (root) | `portal-pc-waffle` | Facade; re-exports and gates sub-crates via features |
| `crates/waffle-entity` | `portal-pc-waffle-entity` | Type-safe arena indices (`Func`, `Block`, `Value`, `Memory`, etc.) and indexed containers |
| `crates/waffle-ir` | `portal-pc-waffle-ir` | Core IR types: `Module`, `FunctionBody`, `ValueDef`, `Operator`, `Terminator`; also contains the built-in interpreter and a WASI stub |
| `crates/waffle-frontend` | `portal-pc-waffle-frontend` | Wasm bytecode -> IR conversion (SSA construction, multivalue handling) |
| `crates/waffle-backend` | `portal-pc-waffle-backend` | IR -> Wasm bytecode (reducify, stackify, treeify, localify) |
| `crates/waffle-passes-shared` | `portal-pc-waffle-passes-shared` | Utilities shared between passes: max-SSA conversion, alias resolution, purity predicates |
| `crates/waffle-passes` | `portal-pc-waffle-passes` | Optimization passes: GVN, constant propagation/folding, redundant blockparam elimination, inlining, reordering, `ub_vaccum`, `func_rocket`, `importify` |
| `crates/waffle-lowering` | `portal-pc-waffle-lowering` | Memory-level lowering passes: `mem_fusing` and `unmem` |
| `crates/waffle-copying` | `portal-pc-waffle-copying` | Utilities for copying/cloning module components (`fcopy`, `fts`, `kts`, module copy) |
| `crates/waffle-copying-passes` | `portal-pc-waffle-copying-passes` | Passes that combine copying with optimization (`mapping`, `tcore`) |
| `crates/waffle-hooking` | `portal-pc-waffle-hooking` | Function wrapping/swizzling: replaces a function body with a new body that calls the original, useful for instrumentation |
| `crates/waffle-fuzzing` | `portal-pc-waffle-fuzzing` | Fuzzing helpers: `ArbitraryModule` wrapper, rejection filters |

## Backend pipeline

Compiling a `FunctionBody` back to Wasm bytecode goes through four stages:

1. **Reducify** (`reducify.rs`) — Handles irreducible control flow by duplicating code to make all CFG loops reducible. Uses RPO-based loop detection. The comments warn of potential exponential code blowup for pathological inputs (dense state machines, cliques).

2. **Stackify** (`stackify.rs`) — Converts the reducible CFG into a structured Wasm control-flow AST (blocks, loops, if-then) using Ramsey's algorithm.

3. **Treeify** (`treeify.rs`) — Identifies SSA values used exactly once and "trees" them: moves the computation inline to avoid materializing an intermediate local.

4. **Localify** (`localify.rs`) — Linear-scan register allocation over the remaining SSA values, assigning them to Wasm locals with no overlapping live ranges.

## Frontend

The frontend (`waffle-frontend`) parses Wasm with `wasmparser` and builds SSA as it goes. When it discovers multiple reaching definitions for a Wasm local (e.g. at a join point), it inserts block parameters rather than phi nodes. Multivalue blocks (Wasm parameters and results for every control-flow construct) are fully handled. Function bodies are parsed lazily and expanded on demand.

## Optimization passes

`OptOptions` (in `waffle-passes`) controls:
- `gvn` — global value numbering (domtree walk with a scoped map)
- `cprop` — constant propagation and folding (uses the interpreter's `const_eval`)
- `redundant_blockparams` — removes block parameters that always carry the same value
- `inline_refs` — inlines single-use pure values
- `ub_vaccum` — removes unreachable/undefined-behavior code

Additional passes include function inlining, function reordering, `importify` (converts internal functions to imports under a feature flag), `func_rocket` (cancels paired call/inverse-call patterns), and memory-level operations in `waffle-lowering`.

## Fuzzing

The `fuzz/` directory contains six libfuzzer targets:

- `roundtrip` — parses generated Wasm and compiles it back; checks for panics
- `roundtrip_roundtrip` — checks that two round-trips produce identical output
- `differential` — compares globals and memory of the original Wasm run against the round-tripped version under Wasmtime (with fuel limits)
- `opt_diff` — compares interpreter execution results before and after optimization
- `irreducible` — exercises the reducify pass specifically
- `parse_ir` — exercises IR parsing

## Wasm feature support

- MVP instructions
- Multivalue (block params/returns)
- SIMD (via `wasmparser`'s `simd` feature)
- Reference types: `funcref`, `externref`, non-nullable refs, typed funcrefs
- GC proposal types: arrays, structs (subtype checking implemented in `ir_subtypes.rs`)
- Exception handling (unstable, behind `unstable-exceptions` feature flag)

## Optional features

- `frontend` / `backend` — enable the parsing and code-generation halves independently
- `copying` — enable `waffle-copying`
- `hooking` — enable `waffle-hooking`
- `tcore` — enable `waffle-copying-passes`
- `fuzzing` — enable `waffle-fuzzing`
- `ssa-traits-02` / `ssa-traits-03` — implement `ssa-traits` and `cfg-traits` interfaces from `portal-co/codegen-utils`
- `rkyv-impl` — derive `rkyv` Archive/Serialize/Deserialize for IR types
- `importify` — enable the `importify` pass in `waffle-passes`

## Related projects

- [Binaryen](https://github.com/WebAssembly/binaryen) — AST-based IR, C/C++ API only; supports CFG-to-Wasm but not Wasm-to-CFG
- [Walrus](https://github.com/rustwasm/walrus) — Rust, Wasm-to-Wasm transforms, but IR mirrors bytecode closely (no SSA)
- [Cranelift](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift/) — similar SSA IR with block params, but only Wasm-to-IR (no Wasm output), and it lowers Wasm abstractions

## License

Apache-2.0 WITH LLVM-exception
