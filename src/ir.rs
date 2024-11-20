//! Intermediate representation for Wasm.

use crate::{declare_entity, entity::EntityRef};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
/// Types in waffle's IR.
///
/// These types correspond to (a subset of) the primitive Wasm value
/// types: integers, floats, SIMD vectors, and function references
/// (optionally typed).
///
/// Every SSA value in a function body has a `Type`, unless it is a
/// tuple (multi-value or zero-value result).

pub enum Type {
    /// A 32-bit integer. Signedness is unspecified: individual
    /// operators specify how they handle sign.
    I32,
    /// A 64-bit integer. Signedness is unspecified: individual
    /// operators specify how they handle sign.
    I64,
    /// A 32-bit IEEE 754 floating point value. Semantics around NaNs
    /// are defined by individual operators; from the point of view of
    /// IR scaffolding, floating-point values are bags of bits.
    F32,
    /// A 64-bit IEEE 754 floating point value. Semantics around NaNs
    /// are defined by individual operators; from the point of view of
    /// IR scaffolding, floating-point values are bags of bits.
    F64,
    /// A 128-bit SIMD vector value. Lanes and lane types are
    /// specified by individual operators; from the point of view of
    /// IR scaffolding, SIMD vector values are bags of bits.
    V128,
    /// A heap type.
    Heap(WithNullable<HeapType>),
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
///a `Type` that can be stored on the heap
pub enum HeapType {
    FuncRef,
    ExternRef,
    Sig { sig_index: Signature },
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
///Something, alsong with whether it can be `null`
pub struct WithNullable<T> {
    pub value: T,
    pub nullable: bool,
}

impl From<wasmparser::ValType> for Type {
    fn from(ty: wasmparser::ValType) -> Self {
        match ty {
            wasmparser::ValType::I32 => Type::I32,
            wasmparser::ValType::I64 => Type::I64,
            wasmparser::ValType::F32 => Type::F32,
            wasmparser::ValType::F64 => Type::F64,
            wasmparser::ValType::V128 => Type::V128,
            wasmparser::ValType::Ref(r) => Type::Heap(r.into()),
        }
    }
}
impl From<wasmparser::RefType> for WithNullable<HeapType> {
    fn from(ty: wasmparser::RefType) -> Self {
        if ty.is_extern_ref() {
            return WithNullable {
                nullable: ty.is_nullable(),
                value: HeapType::ExternRef,
            };
        }
        match ty.type_index() {
            Some(idx) => {
                let nullable = ty.is_nullable();
                WithNullable {
                    nullable,
                    value: HeapType::Sig {
                        sig_index: Signature::new(idx.as_module_index().unwrap() as usize),
                    },
                }
            }
            None => WithNullable {
                value: HeapType::FuncRef,
                nullable: ty.is_nullable(),
            },
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::V128 => write!(f, "v128"),
            Type::Heap(h) => write!(f,"ref({} {})",if h.nullable{
                "null"
            }else{
                "not_null"
            },&h.value)
        }
    }
}

impl std::fmt::Display for HeapType{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self{
            HeapType::FuncRef => write!(f, "funcref"),
            HeapType::ExternRef => write!(f, "externref"),
            HeapType::Sig { sig_index } => write!(
                f,
                "sigref({})",
                sig_index
            ),
        }
    }
}

impl From<Type> for wasm_encoder::ValType {
    fn from(ty: Type) -> wasm_encoder::ValType {
        match ty {
            Type::I32 => wasm_encoder::ValType::I32,
            Type::I64 => wasm_encoder::ValType::I64,
            Type::F32 => wasm_encoder::ValType::F32,
            Type::F64 => wasm_encoder::ValType::F64,
            Type::V128 => wasm_encoder::ValType::V128,
            Type::Heap(h) => wasm_encoder::ValType::Ref(h.into()),
        }
    }
}

impl From<WithNullable<HeapType>> for wasm_encoder::RefType {
    fn from(ty: WithNullable<HeapType>) -> wasm_encoder::RefType {
        match &ty.value {
            HeapType::ExternRef => wasm_encoder::RefType::EXTERNREF,
            HeapType::FuncRef => wasm_encoder::RefType::FUNCREF,
            HeapType::Sig { sig_index } => wasm_encoder::RefType {
                nullable: ty.nullable,
                heap_type: wasm_encoder::HeapType::Concrete(sig_index.0),
            },
            _ => panic!("Cannot convert {:?} into reftype", ty),
        }
    }
}

// Per-module index spaces:

// A signature (list of parameter types and list of return types) in
// the module.
declare_entity!(Signature, "sig");
// A function in the module.
declare_entity!(Func, "func");
// A global variable in the module.
declare_entity!(Global, "global");
// A table in the module.
declare_entity!(Table, "table");
// A memory in the module.
declare_entity!(Memory, "memory");
// A control tag in the module
declare_entity!(ControlTag, "control_tag");
// Per-function index spaces:

// A basic block in one function body.
declare_entity!(Block, "block");
// A local variable (storage slot) in one function body.
declare_entity!(Local, "local");
// An SSA value in one function body.
declare_entity!(Value, "v");

mod module;
pub use module::*;
mod func;
pub use func::*;
mod value;
pub use value::*;
mod display;
pub use display::*;
mod debug;
pub use debug::*;
