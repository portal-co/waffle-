//! Core IR type definitions for WAFFLE.
use crate::{declare_entity, EntityRef};
pub use waffle_entity::entities::*;

#[non_exhaustive]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
#[cfg_attr(feature = "rkyv-impl", rkyv(compare(PartialEq)))]
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
#[non_exhaustive]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
#[cfg_attr(feature = "rkyv-impl", rkyv(compare(PartialEq)))]
///a `Type` that can be stored on the heap
pub enum HeapType {
    FuncRef,
    ExternRef,
    Sig { sig_index: Signature },
    Array,
    /// The abstract `any` heap type (top of the GC type hierarchy).
    Any,
    /// The abstract `eq` heap type (supertype of all ref.eq-comparable types).
    Eq,
    /// The abstract `i31` heap type (unboxed 31-bit integer).
    I31,
    /// The abstract `struct` heap type (supertype of all struct types).
    Struct,
    /// The abstract `none` heap type (bottom of the internal type hierarchy).
    None,
    /// The abstract `noextern` heap type (bottom of the external type hierarchy).
    NoExtern,
    /// The abstract `nofunc` heap type (bottom of the function type hierarchy).
    NoFunc,
    /// The abstract `exn` heap type.
    Exn,
    /// The abstract `noexn` heap type.
    NoExn,
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
#[cfg_attr(feature = "rkyv-impl", rkyv(compare(PartialEq)))]
///Something, alsong with whether it can be `null`
pub struct WithNullable<T> {
    pub value: T,
    pub nullable: bool,
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
///Something, alsong with whether it can be mutated
pub struct WithMutablility<T> {
    pub value: T,
    pub mutable: bool,
}
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    serde::Serialize,
    serde::Deserialize,
    Default,
)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
///An exception's handler
pub enum Handler<T> {
    ///Rethrow the exception
    #[default]
    Throw,
    ///Catch the exception
    Catch(T),
}
#[non_exhaustive]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
///A storage type
pub enum StorageType {
    Val(Type),
    I8,
    I16,
}
impl StorageType {
    pub fn unpack(self) -> Type {
        match self {
            StorageType::Val(a) => a,
            StorageType::I8 => Type::I32,
            StorageType::I16 => Type::I64,
        }
    }
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
impl From<wasmparser::FieldType> for WithMutablility<StorageType> {
    fn from(value: wasmparser::FieldType) -> Self {
        WithMutablility {
            value: match value.element_type {
                wasmparser::StorageType::I8 => StorageType::I8,
                wasmparser::StorageType::I16 => StorageType::I16,
                wasmparser::StorageType::Val(val_type) => StorageType::Val(val_type.into()),
            },
            mutable: value.mutable,
        }
    }
}
impl From<wasmparser::RefType> for WithNullable<HeapType> {
    fn from(ty: wasmparser::RefType) -> Self {
        let nullable = ty.is_nullable();
        let value = match ty.heap_type() {
            wasmparser::HeapType::Concrete(idx) => HeapType::Sig {
                sig_index: Signature::new(idx.as_module_index().unwrap() as usize),
            },
            wasmparser::HeapType::Abstract { ty, .. } => match ty {
                wasmparser::AbstractHeapType::Func => HeapType::FuncRef,
                wasmparser::AbstractHeapType::Extern => HeapType::ExternRef,
                wasmparser::AbstractHeapType::Any => HeapType::Any,
                wasmparser::AbstractHeapType::None => HeapType::None,
                wasmparser::AbstractHeapType::NoExtern => HeapType::NoExtern,
                wasmparser::AbstractHeapType::NoFunc => HeapType::NoFunc,
                wasmparser::AbstractHeapType::Eq => HeapType::Eq,
                wasmparser::AbstractHeapType::Struct => HeapType::Struct,
                wasmparser::AbstractHeapType::Array => HeapType::Array,
                wasmparser::AbstractHeapType::I31 => HeapType::I31,
                wasmparser::AbstractHeapType::Exn => HeapType::Exn,
                wasmparser::AbstractHeapType::NoExn => HeapType::NoExn,
                // Cont, NoCont and any future abstract types
                _ => HeapType::FuncRef,
            },
        };
        WithNullable { value, nullable }
    }
}
impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::V128 => write!(f, "v128"),
            Type::Heap(h) => write!(
                f,
                "ref({} {})",
                if h.nullable { "null" } else { "not_null" },
                &h.value
            ),
        }
    }
}
impl core::fmt::Display for HeapType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HeapType::FuncRef => write!(f, "funcref"),
            HeapType::ExternRef => write!(f, "externref"),
            HeapType::Sig { sig_index } => write!(f, "sigref({})", sig_index),
            HeapType::Array => write!(f, "arrayref"),
            HeapType::Any => write!(f, "anyref"),
            HeapType::Eq => write!(f, "eqref"),
            HeapType::I31 => write!(f, "i31ref"),
            HeapType::Struct => write!(f, "structref"),
            HeapType::None => write!(f, "nullref"),
            HeapType::NoExtern => write!(f, "nullexternref"),
            HeapType::NoFunc => write!(f, "nullfuncref"),
            HeapType::Exn => write!(f, "exnref"),
            HeapType::NoExn => write!(f, "nullexnref"),
            _ => write!(f, "<unknown heap type>"),
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
impl From<WithMutablility<StorageType>> for wasm_encoder::FieldType {
    fn from(value: WithMutablility<StorageType>) -> Self {
        wasm_encoder::FieldType {
            element_type: match value.value {
                StorageType::Val(t) => wasm_encoder::StorageType::Val(t.into()),
                StorageType::I8 => wasm_encoder::StorageType::I8,
                StorageType::I16 => wasm_encoder::StorageType::I16,
            },
            mutable: value.mutable,
        }
    }
}
impl From<WithNullable<HeapType>> for wasm_encoder::RefType {
    fn from(ty: WithNullable<HeapType>) -> wasm_encoder::RefType {
        let heap_type = match &ty.value {
            HeapType::FuncRef => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Func,
            },
            HeapType::ExternRef => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Extern,
            },
            HeapType::Any => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Any,
            },
            HeapType::None => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::None,
            },
            HeapType::NoExtern => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::NoExtern,
            },
            HeapType::NoFunc => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::NoFunc,
            },
            HeapType::Eq => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Eq,
            },
            HeapType::Struct => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Struct,
            },
            HeapType::Array => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Array,
            },
            HeapType::I31 => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::I31,
            },
            HeapType::Exn => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Exn,
            },
            HeapType::NoExn => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::NoExn,
            },
            HeapType::Sig { sig_index } => {
                wasm_encoder::HeapType::Concrete(sig_index.index() as u32)
            }
            _ => panic!("Cannot convert {:?} into reftype", ty),
        };
        wasm_encoder::RefType {
            nullable: ty.nullable,
            heap_type,
        }
    }
}
