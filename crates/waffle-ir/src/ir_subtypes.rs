//! Subtypes trait and implementations for WAFFLE IR types.
use crate::{Module, SignatureData, Signature, WithMutablility, WithNullable, StorageType, Type, HeapType};
use alloc::collections::BTreeSet;

pub trait Subtypes {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool;
}
impl Subtypes for Signature {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        if vsigs.contains(&(*self, *other)) {
            return true;
        }
        let mut vsigs = vsigs.clone();
        vsigs.insert((*self, *other));
        module.signatures[*self].subtypes(&module.signatures[*other], module, &vsigs)
    }
}
impl Subtypes for SignatureData {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        match (self, other) {
            (SignatureData::Array { ty, .. }, SignatureData::Array { ty: tyo, .. }) => {
                ty.subtypes(tyo, module, vsigs)
            }
            (
                SignatureData::Func {
                    params, returns, ..
                },
                SignatureData::Func {
                    params: po,
                    returns: ro,
                    ..
                },
            ) => {
                params.len() == po.len()
                    && returns.len() == ro.len()
                    && params
                        .iter()
                        .zip(po.iter())
                        .all(|(a, b)| b.subtypes(a, module, vsigs))
                    && returns
                        .iter()
                        .zip(ro.iter())
                        .all(|(a, b)| a.subtypes(b, module, vsigs))
            }
            (SignatureData::Struct { fields, .. }, SignatureData::Struct { fields: fo, .. }) => {
                fields.len() >= fo.len()
                    && fields
                        .iter()
                        .zip(fo.iter())
                        .all(|(a, b)| a.subtypes(b, module, vsigs))
            }
            _ => false,
        }
    }
}
impl<T: Subtypes> Subtypes for WithMutablility<T> {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        return self.mutable == other.mutable && self.value.subtypes(&other.value, module, vsigs);
    }
}
impl<T: Subtypes> Subtypes for WithNullable<T> {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        return (self.nullable == other.nullable || self.nullable)
            && self.value.subtypes(&other.value, module, vsigs);
    }
}
impl Subtypes for StorageType {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        return self
            .clone()
            .unpack()
            .subtypes(&other.clone().unpack(), module, vsigs);
    }
}
impl Subtypes for Type {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        match (self, other) {
            (Type::I32, Type::I32) => true,
            (Type::I64, Type::I64) => true,
            (Type::F32, Type::F32) => true,
            (Type::F64, Type::F64) => true,
            (Type::V128, Type::V128) => true,
            (Type::Heap(h), Type::Heap(i)) => h.subtypes(i, module, vsigs),
            _ => false,
        }
    }
}
impl Subtypes for HeapType {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        match (self, other) {
            (HeapType::ExternRef, HeapType::ExternRef) => true,
            (HeapType::FuncRef, HeapType::FuncRef) => true,
            (HeapType::Sig { sig_index }, HeapType::Sig { sig_index: s2 }) => {
                sig_index.subtypes(s2, module, vsigs)
            }
            (HeapType::FuncRef, HeapType::Sig { sig_index }) => {
                matches!(&module.signatures[*sig_index], SignatureData::Func { .. })
            }
            (HeapType::Array, HeapType::Sig { sig_index }) => {
                matches!(&module.signatures[*sig_index], SignatureData::Array { .. })
            }
            _ => false,
        }
    }
}
