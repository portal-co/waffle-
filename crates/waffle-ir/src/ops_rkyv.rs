// `Operator` is `#[repr(u16)]` and all its field types are `Copy` types with
// stable in-memory layout, so it is safe for it to be its own archived form.
// This file is kept separate from `ops.rs` because `waffle-ir` uses
// `#![deny(unsafe_code)]` crate-wide; concentrating the two unavoidable
// `unsafe` items here makes the unsafety easy to audit.
//
// Why is this sound?
//   - `Portable`: `Operator` is `repr(u16)` with only well-defined `Copy`
//     field types (u8, u32, u64, [u8;16], entity-ref newtypes that are
//     `repr(transparent)` over u32). Layout is stable and target-independent.
//   - `write_unchecked`: the archived type *is* `Operator` itself, so writing
//     the live value into the archive slot is a valid, correctly-typed write.
//
// TODO: if rkyv ever exposes a safe path for self-archived `repr(uN)` enums
// (e.g. a `SelfArchive` derive or a `NoUndef`-free `Place::write` overload),
// migrate to that and restore `forbid(unsafe_code)` on this crate.
#![allow(unsafe_code)]

use crate::Operator;

// SAFETY: see module-level comment.
unsafe impl rkyv::Portable for Operator {}

impl rkyv::Archive for Operator {
    type Archived = Self;
    type Resolver = ();
    fn resolve(&self, _: Self::Resolver, out: rkyv::Place<Self::Archived>) {
        // SAFETY: `Archived = Self` and `Operator` is `Portable` (above).
        unsafe { out.write_unchecked(*self) };
    }
}

impl<S: rkyv::rancor::Fallible + ?Sized> rkyv::Serialize<S> for Operator {
    fn serialize(&self, _: &mut S) -> Result<(), S::Error> {
        Ok(())
    }
}

impl<D: rkyv::rancor::Fallible + ?Sized> rkyv::Deserialize<Operator, D> for Operator {
    fn deserialize(&self, _: &mut D) -> Result<Operator, D::Error> {
        Ok(*self)
    }
}
