// IR module components
// Re-export types from parent
pub use crate::{Block, Value, Local, Func, Global, Table, Memory, Signature, ControlTag};
pub use crate::{Type, HeapType, StorageType, WithNullable, WithMutablility, Handler};
pub use crate::{Subtypes};

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
