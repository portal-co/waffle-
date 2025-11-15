use crate::*;

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
