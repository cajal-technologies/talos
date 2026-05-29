import Project.DynDispatch.Program

/-! # Specifications for the `dyn_dispatch` crate

The crate exists as a small Rust source that compiles to wasm using
`call_indirect` through a `&dyn Trait` vtable — the simplest shape we
could find that exercises the indirect-call machinery in
`Interpreter.Wasm` end-to-end. The semantic verification of that
indirect dispatch (table lookup + memory-backed vtable read + chained
function call) is tracked separately; this file only carries the
module under that name so the verifier scaffolding has a Lean home
for the crate. -/

namespace Project.DynDispatch.Spec
end Project.DynDispatch.Spec
