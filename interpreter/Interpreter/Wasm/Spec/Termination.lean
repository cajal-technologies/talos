import Interpreter.Wasm.Spec.Defs
import Interpreter.Wasm.Wp.Call

/-!
# Fuel-free spec predicate bridges

This module re-exports `Spec.Defs` and adds bridges between
`TerminatesWith`, `FuncSpec`, and the weakest-precondition layer.
-/

namespace Wasm

/-- A `FuncSpec` instantiated at concrete args satisfying its precondition
yields a `TerminatesWith` *under the same env*. -/
theorem FuncSpec.to_TerminatesWith {env : HostEnv α} {m : Module} {id : Nat}
    {Pre : List Value → Prop} {Post : Store α → List Value → Prop}
    (spec : FuncSpec env m id Pre Post)
    {initial : Store α} {args : List Value} (hPre : Pre args) :
    TerminatesWith env m id initial args Post :=
  spec args hPre initial

end Wasm
