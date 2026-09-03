import Project.FloatMinmax.Program

/-!
# Specification for `float_minmax`
-/

namespace Project.FloatMinmax.Spec

open Wasm

/-- TODO: state and prove the behaviour of the `check_min` and `check_max`
exports as two separate semantic specifications.

Informal spec:
Describe what each exported check computes, then replace `True` with real
properties. This placeholder is deliberately not registered with `@[spec_of]`:
there is no `float_minmax` export, and `True` is not a specification. -/
def FloatMinmaxSpec : Prop :=
  True

end Project.FloatMinmax.Spec
