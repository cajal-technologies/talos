import Project.FloatMinmax.Program

/-!
# Specification for `float_minmax`
-/

namespace Project.FloatMinmax.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `float_minmax`.

Informal spec:
Describe what `float_minmax` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "float_minmax::float_minmax"]
def FloatMinmaxSpec : Prop :=
  True

end Project.FloatMinmax.Spec
