import Project.Itoa.Program

/-!
# Specification for `itoa`
-/

namespace Project.Itoa.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `itoa`.

Informal spec:
Describe what `itoa` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "itoa::itoa"]
def ItoaSpec : Prop :=
  True

end Project.Itoa.Spec
