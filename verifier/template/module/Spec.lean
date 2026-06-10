import Project.MODULE_NAME.Program

/-!
# Specification for `CRATE_NAME`
-/

namespace Project.MODULE_NAME.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `CRATE_NAME`.

Informal spec:
Describe what `CRATE_NAME` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "CRATE_NAME::CRATE_NAME"]
def MODULE_NAMESpec : Prop :=
  True

end Project.MODULE_NAME.Spec
