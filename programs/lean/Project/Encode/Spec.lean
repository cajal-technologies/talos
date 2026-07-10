import Project.Encode.Program

/-!
# Specification for `encode`
-/

namespace Project.Encode.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `encode`.

Informal spec:
Describe what `encode` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "encode::encode"]
def EncodeSpec : Prop :=
  True

end Project.Encode.Spec
