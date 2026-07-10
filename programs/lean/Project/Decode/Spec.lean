import Project.Decode.Program

/-!
# Specification for `decode`
-/

namespace Project.Decode.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `decode`.

Informal spec:
Describe what `decode` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "decode::decode"]
def DecodeSpec : Prop :=
  True

end Project.Decode.Spec
