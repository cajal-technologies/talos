import Project.EncodeDecode.Program

/-!
# Specification for `encode_decode`
-/

namespace Project.EncodeDecode.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `encode_decode`.

Informal spec:
Describe what `encode_decode` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "encode_decode::encode_decode"]
def EncodeDecodeSpec : Prop :=
  True

end Project.EncodeDecode.Spec
