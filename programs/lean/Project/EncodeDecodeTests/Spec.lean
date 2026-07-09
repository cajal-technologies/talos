import Project.EncodeDecodeTests.Program

/-!
# Specification for `encode_decode_tests`
-/

namespace Project.EncodeDecodeTests.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `encode_decode_tests`.

Informal spec:
Describe what `encode_decode_tests` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "encode_decode_tests::encode_decode_tests"]
def EncodeDecodeTestsSpec : Prop :=
  True

end Project.EncodeDecodeTests.Spec
