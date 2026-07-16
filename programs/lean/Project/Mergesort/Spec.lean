import Project.Mergesort.Program

/-!
# Specification for `mergesort`
-/

namespace Project.Mergesort.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `mergesort`.

Informal spec:
Describe what `mergesort` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "mergesort::mergesort"]
def MergesortSpec : Prop :=
  True

end Project.Mergesort.Spec
