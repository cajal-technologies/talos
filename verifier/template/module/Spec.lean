import Project.MODULE_NAME.Program

/-!
# Specification for `CRATE_NAME`
-/

namespace Project.MODULE_NAME.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `CRATE_NAME` using
one semantic `Input`, one semantic `Output`, and handwritten `args` / `result`
adapters as described in `verifier/SPECIFICATIONS.md`.

Informal spec:
Describe what `CRATE_NAME` computes here, then replace `True` with the honest
total, partial, or outcome form for what has actually been proved. -/
@[spec_of "rust-exported" "CRATE_NAME::CRATE_NAME"]
def MODULE_NAMESpec : Prop :=
  True

end Project.MODULE_NAME.Spec
