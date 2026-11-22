import Project.ByteEcho.Adequacy

/-!
# Correctness of the compiled byte echo

The public theorem is the total adequacy result: the export reads its one
input byte into a freshly allocated buffer and writes exactly that byte back.
-/

namespace Project.ByteEcho.Proof

open Wasm

@[proves Project.ByteEcho.Spec.ByteEchoSpec]
theorem byte_echo_correct : Project.ByteEcho.Spec.ByteEchoSpec :=
  Project.ByteEcho.Adequacy.entry_adequacy

end Project.ByteEcho.Proof
