import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Helpers
import HexEncodeStdio.Blueprint
import HexEncodeStdio.AllocatorMemoryCost
import HexEncodeStdio.ResourceProof
import HexEncodeStdio.ExecutionBudget
import Project.HexStdio.Proof

/-!
# `hex_stdio` encode — public total correctness

`hex_encode_stdio_correct` establishes the exported `encode` entry point's total
OOM-disjunction specification `Project.HexStdio.Spec.EncodeSpec`: for every
input, `encode` writes the lowercase hexadecimal encoding of the bytes it reads,
or its private allocator reaches the `talos.oom` terminal trap. A terminal
outcome is always reached. See `Project/HexStdio/Analysis/`.

`Project.HexEncodeStdio.ResourceProof.named_export_resources` strengthens the
covered range of at most 357738263 input bytes to normal return, with a
numerical byte-work bound and a physical-page bound at every execution prefix.
Its formulas are defined in `Project.HexEncodeStdio.ResourceBounds`.
-/

theorem hex_encode_stdio_correct : Project.HexStdio.Spec.EncodeSpec :=
  Project.HexStdio.Proof.encode_total_correct
