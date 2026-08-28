import Mathlib
import CodeLib
import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.Helpers
import HexDecodeStdio.Proof

/-!
# `hex_stdio` decode — public total correctness

`hex_decode_stdio_correct` establishes the exported `decode` entry point's total
OOM-disjunction specification `Project.HexStdio.Spec.DecodeSpec`: for every
input, `decode` writes the reference decoding (a status byte followed, on
acceptance, by the decoded bytes), or its private allocator reaches the
`talos.oom` terminal trap. A terminal outcome is always reached. See
`Project/HexStdio/Analysis/`.
-/

theorem hex_decode_stdio_correct : Project.HexStdio.Spec.DecodeSpec := by
  intro input
  exact Project.HexDecodeStdio.decode_export_outcome input
