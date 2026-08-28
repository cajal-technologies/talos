import Mathlib
import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Helpers
import HexEncodeStdio.Blueprint

/-!
# `hex_stdio` encode — public total correctness

`hex_encode_stdio_correct` establishes the exported `encode` entry point's total
OOM-disjunction specification `Project.HexStdio.Spec.EncodeSpec`: for every
input, `encode` writes the lowercase hexadecimal encoding of the bytes it reads,
or its private allocator reaches the `talos.oom` terminal trap. A terminal
outcome is always reached. See `Project/HexStdio/Analysis/`.
-/

theorem hex_encode_stdio_correct : Project.HexStdio.Spec.EncodeSpec := by
  intro input
  exact Project.HexEncodeStdio.Blueprint.encode_export_outcome input
