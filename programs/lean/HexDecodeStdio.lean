import Mathlib
import CodeLib
import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.Helpers
import HexDecodeStdio.Proof

/-!
**This is the only file you edit.** Replace `sorry` below with your proof.

Do not change the statement: it must stay identical to `Challenge.lean`, and
comparator rejects the submission if it differs. You may use `Mathlib`,
`CodeLib`, and anything you add under `Submission/`.
-/

theorem hex_decode_stdio_correct : Project.HexStdio.Spec.DecodeSpec := by
  intro input
  exact Submission.HexDecodeStdio.decode_export_outcome input
