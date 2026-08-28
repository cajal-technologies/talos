import Mathlib
import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Helpers
import HexEncodeStdio.Blueprint

/-!
**This is the only file you edit.** Replace `sorry` below with your proof.

Do not change the statement: it must stay identical to `Challenge.lean`, and
comparator rejects the submission if it differs. You may use `Mathlib`,
`CodeLib`, and anything you add under `Submission/`.
-/

theorem hex_encode_stdio_correct : Project.HexStdio.Spec.EncodeSpec := by
  intro input
  exact Submission.Blueprint.encode_export_outcome input
