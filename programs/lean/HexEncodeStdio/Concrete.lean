import Project.HexStdio.Spec
import HexEncodeStdio.Outcome

namespace Submission.Concrete

open Wasm

-- The zero-iteration case of all three data loops, checked by kernel
-- reduction of the executable small-step interpreter.
set_option maxRecDepth 100000 in
theorem func10_export_run_nil :
    ∃ config fuel,
      startConfig? (Universal.envFor Project.HexStdio.«module»)
          Project.HexStdio.«module» "encode" (Universal.State.ofInput []) =
        some config ∧
      Submission.Outcome.EncodesOrOOM []
        (SmallStep.runSteps fuel config).result := by
  refine ⟨_, 260, rfl, ?_⟩
  apply Submission.Outcome.checkEncodesOrOOM_sound
  rfl

end Submission.Concrete
