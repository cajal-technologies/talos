import Project.ByteEcho.Spec

set_option maxRecDepth 4194304
set_option maxHeartbeats 0

namespace Project.ByteEcho.Proof

open Wasm

@[proves Project.ByteEcho.Spec.ByteEchoSpec]
theorem byteEcho_correct : Project.ByteEcho.Spec.ByteEchoSpec := by
  intro byte
  unfold Project.ByteEcho.Spec.RunsBytes Universal.RunsBytes Universal.Runs RunsWith
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_checked_terminates (fuel := 85)
    (fun values store => values == [] && store.wasm.host.stdio.output == [byte])
  · rcases byte with ⟨byte⟩
    decide +revert
  · intro values store h
    cases values with
    | nil =>
        simp only [Bool.and_eq_true] at h
        exact ⟨rfl, beq_iff_eq.mp h.2⟩
    | cons value values => simp at h

end Project.ByteEcho.Proof
