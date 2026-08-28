import Project.Xor.Spec

set_option maxRecDepth 4194304
set_option maxHeartbeats 0

namespace Project.Xor.Proof

open Wasm

@[proves Project.Xor.Spec.XorSpec]
theorem xor_correct : Project.Xor.Spec.XorSpec := by
  intro first second
  unfold Project.Xor.Spec.RunsBytes Universal.RunsBytes Universal.Runs RunsWith
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_checked_terminates (fuel := 121)
    (fun values store =>
      values == [] && store.wasm.host.stdio.output == [first ^^^ second])
  · rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    native_decide +revert
  · intro values store h
    cases values with
    | nil =>
        simp only [Bool.and_eq_true] at h
        exact ⟨rfl, beq_iff_eq.mp h.2⟩
    | cons value values => simp at h

end Project.Xor.Proof
