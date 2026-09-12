import Project.Mergesort.ExportWorkProof
import CodeLib.SepLogic.CostedTerminalBounds

/-! # Executing mergesort with its proved work budget

`run` starts the canonical named export and supplies the closed work bound to
Talos's executable runner. Under the proved input-size condition, that budget
suffices for a normal return with sorted output. Work charges dominate semantic
transition counts; this adapter does not claim a bound on wall-clock time.
-/

namespace Project.Mergesort.ExecutionBudget

open Wasm Wasm.SmallStep
open Project.Mergesort.ExportWorkProof

/-- Run the named export using its closed numerical bound as the runner budget.
Inputs outside the proved size range still have an executable result, but the
normal-return guarantee below applies only within that range. -/
def run (input : List UInt32) : Option (RunnerResult Universal.State) := do
  let initial ← startExportConfig? (Universal.envFor Project.Mergesort.module)
    Project.Mergesort.module "mergesort" (Spec.args input)
  return (runSteps (workBound input) initial).result

/-- The proved budget runs the actual named export to normal completion, with
sorted output and the physical-page bound on that same final store.
No extra fuel unit is needed: `runSteps 0` recognizes terminal configurations. -/
theorem run_export_sorted (input : List UInt32) (hbound : input.length ≤ 89434754) :
    ∃ store output,
      run input = some (.success [] store) ∧
      store.wasm.host.stdio.output = Spec.encodeValues output ∧
      Spec.SortedPermutation input output ∧
      store.wasm.mem.pages ≤ Spec.growingPageBound input := by
  obtain ⟨initial, initialized,
    ⟨trace, store, amount, output, execution, lengthBound, bound, returned, sorted⟩,
    prefixBounds⟩ := named_export_work input hbound
  have result : (runSteps (workBound input) initial).result = .success [] store := by
    rw [runSteps_result_of_steps_le execution.erase (workBound input)
      (lengthBound.trans bound)]
    cases workBound input - trace.length <;> rfl
  exact ⟨store, output, by simp [run, initialized, result], returned, sorted,
    (prefixBounds trace ⟨.done [], store⟩ amount execution).2⟩

end Project.Mergesort.ExecutionBudget
