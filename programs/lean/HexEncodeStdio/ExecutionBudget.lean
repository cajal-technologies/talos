import HexEncodeStdio.ResourceProof
import CodeLib.SepLogic.CostedTerminalBounds

/-! # Executing the hex encoder with its proved work budget

`run` supplies the closed resource bound to the canonical named export. The
shared runner lemma turns the relational work certificate into executable
normal completion, retaining the exact encoded output and physical-page bound.
The work measure does not bound elapsed time or interpreter CPU complexity.
-/

namespace Project.HexEncodeStdio.ExecutionBudget

open Wasm Wasm.SmallStep Project.HexStdio
open Project.HexEncodeStdio.ResourceProof Project.HexEncodeStdio.ResourceBounds

/-- Execute the named encoder with its proved numerical work bound as fuel.
The normal-return guarantee applies within the stated input-size range. -/
def run (input : List UInt8) : Option (RunnerResult Universal.State) := do
  let initial ← startConfig? (Universal.envFor Project.HexStdio.module)
    Project.HexStdio.module "encode" (Universal.State.ofInput input)
  return (runSteps (workBound input) initial).result

/-- The supplied budget suffices for normal completion with the exact lowercase
hex encoding. The physical page interval refers to that same returned store. -/
theorem run_export_encoded (input : List UInt8) (hbound : input.length ≤ 357738263) :
    ∃ store,
      run input = some (.success [] store) ∧
      store.wasm.host.stdio.output = Spec.encode input ∧
      17 ≤ store.wasm.mem.pages ∧ store.wasm.mem.pages ≤ pageBound input := by
  obtain ⟨initial, initialized,
    ⟨trace, store, amount, execution, encoded, lengthBound, bound⟩,
    pageBounds, _workBounds⟩ := named_export_resources input hbound
  have result : (runSteps (workBound input) initial).result = .success [] store := by
    rw [runSteps_result_of_steps_le execution.erase (workBound input)
      (lengthBound.trans bound)]
    cases workBound input - trace.length <;> rfl
  exact ⟨store, by simp [run, initialized, result], encoded,
    pageBounds trace ⟨.done [], store⟩ execution.erase⟩

end Project.HexEncodeStdio.ExecutionBudget
