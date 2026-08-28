import CodeLib
import Project.HexStdio.Spec

namespace Submission.Outcome

open Wasm Wasm.SmallStep
open Project.HexStdio.Spec

/-- The executable runner's two permitted observations for this challenge. -/
def EncodesOrOOM (input : List UInt8) : RunnerResult Universal.State → Prop
  | .success values final =>
      values = [] ∧ final.wasm.host.stdio.output = encode input
  | .trapped reason final =>
      reason = .host OOM.trapMessage ∧ final.wasm.host.oom.raised = true
  | .outOfFuel _ | .internalError _ _ => False

/-- Executable checker used only to certify closed runner calculations. -/
def checkEncodesOrOOM (input : List UInt8) : RunnerResult Universal.State → Bool
  | .success values final =>
      decide (values = []) &&
        decide (final.wasm.host.stdio.output = encode input)
  | .trapped reason final =>
      decide (reason = .host OOM.trapMessage) && final.wasm.host.oom.raised
  | .outOfFuel _ | .internalError _ _ => false

theorem checkEncodesOrOOM_sound (input : List UInt8)
    (result : RunnerResult Universal.State)
    (h : checkEncodesOrOOM input result = true) :
    EncodesOrOOM input result := by
  cases result <;> simp_all [checkEncodesOrOOM, EncodesOrOOM]

/-- Turn one checked interpreter run into the public fuel-free disjunction. -/
theorem run_result_to_spec (input : List UInt8) (config : Config Universal.State)
    (hstart : startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput input) =
      some config)
    (fuel : Nat)
    (houtcome : EncodesOrOOM input (runSteps fuel config).result) :
    RunsEncode input (encode input) ∨ RunsOutOfMemory input := by
  cases hrun : (runSteps fuel config).result with
  | success values final =>
      left
      refine ⟨config, hstart, ?_⟩
      apply runSteps_success_terminates hrun
        (fun actual reached =>
          actual = [] ∧ reached.wasm.host.stdio.output = encode input)
      simpa [EncodesOrOOM, hrun] using houtcome
  | trapped reason final =>
      right
      have hout :
          reason = .host OOM.trapMessage ∧
            final.wasm.host.oom.raised = true := by
        simpa [EncodesOrOOM, hrun] using houtcome
      rw [hout.1] at hrun
      refine ⟨config, hstart, ?_⟩
      apply runSteps_trapped_trapsWith hrun
        (fun reached => reached.wasm.host.oom.raised = true)
      exact hout.2
  | outOfFuel final => simp [EncodesOrOOM, hrun] at houtcome
  | internalError error final => simp [EncodesOrOOM, hrun] at houtcome

end Submission.Outcome
