import HexEncodeStdio.ReachOutcome
import HexEncodeStdio.Outcome

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio.Spec
open Wasm.SmallStep

def EncodesConfig (input : List UInt8) (config : Config Universal.State) : Prop :=
  ∃ final, config = ⟨.done [], final⟩ ∧
    final.wasm.host.stdio.output = encode input

/-- Turn a finite relational success/OOM proof into the executable witness
required by the submission's runner-level interface. -/
theorem reachesOrOOM_to_runner
    (input : List UInt8) (initial : Config Universal.State)
    (h : ReachesOrOOM initial (EncodesConfig input)) :
    ∃ fuel, Project.HexEncodeStdio.Outcome.EncodesOrOOM input
      (runSteps fuel initial).result := by
  rcases h with ⟨final, ⟨trace, hsteps⟩, hfinal⟩ | htrap
  · rcases hfinal with ⟨store, rfl, hout⟩
    refine ⟨trace.length, ?_⟩
    rw [runSteps_eq_success_of_steps hsteps]
    exact ⟨rfl, hout⟩
  · rcases htrap with ⟨trace, store, hsteps, hoom⟩
    refine ⟨trace.length, ?_⟩
    rw [runSteps_finalConfig_of_steps hsteps]
    exact ⟨rfl, hoom⟩

end Project.HexEncodeStdio
