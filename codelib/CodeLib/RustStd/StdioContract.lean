import Interpreter.Wasm.Host.Universal

/-!
# The partial contract shape a stdio program shares

A Talos stdio program reads its whole input, computes, and writes one answer.
Every export of such a program allocates in proportion to that input, so an
allocation failure is a reachable terminal outcome and no total contract
holds.  The shape below is the one `Project.Mergesort.Spec` established and
`Project.RustVec.Spec` wrote out again: a normal return writes exactly the
expected bytes, and the allocator's `talos.oom` trap is admitted as the
alternative.

`RunOutcome`, `ReturnsOutput`, and `RanOutOfMemory` name no module, so they
are the same for every such program.  `PartiallyRuns` and `WritesOrOOM` take
the module, because a contract is about one module's export.  Fuel, linear
memory, and allocator state stay hidden throughout.
-/

namespace Wasm.RustStd.StdioContract

open Wasm

/-- Everything publicly observable at the end of a finite execution. -/
structure RunOutcome where
  outcome : SmallStep.ObservableOutcome
  final : Universal.State

/-- The call returned normally and wrote exactly `output`. -/
def ReturnsOutput (run : RunOutcome) (output : List UInt8) : Prop :=
  run.outcome = .done [] ∧ run.final.stdio.output = output

/-- The call terminated with the allocator's distinguished OOM outcome. -/
def RanOutOfMemory (run : RunOutcome) : Prop :=
  run.outcome = .trapped (.host OOM.trapMessage) ∧ run.final.oom.raised = true

/-- Every finite terminal execution of `m`'s export `op` on `input` either
satisfies `post` or terminates with the allocator's distinguished OOM outcome.
This does not assert termination. -/
def PartiallyRuns (m : Module) (op : String) (input : List UInt8)
    (post : RunOutcome → Prop) : Prop :=
  PartiallyRunsWithOutcome (Universal.envFor m) m op
    (Universal.State.ofInput input)
    (fun outcome final =>
      let run : RunOutcome := ⟨outcome, final⟩
      RanOutOfMemory run ∨ post run)

/-- The shared shape of a stdio contract: a normal return writes exactly
`output`. -/
def WritesOrOOM (m : Module) (op : String) (input output : List UInt8) : Prop :=
  PartiallyRuns m op input (fun run => ReturnsOutput run output)

end Wasm.RustStd.StdioContract
