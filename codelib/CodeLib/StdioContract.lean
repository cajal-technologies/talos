import Interpreter.Wasm.Host.Universal

/-!
# The contract shapes a stdio program shares

A Talos stdio program reads its whole input, computes, and writes one answer.
An export whose allocation grows with that input can reach an allocation
failure, so no contract that promises a normal return holds for it.
`Project.Mergesort.Spec` established the shape for that case: a normal
return, with the allocator's `talos.oom` trap admitted as the alternative.
The byte-level form below, where a normal return writes exactly the expected
bytes, is the one `Project.RustVec.Spec` writes out.

Two shapes carry that alternative.  `PartiallyRuns` and `WritesOrOOM`
classify every finite terminal execution and do not assert termination.
`Runs` and `TerminatesWritingOrOOM` assert that the export terminates in one
of the same two outcomes.

`RunOutcome`, `ReturnsOutput`, and `RanOutOfMemory` name no module, so one
definition of each serves every module.  `PartiallyRuns`, `WritesOrOOM`,
`Runs` and `TerminatesWritingOrOOM` take the module, because a contract is
about one module's export.  `Project.Mergesort.Spec` keeps a `ReturnsOutput`
of its own, whose `output` parameter is a `List UInt32` that `encodeValues`
turns into bytes.  Fuel, linear memory, and allocator state stay hidden
throughout.
-/

namespace Wasm.StdioContract

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

/-- Export `op` of `m`, started on `input` at its call site, reaches a
terminal outcome, and that outcome either satisfies `post` or is the
allocator's distinguished OOM outcome.  This is the total form of
`PartiallyRuns`: it asserts termination.  The start configuration is the
one `PartiallyRunsWithOutcome` uses, so a proof of `PartiallyRuns` and a
proof of `Runs` speak about the same run. -/
def Runs (m : Module) (op : String) (input : List UInt8)
    (post : RunOutcome → Prop) : Prop :=
  ∃ config,
    startCallConfig? (Universal.envFor m) m op (Universal.State.ofInput input) =
      some config ∧
    SmallStep.TerminatesWithOutcome config (fun outcome final =>
      let run : RunOutcome := ⟨outcome, final.wasm.host⟩
      RanOutOfMemory run ∨ post run)

/-- The total shape of a stdio contract: the run terminates, and a normal
return writes exactly `output`. -/
def TerminatesWritingOrOOM (m : Module) (op : String)
    (input output : List UInt8) : Prop :=
  Runs m op input (fun run => ReturnsOutput run output)

end Wasm.StdioContract
