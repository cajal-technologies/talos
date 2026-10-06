import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Host.Universal
import Std.Data.HashSet

/-!
# Running a configuration for testing

`SmallStep.runSteps` records the full step trace and recurses once per step, so
a long execution exhausts the native stack. `run` performs the same transitions
tail-recursively, keeping only a step count and the set of function indices the
execution entered (direct, tail and indirect calls, plus host calls).
`run_result` shows the two agree on the `RunnerResult`, so every verdict below
is a verdict about `runSteps`.
-/

namespace Wasm.SpecTest

open SmallStep

/-- The function index a configuration is about to enter, when its next
instruction is a call whose target can be read off the configuration: the
immediate of `call`/`return_call`, or the table entry selected by the operand on
top of the stack for `call_indirect`/`return_call_indirect`. -/
def nextCallee (config : Config α) : Option Nat :=
  match config.expr with
  | .running thread =>
    match thread.code with
    | .call index :: _ => some index
    | .returnCall index :: _ => some index
    | .callIndirect _ tableIndex :: _ => indirectCallee config thread tableIndex
    | .returnCallIndirect _ tableIndex :: _ => indirectCallee config thread tableIndex
    | _ => none
  | _ => none
where
  indirectCallee (config : Config α) (thread : ThreadState α) (tableIndex : Nat) : Option Nat :=
    match thread.locals.values with
    | selector :: _ =>
      match selector.addrNat?, config.store.wasm.tables[tableIndex]? with
      | some element, some table =>
        match table[element]? with
        | some (.funcref (some index)) => some index
        | _ => none
      | _, _ => none
    | [] => none

/-- Record the callee the next step enters, if any. -/
def noteCallee (config : Config α) (seen : Std.HashSet Nat) : Std.HashSet Nat :=
  match nextCallee config with
  | some index => seen.insert index
  | none => seen

/-- Record a host function the step invoked. -/
def noteStep (kind : StepKind) (seen : Std.HashSet Nat) : Std.HashSet Nat :=
  match kind with
  | .host index => seen.insert index
  | _ => seen

/-- `runSteps` without the trace: the result, the number of steps taken, and
the function indices entered. Tail-recursive, so it runs in constant stack. -/
def run : Nat → Config α → Nat → Std.HashSet Nat →
    RunnerResult α × Nat × Std.HashSet Nat
  | 0, config, steps, seen =>
    match config.expr with
    | .done values => (.success values config.store, steps, seen)
    | .trapped reason => (.trapped reason config.store, steps, seen)
    | .running _ => (.outOfFuel config, steps, seen)
  | fuel + 1, config, steps, seen =>
    match config.expr with
    | .done values => (.success values config.store, steps, seen)
    | .trapped reason => (.trapped reason config.store, steps, seen)
    | .running _ =>
      match stepChecked? config with
      | .error error => (.internalError error config, steps, seen)
      | .ok none =>
        (.internalError ⟨"running configuration has no successor"⟩ config, steps, seen)
      | .ok (some (kind, next)) =>
        run fuel next (steps + 1) (noteStep kind (noteCallee config seen))

/-- `run` returns exactly the result of `runSteps` with the same fuel. -/
theorem run_result (fuel : Nat) (config : Config α) (steps : Nat)
    (seen : Std.HashSet Nat) :
    (run fuel config steps seen).1 = (runSteps fuel config).result := by
  induction fuel generalizing config steps seen with
  | zero =>
    rcases config with ⟨expr, store⟩
    cases expr <;> rfl
  | succ fuel ih =>
    rcases config with ⟨expr, store⟩
    cases expr with
    | done values => rfl
    | trapped reason => rfl
    | running thread =>
      cases h : stepChecked? ⟨.running thread, store⟩ with
      | error error => simp [run, runSteps, h]
      | ok step =>
        cases step with
        | none => simp [run, runSteps, h]
        | some pair =>
          obtain ⟨kind, next⟩ := pair
          simp [run, runSteps, h, ih]

/-- How a bounded execution ended. -/
inductive Termination where
  | done (values : List Value)
  | trapped (reason : TrapReason)
  | outOfFuel
  | internalError (message : String)

/-- Everything a test observes about one execution under the universal host. -/
structure Observation where
  termination : Termination
  /-- Bytes written to standard output by the end of the run. -/
  output : List UInt8
  /-- The OOM host's typed marker in the final state. -/
  oomRaised : Bool
  steps : Nat
  /-- Function indices entered, in increasing order. -/
  functions : List Nat

/-- Run `config` for at most `fuel` steps and record what is observable.
`entry` seeds the coverage set with the function a start configuration enters
directly (rather than through a `call`). -/
def observe (fuel : Nat) (config : Config Universal.State) (entry : Option Nat) :
    Observation :=
  let initial : Std.HashSet Nat :=
    match entry with
    | some index => ({} : Std.HashSet Nat).insert index
    | none => {}
  let (result, steps, seen) := run fuel config 0 initial
  let functions := seen.toList.mergeSort (fun a b => decide (a ≤ b))
  let final (store : MachineStore Universal.State) (termination : Termination) :
      Observation :=
    { termination
      output := store.wasm.host.stdio.output
      oomRaised := store.wasm.host.oom.raised
      steps, functions }
  match result with
  | .success values store => final store (.done values)
  | .trapped reason store => final store (.trapped reason)
  | .outOfFuel config => final config.store .outOfFuel
  | .internalError error config => final config.store (.internalError error.message)

end Wasm.SpecTest
