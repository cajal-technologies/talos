/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.SmallStep.Trace

/-!
# Exact one-instruction refinement of the old interpreter

For the pure-core fragment, one old `execOne` macro-step is already one new
instruction step.  The exact correspondence below is stronger than the weak
simulation needed once administrative control-flow transitions arrive; the
corresponding new step is embedded into `WeakStep` by reflexive
administrative closures.
-/

namespace Wasm.SmallStep

/-- Embed an old `(Store, Locals, Program)` state into the new machine.  The
runtime environment is explicit and is not recovered by choice. -/
def ofOld (runtime : RuntimeEnv) (store : Store α) (frame : Locals)
    (code : Program) : Config α :=
  { expr := .running { frame, code }
    store := { runtime, physical := store } }

/-- Interpret the old one-instruction outcome as a new labelled result.
`Invalid`, control transfer, and fuel exhaustion have no semantic successor in
the pure-core fragment. -/
def liftOldContinuation (runtime : RuntimeEnv) (rest : Program) :
    Continuation α → Option (StepResult α)
  | .Fallthrough store frame =>
      some <| instructionResult { runtime, physical := store } frame rest
  | .Trap store "integer divide by zero" =>
      some <| trapResult { runtime, physical := store } .integerDivideByZero
  | _ => none

/-- Exact executable correspondence on the migrated instruction family.  It
also checks the invalid boundary: a malformed old instruction result maps to
`none`, rather than becoming a semantic trap. -/
theorem step?_agrees_execOne
    (runtime : RuntimeEnv) (module : Module) (store : Store α)
    (frame : Locals) (rest : Program) (env : HostEnv α)
    {inst : Instruction} (hpure : PureCoreInstruction inst) :
    step? (ofOld runtime store frame (inst :: rest)) =
      liftOldContinuation runtime rest
        (execOne 1 module store frame inst env) := by
  cases hpure with
  | localGet i =>
      simp only [ofOld, step?, execOne, liftOldContinuation]
      cases frame.get i <;> rfl
  | localSet i =>
      simp only [ofOld, step?, execOne]
      cases hvalues : frame.values with
      | nil => simp [liftOldContinuation]
      | cons v vs =>
          simp only [Locals.set?]
          split
          · rfl
          · split <;> rfl
  | const v =>
      simp [ofOld, step?, execOne, liftOldContinuation]
  | constI64 v =>
      simp [ofOld, step?, execOne, liftOldContinuation]
  | add =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | sub =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | mul =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | divU =>
      simp only [ofOld, step?, execOne]
      split
      · split <;> simp_all [liftOldContinuation]
      · simp_all [liftOldContinuation]

/-- Relational forward direction of `step?_agrees_execOne`. -/
theorem pureCore_execOne_to_step
    (runtime : RuntimeEnv) (module : Module) (store : Store α)
    (frame : Locals) (rest : Program) (env : HostEnv α)
    {inst : Instruction} (hpure : PureCoreInstruction inst)
    {out : StepResult α}
    (hold :
      liftOldContinuation runtime rest
        (execOne 1 module store frame inst env) = some out) :
    Step (ofOld runtime store frame (inst :: rest)) out := by
  apply step?_sound
  rw [step?_agrees_execOne runtime module store frame rest env hpure]
  exact hold

/-- The exact step is, in particular, the weak/stuttering step required by
the migration architecture. -/
theorem pureCore_execOne_to_weakStep
    (runtime : RuntimeEnv) (module : Module) (store : Store α)
    (frame : Locals) (rest : Program) (env : HostEnv α)
    {inst : Instruction} (hpure : PureCoreInstruction inst)
    {out : StepResult α}
    (hold :
      liftOldContinuation runtime rest
        (execOne 1 module store frame inst env) = some out) :
    WeakStep (ofOld runtime store frame (inst :: rest)) out.next := by
  have hstep :=
    pureCore_execOne_to_step runtime module store frame rest env hpure hold
  exact instruction_step_is_weak hstep (instruction_head_step_kind hstep)

/-- Reverse executable correspondence: every new relational transition from
the pure-core head is exactly the lifted old `execOne` result. -/
theorem pureCore_step_to_execOne
    (runtime : RuntimeEnv) (module : Module) (store : Store α)
    (frame : Locals) (rest : Program) (env : HostEnv α)
    {inst : Instruction} (hpure : PureCoreInstruction inst)
    {out : StepResult α}
    (hstep : Step (ofOld runtime store frame (inst :: rest)) out) :
    liftOldContinuation runtime rest
        (execOne 1 module store frame inst env) = some out := by
  rw [← step?_agrees_execOne runtime module store frame rest env hpure]
  exact step?_complete hstep

end Wasm.SmallStep
