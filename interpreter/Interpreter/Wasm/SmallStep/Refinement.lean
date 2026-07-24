/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.SmallStep.Trace
import Batteries.Data.UInt

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
  | addI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | subI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | mulI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | leSI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | eqI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | neI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | eqzI64 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]
  | extendUI32 =>
      simp only [ofOld, step?, execOne]
      split <;> simp_all [liftOldContinuation]

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

/-- Interpret an old whole-program continuation as a checked small-step
iteration result.  Unsupported old outcomes remain outside the refinement
claim rather than being collapsed into traps or diagnostics. -/
def liftOldProgramContinuation (runtime : RuntimeEnv) :
    Continuation α → Option (IterationResult α)
  | .Fallthrough store frame =>
      some <| .done frame.values { runtime, physical := store }
  | .Trap store reason =>
      if reason = "integer divide by zero" then
        some <| .trapped .integerDivideByZero { runtime, physical := store }
      else
        none
  | _ => none

private theorem runSteps_agrees_exec_cons_fallthrough
    (runtime : RuntimeEnv) (module : Module) (store : Store α)
    (frame frame' : Locals) (inst : Instruction) (rest : Program)
    (env : HostEnv α)
    (hstep :
      step? (ofOld runtime store frame (inst :: rest)) =
        some (instructionResult { runtime, physical := store } frame' rest))
    (hold :
      execOne 1 module store frame inst env = .Fallthrough store frame')
    (ih :
      some (runSteps (rest.length + 1) (ofOld runtime store frame' rest)) =
        liftOldProgramContinuation runtime
          (exec 1 module store frame' rest env)) :
    some
        (runSteps ((inst :: rest).length + 1)
          (ofOld runtime store frame (inst :: rest))) =
      liftOldProgramContinuation runtime
        (exec 1 module store frame (inst :: rest) env) := by
  simp only [List.length_cons]
  change
    some
        (runSteps (Nat.succ (rest.length + 1))
          (ofOld runtime store frame (inst :: rest))) =
      liftOldProgramContinuation runtime
        (exec 1 module store frame (inst :: rest) env)
  have hstep' :
      step?
          { expr := .running { frame, code := inst :: rest }
            store := { runtime, physical := store } } =
        some (instructionResult { runtime, physical := store } frame' rest) := by
    simpa only [ofOld] using hstep
  simp only [ofOld]
  simp only [runSteps]
  rw [hstep', exec, hold]
  simpa [instructionResult, nextConfig, ofOld] using ih

/-- Exact whole-program refinement for the complete well-formed pure-core
slice.  One unit of runner fuel is used per instruction and one final unit
performs the administrative transition to `done`. -/
theorem runSteps_agrees_exec
    (runtime : RuntimeEnv) (module : Module) (store : Store α)
    (frame : Locals) (code : Program) (env : HostEnv α)
    (hwf : FrameProgramWellFormed frame code) :
    some (runSteps (code.length + 1) (ofOld runtime store frame code)) =
      liftOldProgramContinuation runtime
        (exec 1 module store frame code env) := by
  induction hwf with
  | finish =>
      simp [runSteps, ofOld, step?, exec, liftOldProgramContinuation]
  | localGet frame rest i v hget hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := v :: frame.values } (.localGet i) rest env
      · exact step?_complete (.localGet _ _ _ _ _ hget)
      · simp only [execOne.eq_def, hget]
      · exact ih
  | localSet frame rest i v vs frame' hvalues hset hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame' with values := vs } (.localSet i) rest env
      · exact step?_complete (.localSet _ _ _ _ _ _ _ hvalues hset)
      · simp only [execOne.eq_def, hvalues, hset]
      · exact ih
  | const frame rest v hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 v :: frame.values } (.const v) rest env
      · exact step?_complete (.const _ _ _ _)
      · simp only [execOne.eq_def]
      · exact ih
  | constI64 frame rest v hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i64 v :: frame.values } (.constI64 v) rest env
      · exact step?_complete (.constI64 _ _ _ _)
      · simp only [execOne.eq_def]
      · exact ih
  | add frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (a + b) :: vs } .add rest env
      · exact step?_complete (.add _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | sub frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (b - a) :: vs } .sub rest env
      · exact step?_complete (.sub _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | mul frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (a * b) :: vs } .mul rest env
      · exact step?_complete (.mul _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | divU frame rest a b vs hvalues hnz hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (a / b) :: vs } .divU rest env
      · exact step?_complete (.divU _ _ _ _ _ _ hvalues hnz)
      · simp only [execOne.eq_def, hvalues, if_neg hnz]
      · exact ih
  | divUTrap frame rest a vs hvalues =>
      simp [runSteps, ofOld, step?, exec, execOne, hvalues,
        trapResult, liftOldProgramContinuation]
  | addI64 frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i64 (a + b) :: vs } .addI64 rest env
      · exact step?_complete (.addI64 _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | subI64 frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i64 (a - b) :: vs } .subI64 rest env
      · exact step?_complete (.subI64 _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | mulI64 frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i64 (a * b) :: vs } .mulI64 rest env
      · exact step?_complete (.mulI64 _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | leSI64 frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values :=
              Value.i32 (if a.toInt64 ≤ b.toInt64 then 1 else 0) :: vs }
          .leSI64 rest env
      · exact step?_complete (.leSI64 _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | eqI64 frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (if a = b then 1 else 0) :: vs }
          .eqI64 rest env
      · exact step?_complete (.eqI64 _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | neI64 frame rest a b vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (if a = b then 0 else 1) :: vs }
          .neI64 rest env
      · exact step?_complete (.neI64 _ _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues, ne_eq, ite_not]
      · exact ih
  | eqzI64 frame rest a vs hvalues hnext ih =>
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i32 (if a = 0 then 1 else 0) :: vs }
          .eqzI64 rest env
      · exact step?_complete (.eqzI64 _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues]
      · exact ih
  | extendUI32 frame rest a vs hvalues hnext ih =>
      have hext : UInt64.ofNat a.toNat = a.toUInt64 := by
        apply UInt64.ext
        simp
      apply runSteps_agrees_exec_cons_fallthrough
          runtime module store frame
          { frame with values := .i64 a.toUInt64 :: vs }
          .extendUI32 rest env
      · exact step?_complete (.extendUI32 _ _ _ _ _ hvalues)
      · simp only [execOne.eq_def, hvalues, hext]
      · exact ih

end Wasm.SmallStep
