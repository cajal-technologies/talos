/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.SmallStep.Invariants
import Mathlib.Logic.Relation

/-!
# Labelled traces, weak steps, and executable iteration

The trace carrier is a free monoid of step labels.  External observations are
obtained by concatenating each label's observation list.  Administrative
closure is kept explicit so later block/call transitions can refine one old
macro-step by a stuttering sequence.
-/

namespace Wasm.SmallStep

/-- A finite relational execution whose labels are retained in order. -/
inductive Trace : Config α → List StepLabel → Config α → Prop where
  | refl (config) :
      Trace config [] config
  | cons {config out labels final}
      (head : Step config out)
      (tail : Trace out.next labels final) :
      Trace config (out.label :: labels) final

/-- Sequential composition of traces concatenates their label words. -/
theorem Trace.trans
    {config middle final : Config α} {labels₁ labels₂ : List StepLabel}
    (first : Trace config labels₁ middle)
    (second : Trace middle labels₂ final) :
    Trace config (labels₁ ++ labels₂) final := by
  induction first with
  | refl => simpa using second
  | cons head tail ih =>
      exact .cons head (ih second)

/-- External observations of a trace. -/
def externalObservations (labels : List StepLabel) : List WasmObservation :=
  labels.flatMap StepLabel.observations

@[simp]
theorem externalObservations_append (labels₁ labels₂ : List StepLabel) :
    externalObservations (labels₁ ++ labels₂) =
      externalObservations labels₁ ++ externalObservations labels₂ := by
  simp [externalObservations]

/-- Remove administrative labels while preserving every instruction label. -/
def eraseAdmin (labels : List StepLabel) : List StepLabel :=
  labels.filter fun label => label.kind == .instruction

@[simp]
theorem eraseAdmin_append (labels₁ labels₂ : List StepLabel) :
    eraseAdmin (labels₁ ++ labels₂) = eraseAdmin labels₁ ++ eraseAdmin labels₂ := by
  simp [eraseAdmin]

def AdministrativeStep (config config' : Config α) : Prop :=
  ∃ out,
    Step config out ∧
    out.label.kind = .administrative ∧
    out.next = config'

def InstructionStep (config config' : Config α) : Prop :=
  ∃ out,
    Step config out ∧
    out.label.kind = .instruction ∧
    out.next = config'

abbrev AdministrativeClosure (config config' : Config α) : Prop :=
  Relation.ReflTransGen AdministrativeStep config config'

/-- Silent administrative closure, one instruction transition, then silent
administrative closure. -/
def WeakStep (config config' : Config α) : Prop :=
  ∃ before after,
    AdministrativeClosure config before ∧
    InstructionStep before after ∧
    AdministrativeClosure after config'

theorem instruction_step_is_weak {config : Config α} {out : StepResult α}
    (hstep : Step config out)
    (hkind : out.label.kind = .instruction) :
    WeakStep config out.next := by
  refine ⟨config, out.next, .refl, ⟨out, hstep, hkind, rfl⟩, .refl⟩

theorem trace_externalObservations_empty
    {config final : Config α} {labels : List StepLabel}
    (htrace : Trace config labels final) :
    externalObservations labels = [] := by
  induction htrace with
  | refl => rfl
  | @cons config out labels final hstep tail ih =>
      change out.label.observations ++ externalObservations labels = []
      rw [step_observations_empty hstep]
      exact ih

theorem trace_admin_erasure_preserves_observations
    {config final : Config α} {labels : List StepLabel}
    (htrace : Trace config labels final) :
    externalObservations (eraseAdmin labels) =
      externalObservations labels := by
  induction htrace with
  | refl => rfl
  | @cons config out labels final hstep tail ih =>
      change
        List.flatMap StepLabel.observations
            (List.filter (fun label => label.kind == .instruction)
              (out.label :: labels)) =
          out.label.observations ++ externalObservations labels
      simp only [List.filter_cons]
      by_cases hkind : out.label.kind == .instruction
      · simp only [hkind, ↓reduceIte, List.flatMap_cons,
          step_observations_empty hstep, List.nil_append]
        simpa [eraseAdmin, externalObservations] using ih
      · simp only [Bool.not_eq_true] at hkind
        simp only [hkind, step_observations_empty hstep,
          List.nil_append]
        simpa [eraseAdmin, externalObservations] using ih

/-- Checked fuel-bounded execution.  `internalError` is diagnostic, never a
semantic `Expr`; it reports an unsupported or malformed running config. -/
inductive IterationResult (α : Type) where
  | done (values : List Value) (store : MachineStore α)
  | trapped (reason : TrapReason) (store : MachineStore α)
  | internalError (config : Config α)
  | outOfFuel (config : Config α)
deriving Repr

def IterationResult.config : IterationResult α → Config α
  | .done values store => { expr := .done values, store }
  | .trapped reason store => { expr := .trapped reason, store }
  | .internalError config | .outOfFuel config => config

def IterationResult.values? : IterationResult α → Option (List Value)
  | .done values _ => some values
  | _ => none

def IterationResult.trap? : IterationResult α → Option TrapReason
  | .trapped reason _ => some reason
  | _ => none

inductive IterationClass where
  | done
  | trapped
  | internalError
  | outOfFuel
deriving Repr, DecidableEq, BEq

def IterationResult.classification : IterationResult α → IterationClass
  | .done .. => .done
  | .trapped .. => .trapped
  | .internalError .. => .internalError
  | .outOfFuel .. => .outOfFuel

/-- Iterate the proved executable stepper.  Terminal configurations are
recognized before consuming fuel. -/
def runSteps : Nat → Config α → IterationResult α
  | _, { expr := .done values, store } => .done values store
  | _, { expr := .trapped reason, store } => .trapped reason store
  | 0, config@{ expr := .running _, .. } => .outOfFuel config
  | fuel + 1, config@{ expr := .running _, .. } =>
      match step? config with
      | none => .internalError config
      | some out => runSteps fuel out.next

@[simp]
theorem runSteps_done (fuel) (values : List Value) (store : MachineStore α) :
    runSteps fuel { expr := .done values, store } = .done values store := by
  cases fuel <;> rfl

@[simp]
theorem runSteps_trapped (fuel) (reason : TrapReason) (store : MachineStore α) :
    runSteps fuel { expr := .trapped reason, store } = .trapped reason store := by
  cases fuel <;> rfl

/-- `runSteps` is an action of additive fuel.  The only resumable result is
`outOfFuel`; success, trap, and diagnostic stuckness are absorbing. -/
theorem runSteps_add (fuel₁ fuel₂ : Nat) (config : Config α) :
    runSteps (fuel₁ + fuel₂) config =
      match runSteps fuel₁ config with
      | .outOfFuel config' => runSteps fuel₂ config'
      | result => result := by
  induction fuel₁ generalizing config with
  | zero =>
      cases config with
      | mk expr store =>
        cases expr <;> simp [runSteps]
  | succ fuel₁ ih =>
      cases config with
      | mk expr store =>
        cases expr with
        | done values => simp [runSteps]
        | trapped reason => simp [runSteps]
        | running thread =>
            let config : Config α := { expr := .running thread, store }
            cases hstep : step? config with
            | none =>
                simp [runSteps, config, hstep, Nat.succ_add]
            | some out =>
                simpa [runSteps, config, hstep, Nat.succ_add] using
                  ih (config := out.next)

/-- Once an iteration has produced any non-fuel result, increasing fuel leaves
the complete result—not merely its classification—unchanged. -/
theorem runSteps_fuel_mono
    {fuel₁ fuel₂ : Nat} {config : Config α}
    (hle : fuel₁ ≤ fuel₂)
    (hfinished :
      (runSteps fuel₁ config).classification ≠ .outOfFuel) :
    runSteps fuel₂ config = runSteps fuel₁ config := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [runSteps_add]
  generalize hresult : runSteps fuel₁ config = result
  cases result <;> simp_all [IterationResult.classification]

theorem runSteps_trace (fuel : Nat) (config : Config α) :
    ∃ labels,
      Trace config labels (runSteps fuel config).config := by
  induction fuel generalizing config with
  | zero =>
      cases config with
      | mk expr store =>
        cases expr <;> exact ⟨[], .refl _⟩
  | succ fuel ih =>
      cases config with
      | mk expr store =>
        cases expr with
        | done values => exact ⟨[], .refl _⟩
        | trapped reason => exact ⟨[], .refl _⟩
        | running thread =>
            let config : Config α := { expr := .running thread, store }
            cases hstep : step? config with
            | none =>
                refine ⟨[], ?_⟩
                simpa [runSteps, config, hstep, IterationResult.config] using
                  Trace.refl config
            | some out =>
                obtain ⟨labels, htrace⟩ := ih out.next
                refine ⟨out.label :: labels, ?_⟩
                simpa [runSteps, config, hstep, IterationResult.config] using
                  Trace.cons (step?_sound hstep) htrace

end Wasm.SmallStep
