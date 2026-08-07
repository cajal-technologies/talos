import Iris.ProgramLogic.Language
import Interpreter.Wasm.SmallStep

/-!
# iris-lean language adapter for the Wasm small-step machine

This is deliberately a thin adapter: the semantic transition remains
`Wasm.SmallStep.Step`, and WebAssembly does not fork Iris threads.

Iris observations are empty because iris-lean's total weakest precondition
accepts only silent reductions. The authoritative Talos `Step` relation still
carries every instruction/administrative/host `StepKind`, so this does not
erase labels from the Wasm semantics or its `Steps` traces.
-/

namespace Wasm.SmallStep

open Iris.ProgramLogic
open Language.Notation

instance instToVal : ToVal (Expr α) (List Value) where
  toVal
    | .done values => some values
    | .running _ | .trapped _ => none
  ofVal := .done
  coe_of_toVal_eq_some := by
    intro e values h
    cases e <;> simp_all
  toVal_coe := by simp

instance instPrimStep :
    PrimStep (Expr α) (MachineStore α) (List StepKind) where
  primStep source observation target :=
    target.2.2 = [] ∧
    ∃ kind,
      observation = [] ∧
      Step ⟨source.1, source.2⟩ kind ⟨target.1, target.2.1⟩

instance instLanguage :
    Language (Expr α) (MachineStore α) StepKind (List Value) where
  val_stuck := by
    intro e store observation e' store' forks h
    rcases h with ⟨rfl, kind, rfl, hstep⟩
    cases e with
    | running => rfl
    | done values => exact False.elim (done_terminal hstep)
    | trapped => rfl

@[simp] theorem primStep_no_forks
    {source : Expr α × MachineStore α} {observation : List StepKind}
    {target : Expr α × MachineStore α × List (Expr α)}
    (h : PrimStep.primStep source observation target) :
    target.2.2 = [] :=
  h.1

theorem primStep_iff
    {e e' : Expr α} {store store' : MachineStore α}
    {observation : List StepKind} {forks} :
    Iff (PrimStep.primStep (e, store) observation (e', store', forks))
      (forks = [] ∧ ∃ kind, observation = [] ∧
        Step ⟨e, store⟩ kind ⟨e', store'⟩) :=
  Iff.rfl

/-- A Talos relational trace induces a silent iris-lean thread-pool trace with
a single expression and no forks. Step labels remain in the Talos trace. -/
theorem Steps.to_languageNSteps
    (steps : Steps config trace final) :
    Language.NSteps trace.length
      ([config.expr], config.store) []
      ([final.expr], final.store) := by
  induction steps with
  | refl config =>
    exact .refl ([config.expr], config.store)
  | @cons config kind next trace final head tail ih =>
    apply Language.NSteps.cons
      (ρ₂ := ([next.expr], next.store))
      (obs := []) (obs' := [])
    · apply Language.Step.atomic
        (eₜ := []) (t₁ := []) (t₂ := [])
      exact ⟨rfl, kind, rfl, head⟩
    · exact ih

/-- Observation-erased iris-lean reachability induced by a Talos trace. -/
theorem Steps.to_languageErasedSteps
    (steps : Steps config trace final) :
    ([config.expr], config.store) -·->ₜₚ*
      ([final.expr], final.store) :=
  (Language.erasedStep_nSteps _ _).mpr
    ⟨trace.length, [], steps.to_languageNSteps⟩

end Wasm.SmallStep
