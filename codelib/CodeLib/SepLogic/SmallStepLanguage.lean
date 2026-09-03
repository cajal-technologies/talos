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

set_option hygiene false in
/-- Unpack an Iris primitive step and identify its target using determinism of
the authoritative Wasm step relation. -/
macro "wasm_wp_resolve_step " h:term " using " expected:term : tactic =>
  `(tactic| (obtain ⟨rfl, kind, rfl, wasmStep⟩ := $h) <;>
    (obtain ⟨rfl, hconfig⟩ := step_deterministic ($expected) wasmStep) <;>
    cases hconfig)

/-- A terminal observation for the Wasm machine.  Its language must reuse the
authoritative Wasm primitive-step relation; only the terminal-value view may
change. -/
class TerminalView (α : Type) (Terminal : outParam Type) where
  language : Language (Expr α) (MachineStore α) StepKind Terminal
  primStep_eq : language.toPrimStep = instPrimStep
  running_not_val (thread : ThreadState α) :
    @toVal (Expr α) Terminal language.toToVal
      (Expr.running thread : Expr α) = none

/-- Repackage a terminal view with the canonical Wasm primitive-step
instance.  This keeps primitive reductions definitionally transparent to the
shared lifting proofs. -/
@[implicit_reducible] def TerminalView.canonicalLanguage
    [view : TerminalView α Terminal] :
    Language (Expr α) (MachineStore α) StepKind Terminal where
  toToVal := view.language.toToVal
  toPrimStep := instPrimStep
  val_stuck := by
    intro e store observation e' store' forks hstep
    apply @Language.val_stuck (Expr α) (MachineStore α) StepKind Terminal
      view.language e store observation e' store' forks
    rw [view.primStep_eq]
    exact hstep

instance instTerminalView : TerminalView α (List Value) where
  language := instLanguage
  primStep_eq := rfl
  running_not_val _ := rfl

section terminalGeneric

variable {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) traceTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

/-- A Talos relational trace induces a silent iris-lean thread-pool trace with
a single expression and no forks. Step labels remain in the Talos trace. -/
theorem Steps.to_languageNSteps
    {config final : Config α} {trace : List StepKind}
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
    {config final : Config α} {trace : List StepKind}
    (steps : Steps config trace final) :
    ([config.expr], config.store) -·->ₜₚ*
      ([final.expr], final.store) :=
  (Language.erasedStep_nSteps _ _).mpr
    ⟨trace.length, [], steps.to_languageNSteps⟩

end terminalGeneric

end Wasm.SmallStep
