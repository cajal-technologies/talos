import CodeLib.SepLogic.SmallStepState

/-!
# Outcome-valued Wasm language adapter

The existing Wasm Iris adapter observes only normal results.  This file adds
an opt-in terminal view that observes both normal completion and traps while
reusing the same authoritative `Wasm.SmallStep.Step` relation and state
interpretation.  Open `Wasm.SmallStep.Outcome` only around specifications that
need to distinguish those outcomes.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

@[implicit_reducible] def outcomeToVal :
    ToVal (Expr α) ObservableOutcome where
  toVal
    | .done values => some (.done values)
    | .trapped reason => some (.trapped reason)
    | .running _ => none
  ofVal := ObservableOutcome.toExpr
  coe_of_toVal_eq_some := by
    intro e outcome h
    cases e <;> cases outcome <;>
      simp_all [ObservableOutcome.toExpr]
  toVal_coe := by
    intro outcome
    cases outcome <;> rfl

/-- The outcome adapter changes only terminal observations. Primitive steps
remain definitionally the canonical Wasm `instPrimStep`. -/
@[implicit_reducible] def outcomeLanguage :
    Language (Expr α) (MachineStore α) StepKind ObservableOutcome where
  toToVal := outcomeToVal
  toPrimStep := instPrimStep
  val_stuck := by
    intro e store observation e' store' forks h
    rcases h with ⟨rfl, kind, rfl, hstep⟩
    cases e with
    | running => rfl
    | done values => exact False.elim (done_terminal hstep)
    | trapped reason => exact False.elim (trapped_terminal hstep)

@[implicit_reducible] def outcomeTerminalView :
    TerminalView α ObservableOutcome where
  language := outcomeLanguage
  primStep_eq := rfl
  running_not_val _ := rfl

namespace Outcome

scoped instance (priority := high) instTerminalView :
    TerminalView α ObservableOutcome :=
  outcomeTerminalView

scoped instance (priority := high) instLanguage :
    Language (Expr α) (MachineStore α) StepKind ObservableOutcome :=
  outcomeLanguage

/-- Outcome-valued Iris adapter over the same Wasm ghost state. -/
scoped instance (priority := high) instIrisGS [WasmSmallStepGS hlc α] :
    @IrisGS_gen hlc (Expr α) ObservableOutcome (MachineStore α) StepKind
      instLanguage (WasmHeapGF α) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end Outcome

end Wasm.SmallStep
