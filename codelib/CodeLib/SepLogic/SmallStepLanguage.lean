/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.SmallStep.Refinement
import Iris.ProgramLogic.Language

/-!
# iris-lean language adapter for the labelled Wasm small-step kernel

This file contains no transition cases.  `PrimStep` is definitionally an
existential projection of `Wasm.SmallStep.Step`, including observations and
spawned expressions.
-/

namespace Wasm.SmallStep.Iris

open Iris.ProgramLogic

/-- A transparent host-typed wrapper.  `Language` declares its state as an
`outParam`, so the host-state type must be recoverable from the expression
type rather than only from `MachineStore α`. -/
@[ext]
structure IrisExpr (α : Type) where
  toExpr : Expr
deriving Repr

instance instToVal : ToVal (IrisExpr α) (List Value) where
  toVal
    | ⟨.done values⟩ => some values
    | ⟨_⟩ => none
  ofVal values := ⟨.done values⟩
  coe_of_toVal_eq_some := by
    intro expr value h
    rcases expr with ⟨expr⟩
    cases expr <;> simp_all
  toVal_coe _ := rfl

instance instPrimStep :
    PrimStep (IrisExpr α) (MachineStore α) (List WasmObservation) where
  primStep
    | ⟨expr, store⟩, observations, ⟨expr', store', spawned⟩ =>
        ∃ kind,
          Step
            { expr := expr.toExpr, store }
            { label := { kind, observations }
              next := { expr := expr'.toExpr, store := store' }
              spawned := spawned.map IrisExpr.toExpr }

theorem primStep_iff
    {expr expr' : IrisExpr α} {store store' : MachineStore α}
    {observations : List WasmObservation} {spawned : List (IrisExpr α)} :
    Iff
      (PrimStep.primStep
        (expr, store) observations (expr', store', spawned))
      (∃ kind,
        Step
          { expr := expr.toExpr, store }
          { label := { kind, observations }
            next := { expr := expr'.toExpr, store := store' }
            spawned := spawned.map IrisExpr.toExpr }) :=
  Iff.rfl

instance instLanguage :
    Language (IrisExpr α) (MachineStore α) WasmObservation (List Value) where
  val_stuck {expr} {store} {obs} {expr'} {store'} {spawned} hstep := by
    rcases expr with ⟨expr⟩
    cases expr with
      | running thread => rfl
      | trapped reason => rfl
      | done values =>
          exfalso
          rcases hstep with ⟨kind, hstep⟩
          exact terminal_no_step
            (config := { expr := .done values, store }) trivial ⟨_, hstep⟩

end Wasm.SmallStep.Iris
