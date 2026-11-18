import CodeLib.SepLogic.SmallStepOutcomeAdequacy

/-! Compile-time checks for the scoped outcome adapter and shared lifting. -/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

/-- A representative instruction rule is reused unchanged under the outcome
view; there is no outcome-specific copy of its body proof. -/
theorem twp_const_outcome [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)}
    {locals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {value : UInt32} :
    WP (.running ⟨{ locals with values := .i32 value :: locals.values },
      code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨locals, .const value :: code, arity, remainder, controls,
      calls⟩ : Expr α) @ s; E [{ Φ }] :=
  twp_const

end Wasm.SmallStep
