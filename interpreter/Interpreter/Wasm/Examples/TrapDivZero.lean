import Interpreter.Wasm.SmallStep

/-! ## Example: TrapDivZero

Conditional small-step semantics for `divU`: a zero divisor reaches a
structured terminal trap, while a nonzero divisor reaches normal completion.
-/

namespace Wasm
open SmallStep

def TrapDivZero : Program := [.localGet 0, .localGet 1, .divU]

def trapDivZeroModule : Module :=
  { funcs := [{
      params := [.i32, .i32]
      body := TrapDivZero
      results := [.i32] }] }

def trapDivZeroConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 a, .i32 b] }
        code := TrapDivZero
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := trapDivZeroModule, host := {} }], entry := ⟨0⟩ }
        wasm := trapDivZeroModule.initialStore } }

theorem trapDivZero_steps_success (a b : UInt32) (hb : b ≠ 0) :
    Steps (trapDivZeroConfig a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .divU), (.administrative .finish)]
      ⟨.done [.i32 (a / b)], (trapDivZeroConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.divU hb)
  exact Steps.cons .finish (Steps.refl _)

theorem trapDivZero_steps_trap (a : UInt32) :
    Steps (trapDivZeroConfig a 0)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .divU)]
      ⟨.trapped .integerDivideByZero, (trapDivZeroConfig a 0).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.cons .divUZero (Steps.refl _)

theorem trapDivZero_runs_success (a b : UInt32) (hb : b ≠ 0) :
    (runSteps 4 (trapDivZeroConfig a b)).result =
      .success [.i32 (a / b)] (trapDivZeroConfig a b).store :=
  runSteps_eq_success_of_steps (trapDivZero_steps_success a b hb)

theorem trapDivZero_runs_trap (a : UInt32) :
    (runSteps 3 (trapDivZeroConfig a 0)).result =
      .trapped .integerDivideByZero (trapDivZeroConfig a 0).store :=
  runSteps_finalConfig_of_steps (trapDivZero_steps_trap a)

/-- Fuel-free public trap specification. -/
theorem trapDivZero_traps (a : UInt32) :
    TrapsWith (trapDivZeroConfig a 0) .integerDivideByZero
      (fun store => store = (trapDivZeroConfig a 0).store) := by
  apply runSteps_trapped_trapsWith (trapDivZero_runs_trap a)
  rfl

theorem trapDivZeroSpec (a b : UInt32) (hb : b ≠ 0) :
    TerminatesWith (trapDivZeroConfig a b)
      (fun values _ => values = [.i32 (a / b)]) := by
  apply runSteps_success_terminates
  · exact trapDivZero_runs_success a b hb
  · rfl

theorem trapDivZero_partial (a b : UInt32) (hb : b ≠ 0) :
    PartiallyMeets (trapDivZeroConfig a b)
      (fun values _ => values = [.i32 (a / b)]) := by
  apply runSteps_success_partiallyMeets
  · exact trapDivZero_runs_success a b hb
  · rfl

end Wasm
