import Interpreter.Wasm.SmallStep

namespace Wasm
open SmallStep

def SelectMin : Program := [
  .nop, .nop,
  .localGet 0, .localGet 1,
  .localGet 0, .localGet 1, .ltU,
  .select,
  .const 42, .drop
]

def selectMinModule : Module :=
  { funcs := [{ params := [.i32, .i32], body := SelectMin, results := [.i32] }] }

def selectMinConfig (x y : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x, .i32 y] }
        code := SelectMin
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := selectMinModule, host := {} }], entry := ⟨0⟩ }
        wasm := selectMinModule.initialStore } }

theorem selectMin_runs (x y : UInt32) :
    (runSteps 11 (selectMinConfig x y)).result.values? =
      some [.i32 (if x < y then x else y)] := by
  have hsteps : Steps (selectMinConfig x y)
      [(.instruction .nop), (.instruction .nop),
       (.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .ltU), (.instruction .select),
       (.instruction (.const 42)), (.instruction .drop),
       (.administrative .finish)]
      ⟨.done [.i32 (if x < y then x else y)], (selectMinConfig x y).store⟩ := by
    apply Steps.cons .nop
    apply Steps.cons .nop
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.ltU rfl)
    apply Steps.cons (.select rfl)
    apply Steps.cons .const
    apply Steps.cons .drop
    apply Steps.cons .finish
    by_cases h : x < y <;> simp [h]
    all_goals exact Steps.refl _
  exact congrArg RunnerResult.values? (runSteps_eq_success_of_steps hsteps)

theorem selectMinSpec (x y : UInt32) :
    TerminatesWith (selectMinConfig x y)
      (fun values _ => values = [.i32 (if x < y then x else y)]) :=
  runSteps_values_terminates (selectMin_runs x y)

theorem selectMin_partial (x y : UInt32) :
    PartiallyMeets (selectMinConfig x y)
      (fun values _ => values = [.i32 (if x < y then x else y)]) :=
  runSteps_values_partiallyMeets (selectMin_runs x y)

end Wasm
