import Interpreter.Wasm.SmallStep

namespace Wasm
open SmallStep

def SelectAbs : Program := [
  .const 0, .localGet 0, .sub,
  .localGet 0,
  .localGet 0, .const 0, .ltS,
  .select
]

def selectAbsModule : Module :=
  { funcs := [{ params := [.i32], body := SelectAbs, results := [.i32] }] }

def selectAbsConfig (n : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 n] }
        code := SelectAbs
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { module := selectAbsModule, host := {} }
        wasm := selectAbsModule.initialStore } }

def selectAbsResult (n : UInt32) : UInt32 :=
  if n.toInt32 < 0 then 0 - n else n

theorem selectAbs_runs (n : UInt32) :
    (runSteps 9 (selectAbsConfig n)).result.values? =
      some [.i32 (selectAbsResult n)] := by
  have hsteps : Steps (selectAbsConfig n)
      [(.instruction (.const 0)), (.instruction (.localGet 0)), (.instruction .sub),
       (.instruction (.localGet 0)), (.instruction (.localGet 0)), (.instruction (.const 0)),
       (.instruction .ltS), (.instruction .select), (.administrative .finish)]
      ⟨.done [.i32 (selectAbsResult n)], (selectAbsConfig n).store⟩ := by
    apply Steps.cons .const
    apply Steps.cons (.localGet rfl)
    apply Steps.cons .sub
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.localGet rfl)
    apply Steps.cons .const
    apply Steps.cons (.ltS rfl)
    apply Steps.cons (.select rfl)
    apply Steps.cons .finish
    by_cases h : n.toInt32 < 0 <;> simp [selectAbsResult, h]
    all_goals exact Steps.refl _
  exact congrArg RunnerResult.values? (runSteps_eq_success_of_steps hsteps)

theorem selectAbsSpec (n : UInt32) :
    TerminatesWith (selectAbsConfig n)
      (fun values _ => values = [.i32 (selectAbsResult n)]) :=
  runSteps_values_terminates (selectAbs_runs n)

theorem selectAbs_partial (n : UInt32) :
    PartiallyMeets (selectAbsConfig n)
      (fun values _ => values = [.i32 (selectAbsResult n)]) :=
  runSteps_values_partiallyMeets (selectAbs_runs n)

end Wasm
