import Interpreter.Wasm.SmallStep

/-! ## Example: EarlyBr

A top-level `br 0` targets the implicit function label. The relational trace
shows the branch discarding the remaining code and reaching normal completion.
-/

namespace Wasm
open SmallStep

def EarlyBr : Program := [.localGet 0, .br 0]

def earlyBrModule : Module :=
  { funcs := [{ params := [.i32], results := [.i32], body := EarlyBr }] }

def earlyBrConfig (x : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x] }
        code := EarlyBr
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := earlyBrModule, host := {} }], entry := ⟨0⟩ }
        wasm := earlyBrModule.initialStore } }

theorem earlyBr_steps (x : UInt32) :
    Steps (earlyBrConfig x)
      [(.instruction (.localGet 0)), (.instruction (.br 0)),
       (.administrative .finish)]
      ⟨.done [.i32 x], (earlyBrConfig x).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.br rfl)
  exact Steps.cons .finish (Steps.refl _)

theorem earlyBr_runs (x : UInt32) :
    (runSteps 3 (earlyBrConfig x)).result.values? = some [.i32 x] :=
  congrArg RunnerResult.values?
    (runSteps_eq_success_of_steps (earlyBr_steps x))

theorem earlyBrSpec (x : UInt32) :
    TerminatesWith (earlyBrConfig x)
      (fun values _ => values = [.i32 x]) :=
  runSteps_values_terminates (earlyBr_runs x)

theorem earlyBr_partial (x : UInt32) :
    PartiallyMeets (earlyBrConfig x)
      (fun values _ => values = [.i32 x]) :=
  runSteps_values_partiallyMeets (earlyBr_runs x)

end Wasm
