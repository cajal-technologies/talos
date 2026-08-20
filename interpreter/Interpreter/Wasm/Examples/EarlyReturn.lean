import Interpreter.Wasm.SmallStep

/-! ## Example: EarlyReturn

An explicit return inside nested blocks reaches function completion directly;
the block continuations and all following instructions are dead.
-/

namespace Wasm
open SmallStep

def EarlyReturn : Program := [
  .block 0 0 [
    .block 0 0 [
      .localGet 0, .ret
    ],
    .const 999
  ],
  .const 888
]

def earlyReturnModule : Module :=
  { funcs := [{
      params := [.i32]
      results := [.i32]
      body := EarlyReturn }] }

def earlyReturnConfig (x : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x] }
        code := EarlyReturn
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := earlyReturnModule, host := {} }], entry := ⟨0⟩ }
        wasm := earlyReturnModule.initialStore } }

theorem earlyReturn_steps (x : UInt32) :
    Steps (earlyReturnConfig x)
      [(.instruction (.block 0 0 [
          .block 0 0 [.localGet 0, .ret], .const 999])),
       (.instruction (.block 0 0 [.localGet 0, .ret])),
       (.instruction (.localGet 0)),
       (.administrative .returnFromFunction)]
      ⟨.done [.i32 x], (earlyReturnConfig x).store⟩ := by
  apply Steps.cons .block
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  exact Steps.cons .returnFromFunction (Steps.refl _)

theorem earlyReturn_runs (x : UInt32) :
    (runSteps 4 (earlyReturnConfig x)).result.values? = some [.i32 x] :=
  congrArg RunnerResult.values?
    (runSteps_eq_success_of_steps (earlyReturn_steps x))

theorem earlyReturnSpec (x : UInt32) :
    TerminatesWith (earlyReturnConfig x)
      (fun values _ => values = [.i32 x]) :=
  runSteps_values_terminates (earlyReturn_runs x)

theorem earlyReturn_partial (x : UInt32) :
    PartiallyMeets (earlyReturnConfig x)
      (fun values _ => values = [.i32 x]) :=
  runSteps_values_partiallyMeets (earlyReturn_runs x)

end Wasm
