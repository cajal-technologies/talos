import Interpreter.Wasm.SmallStep

/-! ## Example: IfAbs

Signed absolute value via `if`. Both branches are represented by explicit
small-step traces, including the administrative control-frame exit.
-/

namespace Wasm
open SmallStep

def IfAbs : Program := [
  .localGet 0, .const 0, .ltS,
  .iff 0 1
    [.const 0, .localGet 0, .sub]
    [.localGet 0]
]

def ifAbsModule : Module :=
  { funcs := [{ params := [.i32], results := [.i32], body := IfAbs }] }

def ifAbsConfig (x : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x] }
        code := IfAbs
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := ifAbsModule, host := {} }], entry := ⟨0⟩ }
        wasm := ifAbsModule.initialStore } }

def ifAbsResult (x : UInt32) : UInt32 :=
  if x.toInt32 < (0 : UInt32).toInt32 then 0 - x else x

def ifAbsTrace (x : UInt32) : List StepKind :=
  [(.instruction (.localGet 0)), (.instruction (.const 0)),
   (.instruction .ltS),
   (.instruction (.iff 0 1
      [.const 0, .localGet 0, .sub] [.localGet 0]))] ++
  (if x.toInt32 < (0 : UInt32).toInt32 then
    [(.instruction (.const 0)), (.instruction (.localGet 0)),
     (.instruction .sub)]
   else
    [(.instruction (.localGet 0))]) ++
  [(.administrative .exitControl), (.administrative .finish)]

theorem ifAbs_steps (x : UInt32) :
    Steps (ifAbsConfig x) (ifAbsTrace x)
      ⟨.done [.i32 (ifAbsResult x)], (ifAbsConfig x).store⟩ := by
  unfold ifAbsTrace
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons (.ltS rfl)
  apply Steps.cons (.iff rfl)
  by_cases hneg : x.toInt32 < (0 : UInt32).toInt32
  · have hneg' : x.toInt32 < 0 := by simpa using hneg
    simp only [if_pos hneg]
    apply Steps.cons .const
    apply Steps.cons (.localGet rfl)
    apply Steps.cons .sub
    apply Steps.cons (.exitControl rfl)
    apply Steps.cons .finish
    simpa [ifAbsConfig, ifAbsResult, hneg, hneg'] using
      (Steps.refl
        (⟨.done [.i32 (0 - x)], (ifAbsConfig x).store⟩ : Config Unit))
  · have hneg' : ¬x.toInt32 < 0 := by simpa using hneg
    simp only [if_neg hneg]
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.exitControl rfl)
    apply Steps.cons .finish
    simpa [ifAbsConfig, ifAbsResult, hneg, hneg'] using
      (Steps.refl
        (⟨.done [.i32 x], (ifAbsConfig x).store⟩ : Config Unit))

theorem ifAbs_runs (x : UInt32) :
    (runSteps (ifAbsTrace x).length (ifAbsConfig x)).result.values? =
      some [.i32 (ifAbsResult x)] :=
  congrArg RunnerResult.values?
    (runSteps_eq_success_of_steps (ifAbs_steps x))

theorem ifAbsSpec (x : UInt32) :
    TerminatesWith (ifAbsConfig x)
      (fun values _ => values = [.i32 (ifAbsResult x)]) :=
  runSteps_values_terminates (ifAbs_runs x)

theorem ifAbs_partial (x : UInt32) :
    PartiallyMeets (ifAbsConfig x)
      (fun values _ => values = [.i32 (ifAbsResult x)]) :=
  runSteps_values_partiallyMeets (ifAbs_runs x)

end Wasm
