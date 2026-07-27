import Interpreter.Wasm.SmallStep

namespace Wasm
open SmallStep

def IsEven : Program := [.localGet 0, .const 1, .and, .eqz]

def isEvenModule : Module :=
  { funcs := [{ params := [.i32], body := IsEven, results := [.i32] }] }

def isEvenConfig (value : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 value] }
        code := IsEven
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { module := isEvenModule, host := {} }
        wasm := isEvenModule.initialStore } }

def isEvenResult (value : UInt32) : UInt32 :=
  if (1 : UInt32) &&& value = 0 then 1 else 0

theorem isEven_runs (value : UInt32) :
    (runSteps 5 (isEvenConfig value)).result.values? =
      some [.i32 (isEvenResult value)] := by
  have hsteps : Steps (isEvenConfig value)
      [(.instruction (.localGet 0)), (.instruction (.const 1)),
       (.instruction .and), (.instruction .eqz), (.administrative .finish)]
      ⟨.done [.i32 (isEvenResult value)], (isEvenConfig value).store⟩ := by
    apply Steps.cons (.localGet rfl)
    apply Steps.cons .const
    apply Steps.cons .and
    apply Steps.cons (.eqz rfl)
    apply Steps.cons .finish
    by_cases h : value &&& (1 : UInt32) = 0 <;>
      simp [isEvenResult, h, UInt32.and_comm]
    all_goals exact Steps.refl _
  exact congrArg RunnerResult.values? (runSteps_eq_success_of_steps hsteps)

theorem isEvenSpec (value : UInt32) :
    TerminatesWith (isEvenConfig value)
      (fun values _ => values = [.i32 (isEvenResult value)]) :=
  runSteps_values_terminates (isEven_runs value)

theorem isEven_partial (value : UInt32) :
    PartiallyMeets (isEvenConfig value)
      (fun values _ => values = [.i32 (isEvenResult value)]) :=
  runSteps_values_partiallyMeets (isEven_runs value)

end Wasm
