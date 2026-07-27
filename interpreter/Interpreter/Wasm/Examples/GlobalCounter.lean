import Interpreter.Wasm.SmallStep

/-! ## Example: global counter

    `tick() → i32` returns global 0 and increments it. The main theorem is
    symbolic over any store whose first global contains an i32, and uses the
    authoritative relational small-step semantics.
-/

namespace Wasm
open SmallStep

def tickBody : Program := [
  .globalGet 0,
  .globalGet 0,
  .const 1,
  .add,
  .globalSet 0
]

def tickModule : Module :=
  { funcs := [{ body := tickBody, results := [.i32] }]
    globals := [{ init := .i32 0 }] }

theorem tickModule_initial_global :
    (tickModule.initialStore (α := Unit)).globals.globals = [.i32 0] := by
  native_decide

def tickStore (st : Store Unit) : MachineStore Unit :=
  { runtime := { module := tickModule, host := {} }
    wasm := st }

def tickConfig (st : Store Unit) : Config Unit :=
  { expr := .running
      { locals := {}
        code := tickBody
        resultArity := 1
        callerRemainder := [] }
    store := tickStore st }

def tickFinalStore (st : Store Unit) (n : UInt32) : MachineStore Unit :=
  { tickStore st with
    wasm :=
      { st with
        globals := { globals := st.globals.globals.set 0 (.i32 (1 + n)) } } }

def tickTrace : List StepKind := [
  .instruction (.globalGet 0),
  .instruction (.globalGet 0),
  .instruction (.const 1),
  .instruction .add,
  .instruction (.globalSet 0),
  .administrative .finish
]

theorem tick_steps (st : Store Unit) (n : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 n)) :
    Steps (tickConfig st) tickTrace
      ⟨.done [.i32 n], tickFinalStore st n⟩ := by
  unfold tickConfig tickBody tickTrace
  apply Steps.cons
    (Step.globalGet (value := .i32 n) (by
      simpa [tickStore, globalAt?] using hg))
  apply Steps.cons
    (Step.globalGet (value := .i32 n) (by
      simpa [tickStore, globalAt?] using hg))
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  apply Steps.cons (Step.globalSet (by
    simpa [tickStore, globalAt?] using congrArg Option.isSome hg))
  simpa [tickFinalStore, tickStore] using
    (Steps.cons Step.finish (Steps.refl
      (⟨.done [.i32 n], tickFinalStore st n⟩ : Config Unit)))

theorem tick_runs (st : Store Unit) (n : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 n)) :
    (runSteps 6 (tickConfig st)).result =
      .success [.i32 n] (tickFinalStore st n) := by
  simpa [tickTrace] using
    runSteps_eq_success_of_steps (tick_steps st n hg)

/-- One call returns the old global and stores its successor. -/
theorem tick_spec (st : Store Unit) (n : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 n)) :
    TerminatesWith (tickConfig st) (fun values store =>
      values = [.i32 n] ∧
      store.wasm.globals.globals[0]? = some (.i32 (1 + n))) := by
  apply runSteps_success_terminates (tick_runs st n hg)
  constructor
  · rfl
  simp [tickFinalStore, tickStore]
  grind

theorem tick_partial (st : Store Unit) (n : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 n)) :
    PartiallyMeets (tickConfig st) (fun values store =>
      values = [.i32 n] ∧
      store.wasm.globals.globals[0]? = some (.i32 (1 + n))) := by
  apply runSteps_success_partiallyMeets (tick_runs st n hg)
  constructor
  · rfl
  simp [tickFinalStore, tickStore]
  grind

def tickInitialStore : Store Unit := tickModule.initialStore
def tickAfterZero : Store Unit := (tickFinalStore tickInitialStore 0).wasm
def tickAfterOne : Store Unit := (tickFinalStore tickAfterZero 1).wasm
def tickAfterTwo : Store Unit := (tickFinalStore tickAfterOne 2).wasm

/-- Three calls thread the physical global store and return `0`, `1`, `2`. -/
theorem tick_three_calls :
    (runSteps 6 (tickConfig tickInitialStore)).result =
        .success [.i32 0] (tickFinalStore tickInitialStore 0) ∧
    (runSteps 6 (tickConfig tickAfterZero)).result =
        .success [.i32 1] (tickFinalStore tickAfterZero 1) ∧
    (runSteps 6 (tickConfig tickAfterOne)).result =
        .success [.i32 2] (tickFinalStore tickAfterOne 2) ∧
    tickAfterTwo.globals.globals[0]? = some (.i32 3) := by
  constructor
  · exact tick_runs tickInitialStore 0 (by native_decide)
  constructor
  · exact tick_runs tickAfterZero 1 (by native_decide)
  constructor
  · exact tick_runs tickAfterOne 2 (by native_decide)
  · native_decide

end Wasm
