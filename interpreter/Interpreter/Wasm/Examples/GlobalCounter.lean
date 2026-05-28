import Interpreter.Wasm.Wp.Tactic

/-! ## Example: global counter

    The function `tick() → i32` reads global 0 (a counter), pushes the old
    value onto the stack, increments the global, and returns the old value.

    The module declares one global initialised to 0.  Calling `tick()`
    three times should return 0, 1, 2 in succession. -/

namespace Wasm

def tickBody : Program := [
  .globalGet 0,          -- push globals[0]  (old count)
  .globalGet 0,          -- push globals[0]  again
  .const 1,
  .add,                  -- old + 1
  .globalSet 0           -- globals[0] := old + 1
]

def tickModule : Module :=
  { funcs   := [{ params := [], locals := [], body := tickBody, results := [.i32] }]
    globals := [{ type := .i32, init := .i32 0 }] }

-- Sanity: three successive calls increment the global.
#eval
  let m := tickModule
  let st0 := m.initialStore
  match run 10 m 0 st0 [] with
  | .Success vs st1 =>
    match run 10 m 0 st1 [] with
    | .Success vs2 st2 =>
      match run 10 m 0 st2 [] with
      | .Success vs3 _ => (vs, vs2, vs3)
      | _ => ([], [], [.i32 99])
    | _ => ([], [], [.i32 99])
  | _ => ([], [], [.i32 99])

theorem tickModule_initial_global :
    tickModule.initialStore.globals.globals = [.i32 0] := by
  native_decide

/-- One call to `tick` returns the old global value and increments it. -/
theorem tick_spec (st : Store) (n : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 n)) :
    wp tickModule tickBody
      (fun c => c = .Fallthrough
                      { st with globals := { globals := st.globals.globals.set 0 (.i32 (1 + n)) } }
                      { params := [], locals := [], values := [.i32 n] })
      st ⟨[], [], []⟩ := by
  unfold tickBody
  wp_run
  simp [hg]

end Wasm
