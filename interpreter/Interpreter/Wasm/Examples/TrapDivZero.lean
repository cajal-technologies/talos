import Interpreter.Wasm.Wp.Tactic

/-! ## Example: TrapDivZero

    Conditional total spec for `divU`: traps on a zero divisor, falls
    through with the quotient otherwise. Exercises the `.Trap`
    continuation alongside ordinary arithmetic. -/

namespace Wasm

def TrapDivZero : Program := [
  .localGet 0, .localGet 1, .divU
]

#eval
  let m : Module := { funcs := [{ params := [.i32, .i32], body := TrapDivZero, results := [.i32] }] }
  -- args reversed: standard Wasm convention reverses params on entry,
  -- so to compute 10 / 3 we pass [.i32 3, .i32 10].
  run 10 m 0 m.initialStore [.i32 3, .i32 10]
#eval
  let m : Module := { funcs := [{ params := [.i32, .i32], body := TrapDivZero, results := [.i32] }] }
  run 10 m 0 m.initialStore [.i32 0, .i32 10]

theorem trapDivZeroSpec (m : Module) (st : Store) (a b : UInt32) :
    wp m TrapDivZero
        (fun c =>
          if b = 0 then c = .Trap st "integer divide by zero"
          else c = .Fallthrough st
            { params := [.i32 a, .i32 b], locals := [],
              values := [.i32 (a / b)] })
        st { params := [.i32 a, .i32 b], locals := [], values := [] } := by
  unfold TrapDivZero
  wp_run
  by_cases hb : b = 0
  · simp [hb]
  · simp [hb]

end Wasm
