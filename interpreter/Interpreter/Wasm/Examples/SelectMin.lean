import Interpreter.Wasm.Wp.Tactic

/-! ## Example: SelectMin

    Branchless unsigned `min(x, y)` using `.select`. Two leading `.nop`s
    and a trailing `.drop` show the other parametric / nullary ops along
    the way. -/

namespace Wasm

def SelectMin : Program := [
  .nop, .nop,
  .localGet 0, .localGet 1,         -- [.i32 y, .i32 x]
  .localGet 0, .localGet 1, .ltU,   -- push cond = (x < y)
  .select,                           -- if cond then x else y
  .const 42, .drop                   -- pad with const 42; drop it again
]

#eval
  let m : Module := { funcs := [{ params := [.i32, .i32], body := SelectMin, results := [.i32] }] }
  run 10 m 0 m.initialStore [.i32 3, .i32 7]
#eval
  let m : Module := { funcs := [{ params := [.i32, .i32], body := SelectMin, results := [.i32] }] }
  run 10 m 0 m.initialStore [.i32 9, .i32 4]

theorem selectMinSpec (m : Module) (st : Store) (x y : UInt32) :
    wp m SelectMin
        (fun c => c = .Fallthrough st
                    { params := [.i32 x, .i32 y], locals := [],
                      values := [.i32 (if x < y then x else y)] })
        st { params := [.i32 x, .i32 y], locals := [], values := [] } := by
  unfold SelectMin
  wp_run
  simp
  by_cases hxy : x < y
  · simp [hxy]
  · simp [hxy]

end Wasm
