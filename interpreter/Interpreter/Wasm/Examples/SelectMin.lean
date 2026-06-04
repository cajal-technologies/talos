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

theorem selectMinSpec (m : Module) (st : Store Unit) (x y : UInt32) :
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
