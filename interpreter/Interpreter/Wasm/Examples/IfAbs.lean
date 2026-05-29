import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-! ## Example: IfAbs

    Signed absolute value via `.iff`. Branches on `x <ₛ 0`; the `then`
    arm returns `0 - x`, the `else` arm returns `x`. -/

namespace Wasm

def IfAbs : Program := [
  .localGet 0, .const 0, .ltS,
  .iff 0 1
    [.const 0, .localGet 0, .sub]
    [.localGet 0]
]

theorem ifAbsSpec (m : Module) (st : Store Unit) (x : UInt32) :
    wp m IfAbs
        (fun c => c = .Fallthrough st
                    { params := [.i32 x], locals := [],
                      values := [.i32 (if x.toInt32 < 0 then 0 - x else x)] })
        st { params := [.i32 x], locals := [], values := [] } := by
  unfold IfAbs
  wp_run
  simp
  apply wp_iff_cons
    (c := if x.toInt32 < 0 then 1 else 0) (vs := []) rfl
  by_cases hneg : x.toInt32 < 0
  · simp [hneg]
  · simp [hneg]

end Wasm
