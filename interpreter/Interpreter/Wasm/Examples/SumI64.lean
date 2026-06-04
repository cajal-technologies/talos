import Interpreter.Wasm.Wp.Tactic

/-! ## Example: SumI64

    Straight-line exercise of the i64 / conversion subset. Computes
    `extendU(x) + extendU(x) + 1` as an i64 and wraps it back to i32. -/

namespace Wasm

def SumI64 : Program := [
  .localGet 0, .extendUI32,
  .localGet 0, .extendUI32,
  .addI64,
  .constI64 1, .addI64,
  .wrapI64
]

theorem sumI64Spec (m : Module) (st : Store Unit) (x : UInt32) :
    wp m SumI64
        (fun c => c = .Fallthrough st
                    { params := [.i32 x], locals := [],
                      values := [.i32 (UInt32.ofNat
                        ((UInt64.ofNat x.toNat + UInt64.ofNat x.toNat + 1).toNat % 2 ^ 32))] })
        st { params := [.i32 x], locals := [], values := [] } := by
  unfold SumI64
  wp_run
  simp

end Wasm
