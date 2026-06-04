import Interpreter.Wasm.Wp.Tactic

/-! ## Example: EarlyBr

    A top-level `.br 0` targets the implicit function-level block and returns
    the operand stack as the function result (Wasm spec). -/

namespace Wasm

def EarlyBr : Program := [.localGet 0, .br 0]

def earlyBrModule : Module := {
  funcs := [{ params := [.i32], results := [.i32], body := EarlyBr }]
}

theorem earlyBrSpec (m : Module) (st : Store Unit) (x : UInt32) :
    wp m EarlyBr
        (fun c => c = .Break 0 st
                    { params := [.i32 x], locals := [],
                      values := [.i32 x] })
        st { params := [.i32 x], locals := [], values := [] } := by
  unfold EarlyBr
  wp_run
  simp

end Wasm
