import Interpreter.Wasm.Wp.Tactic

/-! ## Example: EarlyBr

    A top-level `.br 0` targets the implicit function-level block and returns
    the operand stack as the function result (Wasm spec). -/

namespace Wasm

def EarlyBr : Program := [.localGet 0, .br 0]

def earlyBrModule : Module := {
  funcs := [{ params := [.i32], results := [.i32], body := EarlyBr }]
}

end Wasm
