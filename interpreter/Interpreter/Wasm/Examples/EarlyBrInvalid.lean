import Interpreter.Wasm.Validate

/-! ## Example: EarlyBrInvalid

A top-level `br k` with `k ≥ 1` targets no static label. Validation rejects
the module, so this malformed control state never enters small-step execution.
-/

namespace Wasm

def EarlyBrInvalid : Program := [.localGet 0, .br 1]

def earlyBrInvalidModule : Module :=
  { funcs := [{
      params := [.i32]
      results := [.i32]
      body := EarlyBrInvalid }] }

theorem early_br_out_of_scope_is_invalid :
    (match earlyBrInvalidModule.validate with
      | .error message => some message
      | .ok _ => none) = some "unknown label" := by
  native_decide

end Wasm
