import Interpreter.Wasm.Wp.Tactic

namespace Wasm

def SelectAbs : Program := [
  .const 0,
  .localGet 0,
  .sub,
  .localGet 0,
  .localGet 0,
  .const 0,
  .ltS,
  .select
]

theorem selectAbsSpec (m : Module) (st : Store Unit) (n : UInt32) :
    wp m SelectAbs
      (fun c => ∃ st' s',
        c = .Fallthrough st' s' ∧
        s'.values = [.i32 (if n.toInt32 < 0 then (0 : UInt32) - n else n)])
      st { params := [.i32 n], locals := [], values := [] } := by
  unfold SelectAbs
  -- wp_run fires all @[simp] lemmas including wp_select_cons
  wp_run
  simp
  by_cases hneg : n.toInt32 < 0
  · simp [hneg]
  · simp [hneg]

end Wasm
