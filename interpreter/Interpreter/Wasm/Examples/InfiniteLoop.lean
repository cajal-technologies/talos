import Interpreter.Wasm.Wp.Loop

/-! ## Example: InfiniteLoop

    `[.loop 0 0 [.br 0]]` cannot terminate. Operationally, every wp for it is
    forced to accept `.OutOfFuel`, so no post that excludes it is provable. -/

namespace Wasm

def InfiniteLoop : Program := [.loop 0 0 [.br 0]]

theorem infiniteLoopDiverges (m : Module) (st : Store Unit) (s : Locals) :
    wp m InfiniteLoop (fun c => c ≠ .OutOfFuel) st s → False := by
  unfold InfiniteLoop
  rw [wp_loop_br0_cons]
  intro h
  exact h rfl

end Wasm
