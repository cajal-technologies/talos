import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-! ## Example: EarlyReturn

    `.ret` from inside two nested `.block`s. The semantics propagates
    `Continuation.Return` straight through both blocks, so anything
    after the `.ret` is dead code. -/

namespace Wasm

def EarlyReturn : Program := [
  .block 0 0 [
    .block 0 0 [
      .localGet 0, .ret
    ],
    .const 999
  ],
  .const 888
]

#eval
  let m : Module := { funcs := [{ params := [.i32], body := EarlyReturn, results := [.i32] }] }
  run 10 m 0 m.initialStore [.i32 42]

theorem earlyReturnSpec (m : Module) (st : Store) (x : UInt32) :
    wp m EarlyReturn
        (fun c => c = .Return st [.i32 x])
        st { params := [.i32 x], locals := [], values := [] } := by
  unfold EarlyReturn
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  simp

end Wasm
