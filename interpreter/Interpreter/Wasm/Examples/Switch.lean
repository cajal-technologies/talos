import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-! ## Example: Switch

    Three-way dispatch via `br_table`. Three nested blocks plus three
    `.ret` exits; the table sends 0 → 10, 1 → 20, anything else → 30. -/

namespace Wasm

def Switch : Program := [
  .block 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 0,
        .brTable [0, 1] 2
      ],
      .const 10, .ret
    ],
    .const 20, .ret
  ],
  .const 30, .ret
]

theorem switchSpec (m : Module) (st : Store) (i : UInt32) :
    wp m Switch
        (fun c => c = .Return st
          [.i32 (if i.toNat = 0 then 10 else if i.toNat = 1 then 20 else 30)])
        st { params := [.i32 i], locals := [], values := [] } := by
  unfold Switch
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  simp
  rcases h0 : i.toNat with _ | _ | n
  · simp
  · simp
  · simp

end Wasm
