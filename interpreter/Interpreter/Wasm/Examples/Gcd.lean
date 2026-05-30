import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Wasm

def Gcd : Program := [
  .loop 0 0 [
    .block 0 0 [
      .localGet 1,          -- push b
      .eqz,                 -- b == 0 ?
      .br_if 0,             -- if b==0: exit block → exits loop
      .localGet 0,          -- push a
      .localGet 1,          -- push b    stack: [b, a]
      .remU,                -- push a % b
      .localSet 2,          -- temp := a % b
      .localGet 1,          -- push b
      .localSet 0,          -- a := b
      .localGet 2,          -- push temp
      .localSet 1,          -- b := temp
      .br 1                 -- jump to top of loop (continue)
    ]
  ],
  .localGet 0               -- return a
]

theorem gcdSpec (m : Module) (st : Store) (n k : UInt32) :
    wp m Gcd
      (fun c => ∃ st' s',
        c = .Fallthrough st' s' ∧
        s'.values = [.i32 (UInt32.ofNat (Nat.gcd n.toNat k.toNat))])
      st { params := [.i32 n, .i32 k], locals := [.i32 0], values := [] } := by
  unfold Gcd
  apply wp_loop_cons
    (Inv := fun st' s' =>
        st' = st ∧
        ∃ a b : UInt32,
          s' = { params := [.i32 a, .i32 b], locals := [.i32 0], values := [] } ∧
          Nat.gcd a.toNat b.toNat = Nat.gcd n.toNat k.toNat)
    (μ := fun _ s' =>
        match s'.params with
        | [_, .i32 b] => b.toNat
        | _           => 0)
  · exact ⟨rfl, n, k, rfl, rfl⟩
  · rintro st' s' ⟨rfl, a, b, rfl, hgcd⟩
    apply wp_block_cons
    wp_run
    simp
    by_cases hb : b = 0
    · subst hb
      simp [Nat.gcd_zero_right] at hgcd
      simp [← hgcd, UInt32.ofNat_toNat]
    · have hbpos : 0 < b.toNat :=
        Nat.pos_of_ne_zero (fun h => hb (UInt32.toNat_eq_zero.mp h))
      refine ⟨rfl, b, a % b, rfl, ?_, ?_⟩
      · rw [← hgcd]
        simp [UInt32.toNat_mod]
        exact (Nat.gcd_rec a.toNat b.toNat).symm
      · simp [UInt32.toNat_mod]
        exact Nat.mod_lt a.toNat hbpos

end Wasm
