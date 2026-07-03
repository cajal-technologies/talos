import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Examples.Harness

/-! ## Example: Factorial

    Loop with measure `k.toNat` (the counter). Invariant:
    `acc * (k.toNat)! = (n.toNat)!`. -/

namespace Wasm

def Factorial : Program := [
  .const 1, .localSet 1,
  .loop 0 0 [
    .block 0 0 [
      .localGet 0, .eqz, .br_if 0, -- if n == 0 break
      .localGet 0, .localGet 1, .mul, .localSet 1, -- acc *= n
      .localGet 0, .const 1, .sub, .localSet 0, -- n -= 1
      .br 1 -- repeat
    ]
  ],
  .localGet 1
]

theorem factorialSpec (m : Module) (st : Store Unit) (n : UInt32) :
    wp m Factorial
        (fun c => ∃ st' s', c = .Fallthrough st' s' ∧
            s'.values = [.i32 (UInt32.ofNat n.toNat.factorial)])
        st { params := [.i32 n], locals := [.i32 0], values := [] } := by
  unfold Factorial
  wp_run
  simp
  apply wp_loop_cons
    (Inv := fun st' s' => st' = st ∧ ∃ x acc : UInt32,
      s' = ⟨[.i32 x], [.i32 acc], []⟩ ∧
        UInt32.ofNat (acc.toNat * x.toNat.factorial) = UInt32.ofNat n.toNat.factorial)
    (μ := fun _ s' => match s'.params.headD (.i32 0) with | .i32 x => x.toNat | _ => 0)
  · refine ⟨rfl, n, 1, rfl, ?_⟩
    simp
  · rintro st' s' ⟨rfl, x, acc, rfl, hacc⟩
    apply wp_block_cons
    wp_run
    simp
    by_cases hx : x = 0
    · subst hx
      simp_all
    · have hxn : x.toNat ≠ 0 := by
        intro h
        exact hx (UInt32.toNat.inj h)
      have hxsub := UInt32.toNat_sub_one_eq hxn
      simp [hx]
      refine ⟨?_, by omega⟩
      rw [← hacc]
      have hxfact : x.toNat.factorial = x.toNat * (x.toNat - 1).factorial := by
        rcases hx' : x.toNat with _ | k
        · exact absurd hx' hxn
        · simp [Nat.factorial_succ]
      apply UInt32.toNat.inj
      simp [UInt32.toNat_mul, hxsub, hxfact]
      rw [Nat.mul_assoc]

end Wasm
