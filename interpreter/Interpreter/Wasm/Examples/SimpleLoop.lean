import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Examples.Harness

/-! ## Example: SimpleLoop

    Counts down `n` while accumulating into `locals[0]`. Uses:
    - invariant `∃ x y, s = ⟨[.i32 x], [.i32 y], []⟩ ∧ x.toNat + y.toNat = n.toNat`,
      where `x` is `params[0]` (the counter) and `y` is `locals[0]` (the accumulator).
    - variant   `x.toNat` (the counter), strictly decreases each iteration.

    The invariant is stated in `Nat` (via `toNat`) to avoid UInt32 wraparound, so
    `omega` applies. -/

namespace Wasm

def SimpleLoop : Program := [
    .const 0, .localSet 1,
    .loop 0 0 [
      .block 0 0 [
        .block 0 0 [
          .localGet 0, .br_if 0, .br 1
        ],
        .localGet 1, .const 1, .add, .localSet 1,
        .localGet 0, .const 1, .sub, .localSet 0, .br 1]],
    .localGet 1
]

theorem simpleLoopSpec (m : Module) (st : Store Unit) (n : UInt32) :
    wp m SimpleLoop
        (fun c => ∃ st' s', c = .Fallthrough st' s' ∧ s'.values = [.i32 n])
        st { params := [.i32 n], locals := [.i32 0], values := [] } := by
  unfold SimpleLoop
  wp_run
  simp
  apply wp_loop_cons
    (Inv := fun st' s' => st' = st ∧ ∃ x y : UInt32,
      s' = ⟨[.i32 x], [.i32 y], []⟩ ∧ x.toNat + y.toNat = n.toNat)
    (μ := fun _ s' => match s'.params.headD (.i32 0) with | .i32 x => x.toNat | _ => 0)
  · refine ⟨rfl, n, 0, ?_, ?_⟩
    · rfl
    · simp
  · rintro st' s' ⟨rfl, x, y, rfl, hxy⟩
    apply wp_block_cons
    apply wp_block_cons
    wp_run
    simp
    by_cases hx : x = 0
    · subst hx
      simp_all
      exact UInt32.toNat.inj hxy
    · have hxn : x.toNat ≠ 0 := by
        intro h
        exact hx (UInt32.toNat.inj h)
      have hxsub := UInt32.toNat_sub_one_eq hxn
      simp
      have hy : y.toNat < 4294967295 := by
        have hn := n.toNat_lt
        omega
      refine ⟨?_, ?_⟩ <;> omega

end Wasm
