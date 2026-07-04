import Mathlib.Tactic
import Interpreter.Wasm.Semantics

/-- Simp set used by the `wp_run` tactic to symbolically execute straight-line
    code. Tag each new atomic `wp_*_cons` lemma with `@[wp_simp]` so it is
    automatically picked up by `wp_run` without editing the tactic. -/
register_simp_attr wp_simp

/-! ## Weakest-precondition foundation

`wp m c Q st s` says: from `(st, s)`, executing `c` in module `m` terminates in
bounded fuel ending in a continuation satisfying `Q`. The existential over fuel
absorbs all fuel-monotonicity reasoning at the framework level — users never
write `∀ fuel ≥ N`, never do induction on fuel.

This is a **total correctness** WP. Termination of loops is discharged by a
user-supplied **variant** (measure) that strictly decreases per iteration.
Infinite loops like `[.loop [.br 0]]` are unprovable by construction. -/

namespace Wasm

abbrev Assertion α  := Continuation α → Prop
abbrev AssertionF α := Store α → Locals → Prop

abbrev Imply (P Q : Assertion α) := ∀ c, P c → Q c

notation:50 P:51 " ⇛ " Q:51 => Imply P Q

@[irreducible]
def wp (m : Module) (c : Program) (Q : Assertion α) (st : Store α) (s : Locals)
    (env : HostEnv α := {}) : Prop :=
  ∃ N, ∀ fuel ≥ N, Q (exec fuel m st s c env)

/-! ### Building blocks -/

/-- If `exec` is constant in fuel (at every successor fuel) and equals `k`,
    then `wp` reduces to `Q k`. At `fuel = 0` `exec` returns `OutOfFuel`, so the
    `fuel + 1` threshold suffices for every atomic instruction. -/
theorem wp_of_exec_const_succ {α : Type} {m c} {Q : Assertion α} {st s k env}
    (heq : ∀ fuel, exec (fuel + 1) m st s c env = k) :
    wp m c Q st s env ↔ Q k := by
  unfold wp
  refine ⟨fun ⟨N, h⟩ => ?_, fun hQ => ⟨1, fun fuel hf => ?_⟩⟩
  · have := h (N + 1) (Nat.le_succ_of_le le_rfl)
    rw [heq] at this; exact this
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hf)
    rw [heq]; exact hQ

/-- If `exec` agrees with another `exec` at every successor fuel, the two `wp`s
    coincide. -/
theorem wp_of_exec_eq_succ {α : Type} {m c c'} {Q : Assertion α} {st st' s s' env env'}
    (heq : ∀ fuel, exec (fuel + 1) m st s c env = exec (fuel + 1) m st' s' c' env') :
    wp m c Q st s env ↔ wp m c' Q st' s' env' := by
  unfold wp
  constructor
  · rintro ⟨N, h⟩
    refine ⟨N + 1, fun fuel hf => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.one_le_iff_ne_zero.mp (Nat.one_le_of_lt hf))
    rw [← heq]; exact h _ (Nat.le_of_succ_le hf)
  · rintro ⟨N, h⟩
    refine ⟨N + 1, fun fuel hf => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.one_le_iff_ne_zero.mp (Nat.one_le_of_lt hf))
    rw [heq]; exact h _ (Nat.le_of_succ_le hf)

/-! ### Consequence -/

theorem wp.conseq {Q Q' : Assertion α} (hq : Q ⇛ Q')
    (h : wp m c Q st s env) : wp m c Q' st s env := by
  unfold wp at h ⊢
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun fuel hf => hq _ (hN fuel hf)⟩

end Wasm
