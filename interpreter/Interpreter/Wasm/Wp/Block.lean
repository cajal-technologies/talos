import Interpreter.Wasm.Wp.Structural
import Interpreter.Wasm.Semantics.Lemmas

/-! ### Block / if-then-else: structural, no measure required.

    Neither iterates; control either falls through, breaks out at level 0
    (exiting the construct), or propagates an outer break/return/trap. The
    rules are one-sided sufficient conditions — provide the body's `wp`
    against the right outcome continuation.

    Both are `wp_of_body_dispatch` (see `Wp/Structural.lean`) applied with this
    construct's unfolding lemma: all the fuel reasoning lives there, and only
    the three continuations a structured construct interprets are handled
    here. -/

namespace Wasm

theorem wp_block_cons {ps rs : Nat} {body rest : Program} {Q : Assertion α}
    (h : wp m body
          (fun c => match c with
            | .Fallthrough st' s'   =>
              wp m rest Q st'
                { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s'       =>
              wp m rest Q st'
                { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break (k+1) st' s'   => Q (.Break k st' s')
            | other                => Q other)
          st s env) :
    wp m (.block ps rs body :: rest) Q st s env := by
  refine wp_of_body_dispatch h ?_ ?_ ?_ ?_ ?_
  · -- Forwarded continuations: the block is transparent to them.
    intro f cont hcont hbody
    cases cont <;>
      first
        | exact (hcont : False).elim
        | rw [exec_block_cons, hbody]
  · intro cont hcont hQ
    cases cont <;>
      first
        | exact (hcont : False).elim
        | exact hQ
  · -- Fall-through: carry on with `rest` on the trimmed stack.
    intro N st' s' hQ hstable
    refine wp_of_eventually_eq (N := N + 1) ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_block_cons, hstable f (by omega)]
  · -- `br 0` exits the block, landing exactly where fall-through does.
    intro N st' s' hQ hstable
    refine wp_of_eventually_eq (N := N + 1) ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_block_cons, hstable f (by omega)]
  · -- An outer break sheds one level and propagates.
    intro N k st' s' hQ hstable
    refine wp_of_eventually_const (N := N + 1) (cont := .Break k st' s') ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_block_cons, hstable f (by omega)]

/-- `iff` rule: dispatch on the top-of-stack i32 condition, then reason like
    a block on the chosen branch. Stack precondition: `.i32 c :: vs` on top. -/
theorem wp_iff_cons {ps rs : Nat} {thn els rest : Program} {Q : Assertion α}
    {c : UInt32} {vs : List Value}
    (hStack : s.values = .i32 c :: vs)
    (hBody : wp m (if c ≠ 0 then thn else els)
              (fun cont => match cont with
                | .Fallthrough st' s'   =>
                  wp m rest Q st'
                    { s' with values := s'.values.take rs ++ vs.drop ps } env
                | .Break 0 st' s'       =>
                  wp m rest Q st'
                    { s' with values := s'.values.take rs ++ vs.drop ps } env
                | .Break (k+1) st' s'   => Q (.Break k st' s')
                | other                => Q other)
              st { s with values := vs } env) :
    wp m (.iff ps rs thn els :: rest) Q st s env := by
  refine wp_of_body_dispatch hBody ?_ ?_ ?_ ?_ ?_
  · -- Forwarded continuations: the chosen branch's result passes through.
    intro f cont hcont hbody
    cases cont <;>
      first
        | exact (hcont : False).elim
        | rw [exec_iff_cons hStack, hbody]
  · intro cont hcont hQ
    cases cont <;>
      first
        | exact (hcont : False).elim
        | exact hQ
  · -- Fall-through: carry on with `rest` on the trimmed stack.
    intro N st' s' hQ hstable
    refine wp_of_eventually_eq (N := N + 1) ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_iff_cons hStack, hstable f (by omega)]
  · -- `br 0` exits the `if`, landing exactly where fall-through does.
    intro N st' s' hQ hstable
    refine wp_of_eventually_eq (N := N + 1) ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_iff_cons hStack, hstable f (by omega)]
  · -- An outer break sheds one level and propagates.
    intro N k st' s' hQ hstable
    refine wp_of_eventually_const (N := N + 1) (cont := .Break k st' s') ?_ hQ
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_iff_cons hStack, hstable f (by omega)]

end Wasm
