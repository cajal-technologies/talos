import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas

/-! ### The skeleton shared by the structural rules.

`block`, `loop` and `if` all reason the same way: run the body at one less
fuel, then react to the continuation the body produced. Everything fuel-shaped
in that argument is common to the three — the `OutOfFuel` split, the
`exec_fuel_mono` stabilisation, and the continuations the construct merely
forwards — so it is written here once, in `wp_of_body_dispatch`.

The reaction is deliberately *not* factored as a
`Continuation α → Continuation α` transformer: on fall-through a structured
construct re-enters `exec (fuel + 1) … rest`, so what it does with a
continuation depends on the fuel it was handed as well as on the continuation
itself. The three arms a construct interprets are therefore left as goals about
`wp m prog Q st s env`, with the body's stabilised behaviour supplied as a
hypothesis; a rule discharges them with `wp_of_eventually_eq` (control leaves
the construct and carries on with the rest of the program) or
`wp_of_eventually_const` (an outer break, which sheds one level and so is no
more the identity than the other two). -/

namespace Wasm

/-- The continuations a structured construct forwards unchanged.

`Fallthrough` and `Break` are the two a `block` / `loop` / `if` interprets;
every other continuation — traps, returns, `OutOfFuel` — passes straight
through, in the semantics and in the rule's postcondition alike. -/
def Continuation.IsPassthrough {α : Type} : Continuation α → Prop
  | .Fallthrough _ _ => False
  | .Break _ _ _     => False
  | _                => True

/-- `wp` from an eventually constant `exec`: if every fuel from `N` on runs
`prog` to `cont`, the postcondition only has to hold of `cont`. -/
theorem wp_of_eventually_const {α : Type} {m : Module} {env : HostEnv α}
    {st : Store α} {s : Locals} {prog : Program} {Q : Assertion α}
    {N : Nat} {cont : Continuation α}
    (hconst : ∀ f ≥ N, exec f m st s prog env = cont) (hQ : Q cont) :
    wp m prog Q st s env := by
  unfold wp
  refine ⟨N, fun f hf => ?_⟩
  rw [hconst f hf]
  exact hQ

/-- `wp` transported along an eventual agreement: if from `N` on, running
`prog` from `(st, s)` *is* running `prog'` from `(st', s')` at the same fuel,
then a `wp` for the latter is a `wp` for the former. This is what a structured
construct does once control has left it and the rest of the program takes
over. -/
theorem wp_of_eventually_eq {α : Type} {m : Module} {env : HostEnv α}
    {st st' : Store α} {s s' : Locals} {prog prog' : Program} {Q : Assertion α}
    {N : Nat}
    (heq : ∀ f ≥ N, exec f m st s prog env = exec f m st' s' prog' env)
    (hcont : wp m prog' Q st' s' env) :
    wp m prog Q st s env := by
  unfold wp at hcont ⊢
  obtain ⟨Nr, hNr⟩ := hcont
  refine ⟨max N Nr, fun f hf => ?_⟩
  rw [heq f (by omega)]
  exact hNr f (by omega)

/-- Fuel stabilisation of a body's `wp` — the `by_cases` / `exec_fuel_mono`
preamble every structural rule opens with.

Either the body diverges, in which case no fuel makes `exec` return and the
body's `wp` already records `Qb .OutOfFuel`; or `exec` on the body is pinned,
from some fuel on, to a single non-`OutOfFuel` continuation that `Qb`
describes. -/
theorem wp_stabilise {α : Type} {m : Module} {env : HostEnv α}
    {st : Store α} {s : Locals} {body : Program} {Qb : Assertion α}
    (h : wp m body Qb st s env) :
    (Qb .OutOfFuel ∧ ∃ N : Nat, ∀ f ≥ N, exec f m st s body env = .OutOfFuel) ∨
      ∃ (N : Nat) (cont : Continuation α), cont ≠ .OutOfFuel ∧ Qb cont ∧
        ∀ f ≥ N, exec f m st s body env = cont := by
  unfold wp at h
  obtain ⟨Nb, hN⟩ := h
  by_cases hOOF : ∀ f ≥ Nb, exec f m st s body env = .OutOfFuel
  · have hQ := hN Nb le_rfl
    rw [hOOF Nb le_rfl] at hQ
    exact .inl ⟨hQ, Nb, hOOF⟩
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hf₀_ne⟩ := hOOF
    exact .inr ⟨f₀, exec f₀ m st s body env, hf₀_ne, hN f₀ hf₀,
      fun f hf => exec_fuel_mono hf hf₀_ne⟩

/-- The body-dispatch step shared by `wp_block_cons`, `wp_iff_cons` and
`wp_loop_cons`.

`prog` runs `body` from `(st, sb)` at one less fuel and then reacts to the
continuation the body produced. This lemma does the fuel bookkeeping: it
stabilises the body and settles every continuation the construct forwards —
`hFwd` in the semantics, `hQFwd` in the postcondition, `OutOfFuel` included.

Three arms are left to the caller, one per continuation a structured construct
interprets: fall-through, `Break 0`, and `Break (k+1)`. Each is handed the fuel
`N` from which the body's result is pinned, and has to prove the rule's own
goal from it. -/
theorem wp_of_body_dispatch {α : Type} {m : Module} {env : HostEnv α}
    {st : Store α} {s sb : Locals} {body prog : Program} {Q Qb : Assertion α}
    (hBody : wp m body Qb st sb env)
    (hFwd : ∀ (f : Nat) (cont : Continuation α), cont.IsPassthrough →
      exec f m st sb body env = cont → exec (f + 1) m st s prog env = cont)
    (hQFwd : ∀ cont : Continuation α, cont.IsPassthrough → Qb cont → Q cont)
    (hFall : ∀ (N : Nat) (st' : Store α) (s' : Locals),
      Qb (.Fallthrough st' s') →
      (∀ f ≥ N, exec f m st sb body env = .Fallthrough st' s') →
      wp m prog Q st s env)
    -- The break levels are given in constructor form (`Nat.zero`, `k.succ`
    -- rather than `0`, `k + 1`) so that a construct's own matcher reduces on
    -- these continuations without unfolding `OfNat`/`Nat.add`: the callers'
    -- closing `rfl`s run at reducible transparency.
    (hBreak0 : ∀ (N : Nat) (st' : Store α) (s' : Locals),
      Qb (.Break Nat.zero st' s') →
      (∀ f ≥ N, exec f m st sb body env = .Break Nat.zero st' s') →
      wp m prog Q st s env)
    (hBreakSucc : ∀ (N k : Nat) (st' : Store α) (s' : Locals),
      Qb (.Break k.succ st' s') →
      (∀ f ≥ N, exec f m st sb body env = .Break k.succ st' s') →
      wp m prog Q st s env) :
    wp m prog Q st s env := by
  rcases wp_stabilise hBody with ⟨hQoof, Nb, hoof⟩ | ⟨N, cont, _, hQ, hstable⟩
  · -- The body never returns: the construct runs out of fuel with it.
    refine wp_of_eventually_const (N := Nb + 1) (cont := .OutOfFuel) ?_
      (hQFwd .OutOfFuel trivial hQoof)
    intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact hFwd f .OutOfFuel trivial (hoof f (by omega))
  · by_cases hfwd : cont.IsPassthrough
    · -- Nothing to interpret: the body's continuation passes through.
      refine wp_of_eventually_const (N := N + 1) (cont := cont) ?_
        (hQFwd cont hfwd hQ)
      intro fuel hfuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      exact hFwd f cont hfwd (hstable f (by omega))
    · cases cont with
      | Fallthrough st' s' => exact hFall N st' s' hQ hstable
      | Break k st' s' =>
        cases k with
        | zero => exact hBreak0 N st' s' hQ hstable
        | succ k => exact hBreakSucc N k st' s' hQ hstable
      | Return _ _ => exact absurd trivial hfwd
      | Trap _ _ => exact absurd trivial hfwd
      | Invalid _ => exact absurd trivial hfwd
      | OutOfFuel => exact absurd trivial hfwd
      | ReturnCall _ _ _ => exact absurd trivial hfwd
      | Throwing _ _ _ _ => exact absurd trivial hfwd

end Wasm
