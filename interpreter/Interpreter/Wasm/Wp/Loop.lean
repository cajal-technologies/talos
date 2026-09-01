import Interpreter.Wasm.Wp.Structural
import Interpreter.Wasm.Semantics.Lemmas

/-! ### Loop with a variant.

    The user supplies an invariant `Inv` and a `Nat`-valued measure `μ`. Each
    iteration must either exit (fallthrough or non-`br 0`) or re-enter with
    `Inv` re-established **and** `μ` strictly smaller. Termination is then
    automatic from well-foundedness of `<` on `Nat`; no fuel reasoning leaks
    into user proofs.

    Infinite loops are excluded: `[.loop 0 0 [.br 0]]` cannot satisfy `μ st' s' < μ st s`
    for any measure, so no instance of this rule applies. -/

namespace Wasm

/-- One-step unfolding of `exec` on a `.loop ps rs body :: rest` program.
The loop trims to `paramArity` on a `br 0` re-entry (the loop's
iteration carries `ps` values) and to `resultArity` on fall-through.
On a recursive `Break 0`, the inner `execOne` is invoked on the
trimmed stack and its result is plumbed through directly. -/
private theorem exec_loop_cons_unfold {α : Type} (fuel : Nat) (m : Module)
    (env : HostEnv α) (st : Store α) (s : Locals)
    (ps rs : Nat) (body rest : Program) :
    exec (fuel + 1) m st s (.loop ps rs body :: rest) env =
      (match exec fuel m st s body env with
       | .Fallthrough st' s' =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ s.values.drop ps } rest env
       | .Break 0 st' s' =>
           (match execOne fuel m st'
                    { s' with values := s'.values.take ps ++ s.values.drop ps }
                    (.loop ps rs body) env with
            | .Fallthrough st'' s'' => exec (fuel + 1) m st'' s'' rest env
            | other => other)
       | .Break (k+1) st' s' => .Break k st' s'
       | other => other) := by
  simp only [exec, execOne_loop_succ]
  cases hb : exec fuel m st s body env with
  | Fallthrough _ _ => rfl
  | Break n _ _ =>
    cases n with
    | zero =>
      simp only
      cases hk : execOne fuel _ _ _ (.loop ps rs body) env with
      | Fallthrough _ _ => rfl
      | Break _ _ _ => rfl
      | Return _ _ => rfl
      | Trap _ _ => rfl
      | Invalid _ => rfl
      | OutOfFuel => rfl
      | ReturnCall _ _ _ => rfl
      | Throwing _ _ _ _ => rfl
    | succ _ => rfl
  | Return _ _ => rfl
  | Trap _ _ => rfl
  | Invalid _ => rfl
  | OutOfFuel => rfl
  | ReturnCall _ _ _ => rfl
  | Throwing _ _ _ _ => rfl

theorem wp_loop_cons {ps rs : Nat} {body rest : Program} {Q : Assertion α}
    (Inv : AssertionF α) (μ : Store α → Locals → Nat)
    (hInit : Inv st s)
    (hStep : ∀ st s, Inv st s →
        wp m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wp m rest Q st'
                { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s'     =>
              -- Next iteration runs with the loop's trimmed stack
              -- (top `ps` values become the new params, rest of entry
              -- stack is restored). The invariant must hold *there*.
              Inv st' { s' with values := s'.values.take ps ++ s.values.drop ps }
              ∧ μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } < μ st s
            | .Break (k+1) st' s' => Q (.Break k st' s')
            | other              => Q other)
          st s env) :
    wp m (.loop ps rs body :: rest) Q st s env := by
  suffices key : ∀ n, ∀ st s, Inv st s → μ st s = n →
      wp m (.loop ps rs body :: rest) Q st s env by
    exact key _ st s hInit rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro st s hInv hμ
    refine wp_of_body_dispatch (hStep st s hInv) ?_ ?_ ?_ ?_ ?_
    · -- Forwarded continuations: the loop is transparent to them.
      intro f cont hcont hbody
      cases cont <;>
        first
          | exact (hcont : False).elim
          | rw [exec_loop_cons_unfold, hbody]
    · intro cont hcont hQ
      cases cont <;>
        first
          | exact (hcont : False).elim
          | exact hQ
    · -- Fall-through leaves the loop and carries on with `rest`.
      intro N st' s' hQ hstable
      refine wp_of_eventually_eq (N := N + 1) ?_ hQ
      intro fuel hfuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_loop_cons_unfold, hstable f (by omega)]
    · -- `br 0` re-enters the loop: the invariant holds again on the trimmed
      -- stack and the measure has dropped, so the induction hypothesis applies.
      -- The re-entry is the one place where the two sides run at different
      -- fuel: the inner `execOne` gets `f`, the recursive `exec` gets `f + 1`.
      intro N st' s' hQ hstable
      have hQ' : Inv st' { s' with values := s'.values.take ps ++ s.values.drop ps }
          ∧ μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } < μ st s := hQ
      obtain ⟨hInv', hμ_lt⟩ := hQ'
      set trimmed : Locals :=
        { s' with values := s'.values.take ps ++ s.values.drop ps } with htrimmed
      have hμ_lt' : μ st' trimmed < n := by omega
      have hIH := IH (μ st' trimmed) hμ_lt' st' trimmed hInv' rfl
      unfold wp at hIH ⊢
      obtain ⟨N_inner, hN_inner⟩ := hIH
      refine ⟨max (N + 1) (N_inner + 1), fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_loop_cons_unfold, hstable f (by omega)]
      simp only
      by_cases hOf : execOne f m st' trimmed (.loop ps rs body) env = .OutOfFuel
      · rw [hOf]
        have hf_eq : exec f m st' trimmed (.loop ps rs body :: rest) env = .OutOfFuel := by
          simp only [exec, hOf]
        have hres := hN_inner f (by omega)
        rw [hf_eq] at hres
        exact hres
      · have h_mono : execOne (f+1) m st' trimmed (.loop ps rs body) env = execOne f m st' trimmed (.loop ps rs body) env :=
          execOne_fuel_mono (Nat.le_succ _) hOf
        have h_unfold : exec (f+1) m st' trimmed (.loop ps rs body :: rest) env =
              (match execOne (f+1) m st' trimmed (.loop ps rs body) env with
               | .Fallthrough r s => exec (f+1) m r s rest env
               | other => other) := by
          simp only [exec]; rfl
        have h_eq : exec (f+1) m st' trimmed (.loop ps rs body :: rest) env =
              (match execOne f m st' trimmed (.loop ps rs body) env with
               | .Fallthrough r s => exec (f+1) m r s rest env
               | other => other) := by rw [h_unfold, h_mono]
        rw [← h_eq]
        exact hN_inner (f+1) (by omega)
    · -- An outer break sheds one level and propagates.
      intro N k st' s' hQ hstable
      refine wp_of_eventually_const (N := N + 1) (cont := .Break k st' s') ?_ hQ
      intro fuel hfuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_loop_cons_unfold, hstable f (by omega)]

/-- For any fuel, executing a single `.br 0` is either `OutOfFuel` (when fuel = 0)
    or `Break 0 st s` (when fuel ≥ 1). -/
private theorem exec_br0 (f : Nat) (m : Module) (st : Store α) (s : Locals) :
    exec f m st s [.br 0] = (match f with | 0 => .OutOfFuel | _ + 1 => .Break 0 st s) := by
  cases f <;> simp [exec, execOne.eq_def]

/-- A loop with body `[.br 0]` always runs out of fuel: no amount of fuel
    suffices, since each iteration consumes one and returns to the same state. -/
private theorem execOne_loop_br0 (f : Nat) (m : Module) (st : Store α) (s : Locals) :
    execOne f m st s (.loop 0 0 [.br 0]) = .OutOfFuel := by
  induction f generalizing st s with
  | zero => simp [execOne.eq_def]
  | succ f' ih =>
    simp only [execOne_loop_succ]
    rw [exec_br0]
    cases f' with
    | zero => rfl
    | succ f'' => simpa using ih st s

/-- Therefore the entire `.loop 0 0 [.br 0] :: rest` program always runs out of fuel. -/
private theorem exec_loop_br0_cons (f : Nat) (m : Module) (st : Store α) (s : Locals)
    (rest : Program) :
    exec f m st s (.loop 0 0 [.br 0] :: rest) = .OutOfFuel := by
  cases f with
  | zero => simp [exec, execOne.eq_def]
  | succ f' =>
    simp only [exec]
    rw [execOne_loop_br0]

/-- A loop whose body is just `.br 0` never terminates: any `wp` for it forces
    `Q .OutOfFuel`. This is the framework-level statement that makes infinite
    loops unprovable for non-trivial posts. -/
theorem wp_loop_br0_cons (m : Module) (rest : Program) (Q : Assertion α) (st : Store α) (s : Locals) :
    wp m (.loop 0 0 [.br 0] :: rest) Q st s ↔ Q .OutOfFuel := by
  unfold wp
  constructor
  · rintro ⟨N, h⟩
    have := h N le_rfl
    rwa [exec_loop_br0_cons] at this
  · intro hQ
    exact ⟨0, fun fuel _ => by rw [exec_loop_br0_cons]; exact hQ⟩

end Wasm
