import Interpreter.Wasm.Wp.Defs
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
private theorem exec_loop_cons_unfold (fuel : Nat) (m : Module) (st : Store α) (s : Locals)
    (ps rs : Nat) (body rest : Program) :
    exec (fuel + 1) m st s (.loop ps rs body :: rest) =
      (match exec fuel m st s body with
       | .Fallthrough st' s' =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ s.values.drop ps } rest
       | .Break 0 st' s' =>
           (match execOne fuel m st'
                    { s' with values := s'.values.take ps ++ s.values.drop ps }
                    (.loop ps rs body) with
            | .Fallthrough st'' s'' => exec (fuel + 1) m st'' s'' rest
            | other => other)
       | .Break (k+1) st' s' => .Break k st' s'
       | other => other) := by
  simp only [exec, execOne]
  rcases hb : exec fuel m st s body with ⟨_, _⟩ | ⟨n, _, _⟩ | ⟨_, _⟩ | _ | _ | _
  · rfl
  · cases n
    · simp only
      rcases hk : execOne fuel _ _ _ (.loop ps rs body)
        with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | _ | _ | _ <;> rfl
    · rfl
  all_goals rfl

theorem wp_loop_cons {ps rs : Nat} {body rest : Program} {Q : Assertion α}
    (Inv : AssertionF α) (μ : Store α → Locals → Nat)
    (hInit : Inv st s)
    (hStep : ∀ st s, Inv st s →
        wp m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wp m rest Q st'
                { s' with values := s'.values.take rs ++ s.values.drop ps }
            | .Break 0 st' s'     =>
              -- Next iteration runs with the loop's trimmed stack
              -- (top `ps` values become the new params, rest of entry
              -- stack is restored). The invariant must hold *there*.
              Inv st' { s' with values := s'.values.take ps ++ s.values.drop ps }
              ∧ μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } < μ st s
            | .Break (k+1) st' s' => Q (.Break k st' s')
            | other              => Q other)
          st s) :
    wp m (.loop ps rs body :: rest) Q st s := by
  unfold wp
  suffices key : ∀ n, ∀ st s, Inv st s → μ st s = n →
      ∃ N, ∀ fuel ≥ N, Q (exec fuel m st s (.loop ps rs body :: rest)) by
    exact key _ st s hInit rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro st s hInv hμ
    have hBody := hStep st s hInv
    unfold wp at hBody
    obtain ⟨Nb, hNb⟩ := hBody
    by_cases hOOF : ∀ f ≥ Nb, exec f m st s body = .OutOfFuel
    · refine ⟨Nb + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbf : exec f m st s body = .OutOfFuel := hOOF f (by omega)
      have hpre := hNb f (by omega)
      rw [hbf] at hpre
      rw [exec_loop_cons_unfold, hbf]
      exact hpre
    · push Not at hOOF
      obtain ⟨f₀, hf₀, hf₀_ne⟩ := hOOF
      have hk_stable : ∀ f' ≥ f₀, exec f' m st s body = exec f₀ m st s body := fun f' hf' =>
        exec_fuel_mono hf' hf₀_ne
      have hQ_at := hNb f₀ hf₀
      cases hk : exec f₀ m st s body with
      | OutOfFuel => exact absurd hk hf₀_ne
      | Fallthrough st' s' =>
        rw [hk] at hQ_at
        simp only at hQ_at
        obtain ⟨Nr, hNr⟩ := hQ_at
        refine ⟨max (f₀ + 1) Nr, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s body = .Fallthrough st' s' := by
          rw [hk_stable f (by omega), hk]
        rw [exec_loop_cons_unfold, hbody]
        simp only
        exact hNr _ (by omega)
      | Break k' st' s' =>
        cases k' with
        | zero =>
          rw [hk] at hQ_at
          simp only at hQ_at
          obtain ⟨hInv', hμ_lt⟩ := hQ_at
          set trimmed : Locals :=
            { s' with values := s'.values.take ps ++ s.values.drop ps } with htrimmed
          have hμ_lt' : μ st' trimmed < n := by omega
          obtain ⟨N_inner, hN_inner⟩ := IH (μ st' trimmed) hμ_lt' st' trimmed hInv' rfl
          refine ⟨max (f₀ + 1) (N_inner + 1), fun fuel hfuel => ?_⟩
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          have hbody : exec f m st s body = .Break 0 st' s' := by
            rw [hk_stable f (by omega), hk]
          rw [exec_loop_cons_unfold, hbody]
          simp only
          by_cases hOf : execOne f m st' trimmed (.loop ps rs body) = .OutOfFuel
          · rw [hOf]
            have hf_eq : exec f m st' trimmed (.loop ps rs body :: rest) = .OutOfFuel := by
              simp only [exec, hOf]
            have hIH := hN_inner f (by omega)
            rw [hf_eq] at hIH
            exact hIH
          · have h_mono : execOne (f+1) m st' trimmed (.loop ps rs body) = execOne f m st' trimmed (.loop ps rs body) :=
              execOne_fuel_mono (Nat.le_succ _) hOf
            have h_unfold : exec (f+1) m st' trimmed (.loop ps rs body :: rest) =
                  (match execOne (f+1) m st' trimmed (.loop ps rs body) with
                   | .Fallthrough r s => exec (f+1) m r s rest
                   | other => other) := by
              simp only [exec]; rfl
            have h_eq : exec (f+1) m st' trimmed (.loop ps rs body :: rest) =
                  (match execOne f m st' trimmed (.loop ps rs body) with
                   | .Fallthrough r s => exec (f+1) m r s rest
                   | other => other) := by rw [h_unfold, h_mono]
            rw [← h_eq]
            exact hN_inner (f+1) (by omega)
        | succ k' =>
          rw [hk] at hQ_at
          simp only at hQ_at
          refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          have hbody : exec f m st s body = .Break (k'+1) st' s' := by
            rw [hk_stable f (by omega), hk]
          rw [exec_loop_cons_unfold, hbody]
          simp only
          exact hQ_at
      | Return st' vs =>
        rw [hk] at hQ_at
        simp only at hQ_at
        refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s body = .Return st' vs := by
          rw [hk_stable f (by omega), hk]
        rw [exec_loop_cons_unfold, hbody]
        simp only
        exact hQ_at
      | Trap st' msg =>
        rw [hk] at hQ_at
        simp only at hQ_at
        refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s body = .Trap st' msg := by
          rw [hk_stable f (by omega), hk]
        rw [exec_loop_cons_unfold, hbody]
        simp only
        exact hQ_at
      | Invalid msg =>
        rw [hk] at hQ_at
        simp only at hQ_at
        refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s body = .Invalid msg := by
          rw [hk_stable f (by omega), hk]
        rw [exec_loop_cons_unfold, hbody]
        simp only
        exact hQ_at

/-- For any fuel, executing a single `.br 0` is either `OutOfFuel` (when fuel = 0)
    or `Break 0 st s` (when fuel ≥ 1). -/
private theorem exec_br0 (f : Nat) (m : Module) (st : Store α) (s : Locals) :
    exec f m st s [.br 0] = (match f with | 0 => .OutOfFuel | _ + 1 => .Break 0 st s) := by
  cases f <;> simp [exec, execOne]

/-- A loop with body `[.br 0]` always runs out of fuel: no amount of fuel
    suffices, since each iteration consumes one and returns to the same state. -/
private theorem execOne_loop_br0 (f : Nat) (m : Module) (st : Store α) (s : Locals) :
    execOne f m st s (.loop 0 0 [.br 0]) = .OutOfFuel := by
  induction f generalizing st s with
  | zero => simp [execOne]
  | succ f' ih =>
    simp only [execOne]
    rw [exec_br0]
    cases f' with
    | zero => rfl
    | succ f'' => simpa using ih st s

/-- Therefore the entire `.loop 0 0 [.br 0] :: rest` program always runs out of fuel. -/
private theorem exec_loop_br0_cons (f : Nat) (m : Module) (st : Store α) (s : Locals)
    (rest : Program) :
    exec f m st s (.loop 0 0 [.br 0] :: rest) = .OutOfFuel := by
  cases f with
  | zero => simp [exec, execOne]
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
