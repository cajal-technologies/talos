import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas

/-! ### Block / if-then-else: structural, no measure required.

    Neither iterates; control either falls through, breaks out at level 0
    (exiting the construct), or propagates an outer break/return/trap. The
    rules are one-sided sufficient conditions — provide the body's `wp`
    against the right outcome continuation. -/

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
  unfold wp at h ⊢
  obtain ⟨Nb, hN⟩ := h
  by_cases hOOF : ∀ f ≥ Nb, exec f m st s body env = .OutOfFuel
  · -- body always OutOfFuel: block propagates OutOfFuel; hN gives Q OutOfFuel.
    refine ⟨Nb + 1, fun fuel hfuel => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hbf : exec f m st s body env = .OutOfFuel := hOOF f (by omega)
    have hpre := hN f (by omega)
    rw [hbf] at hpre
    rw [exec_block_cons, hbf]
    exact hpre
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hf₀_ne⟩ := hOOF
    have hk_stable : ∀ f' ≥ f₀, exec f' m st s body env = exec f₀ m st s body env := fun f' hf' =>
      exec_fuel_mono hf' hf₀_ne
    have hQ_at := hN f₀ hf₀
    cases hk : exec f₀ m st s body env with
    | OutOfFuel => exact absurd hk hf₀_ne
    | Fallthrough r' s' =>
      rw [hk] at hQ_at
      obtain ⟨Nr, hNr⟩ := hQ_at
      refine ⟨max (f₀ + 1) Nr, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s body env = .Fallthrough r' s' := by
        rw [hk_stable f (by omega), hk]
      rw [exec_block_cons, hbody]
      exact hNr _ (by omega)
    | Break n r' s' =>
      cases n with
      | zero =>
        rw [hk] at hQ_at
        obtain ⟨Nr, hNr⟩ := hQ_at
        refine ⟨max (f₀ + 1) Nr, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s body env = .Break 0 r' s' := by
          rw [hk_stable f (by omega), hk]
        rw [exec_block_cons, hbody]
        exact hNr _ (by omega)
      | succ n' =>
        rw [hk] at hQ_at
        refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s body env = .Break (n'+1) r' s' := by
          rw [hk_stable f (by omega), hk]
        rw [exec_block_cons, hbody]
        exact hQ_at
    | Return r' vs =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s body env = .Return r' vs := by
        rw [hk_stable f (by omega), hk]
      rw [exec_block_cons, hbody]
      exact hQ_at
    | Trap r' msg =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s body env = .Trap r' msg := by
        rw [hk_stable f (by omega), hk]
      rw [exec_block_cons, hbody]
      exact hQ_at
    | Invalid msg =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s body env = .Invalid msg := by
        rw [hk_stable f (by omega), hk]
      rw [exec_block_cons, hbody]
      exact hQ_at
    | ReturnCall fid st' vs =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s body env = .ReturnCall fid st' vs := by
        rw [hk_stable f (by omega), hk]
      rw [exec_block_cons, hbody]
      exact hQ_at

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
  unfold wp at hBody ⊢
  set body := if c ≠ 0 then thn else els with hbody_def
  set s' : Locals := { s with values := vs } with hs'_def
  obtain ⟨Nb, hN⟩ := hBody
  by_cases hOOF : ∀ f ≥ Nb, exec f m st s' body env = .OutOfFuel
  · refine ⟨Nb + 1, fun fuel hfuel => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hbf : exec f m st s' body env = .OutOfFuel := hOOF f (by omega)
    have hpre := hN f (by omega)
    rw [hbf] at hpre
    rw [exec_iff_cons hStack, hbf]
    exact hpre
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hf₀_ne⟩ := hOOF
    have hk_stable : ∀ f' ≥ f₀, exec f' m st s' body env = exec f₀ m st s' body env := fun f' hf' =>
      exec_fuel_mono hf' hf₀_ne
    have hQ_at := hN f₀ hf₀
    cases hk : exec f₀ m st s' body env with
    | OutOfFuel => exact absurd hk hf₀_ne
    | Fallthrough r' s'' =>
      rw [hk] at hQ_at
      obtain ⟨Nr, hNr⟩ := hQ_at
      refine ⟨max (f₀ + 1) Nr, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s' body env = .Fallthrough r' s'' := by
        rw [hk_stable f (by omega), hk]
      rw [exec_iff_cons hStack, hbody]
      exact hNr _ (by omega)
    | Break n r' s'' =>
      cases n with
      | zero =>
        rw [hk] at hQ_at
        obtain ⟨Nr, hNr⟩ := hQ_at
        refine ⟨max (f₀ + 1) Nr, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s' body env = .Break 0 r' s'' := by
          rw [hk_stable f (by omega), hk]
        rw [exec_iff_cons hStack, hbody]
        exact hNr _ (by omega)
      | succ n' =>
        rw [hk] at hQ_at
        refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hbody : exec f m st s' body env = .Break (n'+1) r' s'' := by
          rw [hk_stable f (by omega), hk]
        rw [exec_iff_cons hStack, hbody]
        exact hQ_at
    | Return r' vs' =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s' body env = .Return r' vs' := by
        rw [hk_stable f (by omega), hk]
      rw [exec_iff_cons hStack, hbody]
      exact hQ_at
    | Trap r' msg =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s' body env = .Trap r' msg := by
        rw [hk_stable f (by omega), hk]
      rw [exec_iff_cons hStack, hbody]
      exact hQ_at
    | Invalid msg =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s' body env = .Invalid msg := by
        rw [hk_stable f (by omega), hk]
      rw [exec_iff_cons hStack, hbody]
      exact hQ_at
    | ReturnCall fid st'' vs' =>
      rw [hk] at hQ_at
      refine ⟨f₀ + 1, fun fuel hfuel => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hbody : exec f m st s' body env = .ReturnCall fid st'' vs' := by
        rw [hk_stable f (by omega), hk]
      rw [exec_iff_cons hStack, hbody]
      exact hQ_at

end Wasm
