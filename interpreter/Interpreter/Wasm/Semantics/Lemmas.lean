import Interpreter.Wasm.Semantics

/-!
# Bridge lemmas between the interpreter and the wp framework

Operational facts about `exec`, `execOne`, and `run` that the wp framework
factors through.
-/

namespace Wasm

/-! ## Fuel monotonicity

Once a run has succeeded with some amount of fuel (≠ `.OutOfFuel`), adding
more fuel doesn't change the answer. This is what makes the `∃ N, ∀ fuel ≥ N`
existential in `wp` well-behaved. -/

/-- Joint induction principle for fuel monotonicity of `execOne`, `exec`, and
`run`. Proved by induction on `f₁`; the three public theorems below are
one-line projections. -/
theorem fuel_mono_aux : ∀ (f₁ : Nat),
    (∀ (m : Module) (st : Store) (s : Locals) (inst : Instruction) (f₂ : Nat),
        f₁ ≤ f₂ → execOne f₁ m st s inst ≠ .OutOfFuel →
        execOne f₂ m st s inst = execOne f₁ m st s inst) ∧
    (∀ (m : Module) (st : Store) (s : Locals) (p : Program) (f₂ : Nat),
        f₁ ≤ f₂ → exec f₁ m st s p ≠ .OutOfFuel →
        exec f₂ m st s p = exec f₁ m st s p) ∧
    (∀ (m : Module) (id : Nat) (initial : Store) (args : List Value) (f₂ : Nat),
        f₁ ≤ f₂ → run f₁ m id initial args ≠ .OutOfFuel →
        run f₂ m id initial args = run f₁ m id initial args) := by
  intro f₁
  induction f₁ with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro m st s inst f₂ _ hne
      cases inst <;> simp only [execOne] at hne <;> exact absurd rfl hne
    · intro m st s p f₂ _ hne
      cases p with
      | nil => simp only [exec]
      | cons inst rest =>
        cases inst <;> simp only [exec, execOne] at hne <;> exact absurd rfl hne
    · intro m id initial args f₂ _ hne
      simp only [run]
      rcases h : m.funcs[id]? with _ | f
      · rfl
      · simp only [run, h] at hne
        cases hbody : f.body with
        | nil => simp only [exec, hbody]
        | cons inst rest =>
          rw [hbody] at hne
          cases inst <;> simp only [exec, execOne] at hne <;> exact absurd rfl hne
  | succ k ih =>
    obtain ⟨ihOne, ihExec, ihRun⟩ := ih
    -- Step 1: prove execOne at fuel k+1.
    have monoOne :
        ∀ (m : Module) (st : Store) (s : Locals) (inst : Instruction) (f₂ : Nat),
          k + 1 ≤ f₂ → execOne (k + 1) m st s inst ≠ .OutOfFuel →
          execOne f₂ m st s inst = execOne (k + 1) m st s inst := by
      intro m st s inst f₂ hle hne
      obtain ⟨k', rfl⟩ : ∃ k', f₂ = k' + 1 := ⟨f₂ - 1, by omega⟩
      have hk' : k ≤ k' := by omega
      cases inst with
      | block ps rs body =>
        simp only [execOne]
        have hexec : exec k m st s body ≠ .OutOfFuel := by
          intro h; apply hne; simp only [execOne, h]
        rw [ihExec m st s body k' hk' hexec]
      | loop ps rs body =>
        simp only [execOne]
        have hexec : exec k m st s body ≠ .OutOfFuel := by
          intro h; apply hne; simp only [execOne, h]
        rw [ihExec m st s body k' hk' hexec]
        rcases hres : exec k m st s body with ⟨st', s'⟩ | ⟨n, st', s'⟩ | ⟨st', vs⟩ | msg | msg | _
        · rfl
        · cases n with
          | zero =>
            have hrec : execOne k m st'
                { s' with values := s'.values.take ps ++ s.values.drop ps }
                (.loop ps rs body) ≠ .OutOfFuel := by
              intro h
              apply hne
              simp only [execOne, hres]
              exact h
            exact ihOne m st'
              { s' with values := s'.values.take ps ++ s.values.drop ps }
              (.loop ps rs body) k' hk' hrec
          | succ _ => rfl
        · rfl
        · rfl
        · rfl
        · exact absurd hres hexec
      | iff ps rs thn els =>
        simp only [execOne]
        rcases hvals : s.values with _ | ⟨v, vs⟩
        · rfl
        · cases v with
          | i32 c =>
            by_cases hc : c ≠ 0
            · simp only [if_pos hc]
              have hexec : exec k m st { s with values := vs } thn ≠ .OutOfFuel := by
                intro h
                apply hne
                simp only [execOne, hvals, if_pos hc, h]
              rw [ihExec m st { s with values := vs } thn k' hk' hexec]
            · simp only [if_neg hc]
              have hexec : exec k m st { s with values := vs } els ≠ .OutOfFuel := by
                intro h
                apply hne
                simp only [execOne, hvals, if_neg hc, h]
              rw [ihExec m st { s with values := vs } els k' hk' hexec]
          | i64 _ => rfl
      | call id =>
        simp only [execOne]
        have hrun : run k m id st s.values ≠ .OutOfFuel := by
          intro h; apply hne; simp only [execOne, h]
        rw [ihRun m id st s.values k' hk' hrun]
      | _ => simp only [execOne]
    -- Step 2: prove exec at fuel k+1 using monoOne.
    have monoExec :
        ∀ (m : Module) (st : Store) (s : Locals) (p : Program) (f₂ : Nat),
          k + 1 ≤ f₂ → exec (k + 1) m st s p ≠ .OutOfFuel →
          exec f₂ m st s p = exec (k + 1) m st s p := by
      intro m st s p f₂ hle hne
      induction p generalizing st s with
      | nil => simp only [exec]
      | cons inst rest ihRest =>
        simp only [exec] at hne ⊢
        have hOne : execOne (k+1) m st s inst ≠ .OutOfFuel := by
          intro h; rw [h] at hne; exact hne rfl
        rw [monoOne m st s inst f₂ hle hOne]
        rcases hres : execOne (k+1) m st s inst with ⟨st', s'⟩ | ⟨n, st', s'⟩ | ⟨st', vs⟩ | msg | msg | _
        · -- Fallthrough
          have hrest : exec (k+1) m st' s' rest ≠ .OutOfFuel := by
            rw [hres] at hne; exact hne
          exact ihRest st' s' hrest
        all_goals rfl
    refine ⟨monoOne, monoExec, ?_⟩
    -- Step 3: run at fuel k+1.
    intro m id initial args f₂ hle hne
    simp only [run]
    rcases h : m.funcs[id]? with _ | f
    · rfl
    · simp only
      have hexec : exec (k+1) m initial (f.toLocals (args.take f.numParams).reverse) f.body ≠ .OutOfFuel := by
        intro hOOF
        apply hne
        simp only [run, h, hOOF]
      rw [monoExec _ _ _ _ f₂ hle hexec]

theorem execOne_fuel_mono
    {m : Module} {st : Store} {s : Locals} {inst : Instruction} {f₁ f₂ : Nat}
    (hle : f₁ ≤ f₂) (hne : execOne f₁ m st s inst ≠ .OutOfFuel) :
    execOne f₂ m st s inst = execOne f₁ m st s inst :=
  (fuel_mono_aux f₁).1 m st s inst f₂ hle hne

theorem exec_fuel_mono
    {m : Module} {st : Store} {s : Locals} {p : Program} {f₁ f₂ : Nat}
    (hle : f₁ ≤ f₂) (hne : exec f₁ m st s p ≠ .OutOfFuel) :
    exec f₂ m st s p = exec f₁ m st s p :=
  (fuel_mono_aux f₁).2.1 m st s p f₂ hle hne

theorem run_fuel_mono
    {m : Module} {id : Nat} {initial : Store} {args : List Value} {f₁ f₂ : Nat}
    (hle : f₁ ≤ f₂) (hne : run f₁ m id initial args ≠ .OutOfFuel) :
    run f₂ m id initial args = run f₁ m id initial args :=
  (fuel_mono_aux f₁).2.2 m id initial args f₂ hle hne

/-! ## Control-flow unfoldings

The structured-control arms (`block`, `loop`, `iff`, `call`) decrement fuel
explicitly. These lemmas restate each arm's behaviour in a form that
exposes the body's `exec` call, which is what the wp framework rules need. -/

theorem exec_block_cons
    {m : Module} {st : Store} {s : Locals}
    {ps rs : Nat} {body rest : Program} {fuel : Nat} :
    exec (fuel + 1) m st s (.block ps rs body :: rest) =
      (match exec fuel m st s body with
       | .Break 0 st' s'       =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ s.values.drop ps } rest
       | .Break (k + 1) st' s' => .Break k st' s'
       | .Fallthrough st' s'   =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ s.values.drop ps } rest
       | other                => other) := by
  simp only [exec, execOne]
  rcases exec fuel m st s body with _ | ⟨n, _, _⟩ | _ | _ | _ | _
  · rfl
  · cases n <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem exec_iff_cons
    {m : Module} {st : Store} {s : Locals}
    {ps rs : Nat} {thn els rest : Program} {fuel : Nat}
    {c : UInt32} {vs : List Value}
    (hStack : s.values = .i32 c :: vs) :
    exec (fuel + 1) m st s (.iff ps rs thn els :: rest) =
      (match exec fuel m st { s with values := vs }
                (if c ≠ 0 then thn else els) with
       | .Break 0 st' s'       =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ vs.drop ps } rest
       | .Break (k + 1) st' s' => .Break k st' s'
       | .Fallthrough st' s'   =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ vs.drop ps } rest
       | other                => other) := by
  simp only [exec, execOne, hStack]
  by_cases hc : c ≠ 0
  all_goals first
    | (simp only [if_pos hc]
       rcases exec fuel m st { s with values := vs } thn with _ | ⟨n, _, _⟩ | _ | _ | _ | _
       · rfl
       · cases n <;> rfl
       all_goals rfl)
    | (simp only [if_neg hc]
       rcases exec fuel m st { s with values := vs } els with _ | ⟨n, _, _⟩ | _ | _ | _ | _
       · rfl
       · cases n <;> rfl
       all_goals rfl)

theorem exec_call_cons
    {m : Module} {st : Store} {s : Locals}
    {id : Nat} {rest : Program} {fuel : Nat} :
    exec (fuel + 1) m st s (.call id :: rest) =
      (match run fuel m id st s.values with
       | .Success vs st' => exec (fuel + 1) m st' { s with values := vs } rest
       | .Trap st' msg   => .Trap st' msg
       | .Invalid msg    => .Invalid msg
       | .OutOfFuel      => .OutOfFuel) := by
  simp only [exec, execOne]
  rcases run fuel m id st s.values with _ | _ | _ | _ <;> rfl

/-! ## `run` characterisation -/

theorem run_eq
    {m : Module} {id : Nat} {initial : Store} {args : List Value} {fuel : Nat} :
    run fuel m id initial args =
      (match m.funcs[id]? with
       | none   => .Invalid "Function index out of bounds"
       | some f =>
         let callerRemainder := args.drop f.numParams
         match exec fuel m initial
                  (f.toLocals (args.take f.numParams).reverse) f.body with
         | .Fallthrough st s =>
           .Success (s.values.take f.results.length ++ callerRemainder) st
         | .Return st vs     =>
           .Success (vs.take f.results.length ++ callerRemainder) st
         | .Break _ st _     => .Trap st "Unexpected break targeting function"
         | .Invalid msg      => .Invalid msg
         | .Trap st msg      => .Trap st msg
         | .OutOfFuel        => .OutOfFuel) := by
  simp only [run]
  rcases m.funcs[id]? with _ | f
  · rfl
  · simp only
    rcases exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body with
      _ | _ | _ | _ | _ | _ <;> rfl

end Wasm
