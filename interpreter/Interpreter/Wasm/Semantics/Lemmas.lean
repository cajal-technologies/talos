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
    (∀ (m : Module) (env : HostEnv α) (st : Store α) (s : Locals)
        (inst : Instruction) (f₂ : Nat),
        f₁ ≤ f₂ → execOne f₁ m st s inst env ≠ .OutOfFuel →
        execOne f₂ m st s inst env = execOne f₁ m st s inst env) ∧
    (∀ (m : Module) (env : HostEnv α) (st : Store α) (s : Locals)
        (p : Program) (f₂ : Nat),
        f₁ ≤ f₂ → exec f₁ m st s p env ≠ .OutOfFuel →
        exec f₂ m st s p env = exec f₁ m st s p env) ∧
    (∀ (m : Module) (env : HostEnv α) (id : Nat) (initial : Store α)
        (args : List Value) (f₂ : Nat),
        f₁ ≤ f₂ → run f₁ m id initial args env ≠ .OutOfFuel →
        run f₂ m id initial args env = run f₁ m id initial args env) := by
  intro f₁
  induction f₁ with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro m env st s inst f₂ _ hne
      cases inst <;> simp only [execOne] at hne <;> exact absurd rfl hne
    · intro m env st s p f₂ _ hne
      cases p with
      | nil => simp only [exec]
      | cons inst rest =>
        cases inst <;> simp only [exec, execOne] at hne <;> exact absurd rfl hne
    · intro m env id initial args f₂ _ hne
      simp only [run]
      rcases hImp : m.imports[id]? with _ | imp
      · -- wasm path: the in-module function index space.
        simp only []
        rcases h : m.funcs[id - m.imports.length]? with _ | f
        · rfl
        · simp only [run, hImp, h] at hne
          cases hbody : f.body with
          | nil => simp only [exec, hbody]
          | cons inst rest =>
            rw [hbody] at hne
            cases inst <;> simp only [exec, execOne] at hne <;> exact absurd rfl hne
      · -- host path: result is fuel-independent, both sides agree by reflexivity.
        rfl
  | succ k ih =>
    obtain ⟨ihOne, ihExec, ihRun⟩ := ih
    -- Step 1: prove execOne at fuel k+1.
    have monoOne :
        ∀ (m : Module) (env : HostEnv α) (st : Store α) (s : Locals)
          (inst : Instruction) (f₂ : Nat),
          k + 1 ≤ f₂ → execOne (k + 1) m st s inst env ≠ .OutOfFuel →
          execOne f₂ m st s inst env = execOne (k + 1) m st s inst env := by
      intro m env st s inst f₂ hle hne
      obtain ⟨k', rfl⟩ : ∃ k', f₂ = k' + 1 := ⟨f₂ - 1, by omega⟩
      have hk' : k ≤ k' := by omega
      cases inst with
      | block ps rs body =>
        simp only [execOne]
        have hexec : exec k m st s body env ≠ .OutOfFuel := by
          intro h; apply hne; simp only [execOne, h]
        rw [ihExec m env st s body k' hk' hexec]
      | loop ps rs body =>
        simp only [execOne]
        have hexec : exec k m st s body env ≠ .OutOfFuel := by
          intro h; apply hne; simp only [execOne, h]
        rw [ihExec m env st s body k' hk' hexec]
        rcases hres : exec k m st s body env with ⟨st', s'⟩ | ⟨n, st', s'⟩ | ⟨st', vs⟩ | msg | msg | _
        · rfl
        · cases n with
          | zero =>
            have hrec : execOne k m st'
                { s' with values := s'.values.take ps ++ s.values.drop ps }
                (.loop ps rs body) env ≠ .OutOfFuel := by
              intro h
              apply hne
              simp only [execOne, hres]
              exact h
            exact ihOne m env st'
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
              have hexec : exec k m st { s with values := vs } thn env ≠ .OutOfFuel := by
                intro h
                apply hne
                simp only [execOne, hvals, if_pos hc, h]
              rw [ihExec m env st { s with values := vs } thn k' hk' hexec]
            · simp only [if_neg hc]
              have hexec : exec k m st { s with values := vs } els env ≠ .OutOfFuel := by
                intro h
                apply hne
                simp only [execOne, hvals, if_neg hc, h]
              rw [ihExec m env st { s with values := vs } els k' hk' hexec]
          | i64 _ => rfl
          | f32 _ => rfl
          | f64 _ => rfl
          | funcref _ => rfl
      | call id =>
        simp only [execOne]
        have hrun : run k m id st s.values env ≠ .OutOfFuel := by
          intro h; apply hne; simp only [execOne, h]
        rw [ihRun m env id st s.values k' hk' hrun]
      | callIndirect ti tj =>
        -- The two sides differ only in the `run k'` vs `run k` deep
        -- inside; the wrapping match structure (on stack head, table
        -- slot, function/type lookups, and signature check) is the same.
        -- Case-split each discriminant; the non-recursive arms close by
        -- `rfl` (both sides reduce to the same trap/invalid), and the
        -- signature-matched arm uses `ihRun` to fold `run k' = run k`.
        rcases hvals : s.values with _ | ⟨v, rest⟩
        · simp only [execOne, hvals]
        · cases hv : v with
          | i64 _    => simp only [execOne, hvals, hv]
          | f32 _    => simp only [execOne, hvals, hv]
          | f64 _    => simp only [execOne, hvals, hv]
          | funcref _ => simp only [execOne, hvals, hv]
          | i32 i =>
            rcases htbl : st.tables[tj]? with _ | tbl
            · simp only [execOne, hvals, hv, htbl]
            · rcases hslot : tbl[i.toNat]? with _ | slot
              · simp only [execOne, hvals, hv, htbl, hslot]
              · rcases hslot' : slot with _ | fid
                · simp only [execOne, hvals, hv, htbl, hslot, hslot']
                · rcases hfn : m.funcSig? fid with _ | fn
                  · simp only [execOne, hvals, hv, htbl, hslot, hslot', hfn]
                  · rcases hty : m.types[ti]? with _ | ty
                    · simp only [execOne, hvals, hv, htbl, hslot, hslot', hfn, hty]
                    · by_cases hsig :
                          fn.params = ty.params ∧ fn.results = ty.results
                      · have hrun : run k m fid st rest env ≠ .OutOfFuel := by
                          intro h; apply hne
                          simp only [execOne, hvals, hv, htbl, hslot, hslot',
                            hfn, hty, if_pos hsig, h]
                        simp only [execOne, hvals, hv, htbl, hslot, hslot',
                          hfn, hty, if_pos hsig,
                          ihRun m env fid st rest k' hk' hrun]
                      · simp only [execOne, hvals, hv, htbl, hslot, hslot',
                          hfn, hty, if_neg hsig]
      | _ => simp only [execOne]
    -- Step 2: prove exec at fuel k+1 using monoOne.
    have monoExec :
        ∀ (m : Module) (env : HostEnv α) (st : Store α) (s : Locals)
          (p : Program) (f₂ : Nat),
          k + 1 ≤ f₂ → exec (k + 1) m st s p env ≠ .OutOfFuel →
          exec f₂ m st s p env = exec (k + 1) m st s p env := by
      intro m env st s p f₂ hle hne
      induction p generalizing st s with
      | nil => simp only [exec]
      | cons inst rest ihRest =>
        simp only [exec] at hne ⊢
        have hOne : execOne (k+1) m st s inst env ≠ .OutOfFuel := by
          intro h; rw [h] at hne; exact hne rfl
        rw [monoOne m env st s inst f₂ hle hOne]
        rcases hres : execOne (k+1) m st s inst env with ⟨st', s'⟩ | ⟨n, st', s'⟩ | ⟨st', vs⟩ | msg | msg | _
        · -- Fallthrough
          have hrest : exec (k+1) m st' s' rest env ≠ .OutOfFuel := by
            rw [hres] at hne; exact hne
          exact ihRest st' s' hrest
        all_goals rfl
    refine ⟨monoOne, monoExec, ?_⟩
    -- Step 3: run at fuel k+1.
    intro m env id initial args f₂ hle hne
    simp only [run]
    rcases hImp : m.imports[id]? with _ | imp
    · -- wasm path
      simp only []
      rcases h : m.funcs[id - m.imports.length]? with _ | f
      · rfl
      · simp only
        have hexec : exec (k+1) m initial (f.toLocals (args.take f.numParams).reverse) f.body env ≠ .OutOfFuel := by
          intro hOOF
          apply hne
          simp only [run, hImp, h, hOOF]
        rw [monoExec _ _ _ _ _ f₂ hle hexec]
    · -- host path: result is fuel-independent.
      rfl

theorem execOne_fuel_mono
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {inst : Instruction} {f₁ f₂ : Nat}
    (hle : f₁ ≤ f₂) (hne : execOne f₁ m st s inst env ≠ .OutOfFuel) :
    execOne f₂ m st s inst env = execOne f₁ m st s inst env :=
  (fuel_mono_aux f₁).1 m env st s inst f₂ hle hne

theorem exec_fuel_mono
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {p : Program} {f₁ f₂ : Nat}
    (hle : f₁ ≤ f₂) (hne : exec f₁ m st s p env ≠ .OutOfFuel) :
    exec f₂ m st s p env = exec f₁ m st s p env :=
  (fuel_mono_aux f₁).2.1 m env st s p f₂ hle hne

theorem run_fuel_mono
    {m : Module} {env : HostEnv α} {id : Nat} {initial : Store α}
    {args : List Value} {f₁ f₂ : Nat}
    (hle : f₁ ≤ f₂) (hne : run f₁ m id initial args env ≠ .OutOfFuel) :
    run f₂ m id initial args env = run f₁ m id initial args env :=
  (fuel_mono_aux f₁).2.2 m env id initial args f₂ hle hne

/-! ## Control-flow unfoldings

The structured-control arms (`block`, `loop`, `iff`, `call`) decrement fuel
explicitly. These lemmas restate each arm's behaviour in a form that
exposes the body's `exec` call, which is what the wp framework rules need. -/

theorem exec_block_cons
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {ps rs : Nat} {body rest : Program} {fuel : Nat} :
    exec (fuel + 1) m st s (.block ps rs body :: rest) env =
      (match exec fuel m st s body env with
       | .Break 0 st' s'       =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ s.values.drop ps } rest env
       | .Break (k + 1) st' s' => .Break k st' s'
       | .Fallthrough st' s'   =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ s.values.drop ps } rest env
       | other                => other) := by
  simp only [exec, execOne]
  rcases exec fuel m st s body env with _ | ⟨n, _, _⟩ | _ | _ | _ | _
  · rfl
  · cases n <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem exec_iff_cons
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {ps rs : Nat} {thn els rest : Program} {fuel : Nat}
    {c : UInt32} {vs : List Value}
    (hStack : s.values = .i32 c :: vs) :
    exec (fuel + 1) m st s (.iff ps rs thn els :: rest) env =
      (match exec fuel m st { s with values := vs }
                (if c ≠ 0 then thn else els) env with
       | .Break 0 st' s'       =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ vs.drop ps } rest env
       | .Break (k + 1) st' s' => .Break k st' s'
       | .Fallthrough st' s'   =>
         exec (fuel + 1) m st'
           { s' with values := s'.values.take rs ++ vs.drop ps } rest env
       | other                => other) := by
  simp only [exec, execOne, hStack]
  by_cases hc : c ≠ 0
  all_goals first
    | (simp only [if_pos hc]
       rcases exec fuel m st { s with values := vs } thn env with _ | ⟨n, _, _⟩ | _ | _ | _ | _
       · rfl
       · cases n <;> rfl
       all_goals rfl)
    | (simp only [if_neg hc]
       rcases exec fuel m st { s with values := vs } els env with _ | ⟨n, _, _⟩ | _ | _ | _ | _
       · rfl
       · cases n <;> rfl
       all_goals rfl)

theorem exec_call_cons
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {id : Nat} {rest : Program} {fuel : Nat} :
    exec (fuel + 1) m st s (.call id :: rest) env =
      (match run fuel m id st s.values env with
       | .Success vs st' => exec (fuel + 1) m st' { s with values := vs } rest env
       | .Trap st' msg   => .Trap st' msg
       | .Invalid msg    => .Invalid msg
       | .OutOfFuel      => .OutOfFuel) := by
  simp only [exec, execOne]
  rcases run fuel m id st s.values env with _ | _ | _ | _ <;> rfl

/-- Specialised characterisation of `exec` on a `.call id :: rest` whose
target `id` falls inside the imports range. Exposes the host's `invoke`
result directly so wp-level reasoning about host calls (see
`wp_call_host_cons`) can step over the dispatch without going through
the generic `run` characterisation. -/
theorem exec_call_host_cons
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {id : Nat} {imp : ImportDecl} {hf : HostFn α}
    {rest : Program} {fuel : Nat}
    (hImp : m.imports[id]? = some imp)
    (hEnv : env.funcs[id]? = some hf) :
    exec (fuel + 1) m st s (.call id :: rest) env =
      (match hf.invoke st (s.values.take imp.params.length).reverse with
       | .Return vs st' =>
         exec (fuel + 1) m st'
           { s with values := vs.take imp.results.length
                          ++ s.values.drop imp.params.length }
           rest env
       | .Trap st' msg => .Trap st' msg) := by
  simp only [exec, execOne, run, hImp, hEnv]
  rcases hf.invoke st (s.values.take imp.params.length).reverse with _ | _ <;> rfl

/-- Specialised unfolding of `exec` on a `.callIndirect` head when the
operand stack starts with an `i32` selector, the table+slot resolve to
a non-null `funcref`, and the target function's signature matches the
declared type. The WP rule consumes this lemma to bridge between the
indirect call site and `FuncSpec` of the resolved callee. -/
theorem exec_callIndirect_cons {α : Type}
    {m : Module} {env : HostEnv α} {st : Store α} {s : Locals}
    {ti tj : Nat} {rest : Program} {fuel : Nat}
    {i : UInt32} {vs0 : List Value}
    {tbl : TableInst} {fid : Nat} {fn : FuncType} {ty : FuncType}
    (hStack : s.values = .i32 i :: vs0)
    (hTbl  : st.tables[tj]? = some tbl)
    (hSlot : tbl[i.toNat]? = some (some fid))
    (hFn   : m.funcSig? fid = some fn)
    (hTy   : m.types[ti]? = some ty)
    (hSig  : fn.params = ty.params ∧ fn.results = ty.results) :
    exec (fuel + 1) m st s (.callIndirect ti tj :: rest) env =
      (match run fuel m fid st vs0 env with
       | .Success vs st' => exec (fuel + 1) m st' { s with values := vs } rest env
       | .Trap st' msg   => .Trap st' msg
       | .Invalid msg    => .Invalid msg
       | .OutOfFuel      => .OutOfFuel) := by
  simp only [exec, execOne, hStack, hTbl, hSlot, hFn, hTy, if_pos hSig]
  rcases run fuel m fid st vs0 env with _ | _ | _ | _ <;> rfl

/-! ## `run` characterisation -/

/-- Characterise `run` on the in-module (non-import) path. Holds when the
called index falls outside the imports range — exposed via the
`m.imports[id]? = none` hypothesis. For modules with `imports = []`,
`m.imports[id]?` is `none` for every `id`, and `id - m.imports.length`
reduces to `id`, so existing proofs `rw [run_eq] ; simp [hf]` keep
working with `hf : m.funcs[id]? = some f`. -/
theorem run_eq
    {m : Module} {id : Nat} {initial : Store α} {args : List Value} {fuel : Nat}
    {env : HostEnv α}
    (hImp : m.imports[id]? = none) :
    run fuel m id initial args env =
      (match m.funcs[id - m.imports.length]? with
       | none   => .Invalid "Function index out of bounds"
       | some f =>
         let callerRemainder := args.drop f.numParams
         match exec fuel m initial
                  (f.toLocals (args.take f.numParams).reverse) f.body env with
         | .Fallthrough st s =>
           .Success (s.values.take f.results.length ++ callerRemainder) st
         | .Return st vs     =>
           .Success (vs.take f.results.length ++ callerRemainder) st
         | .Break 0 st s     =>
           .Success (s.values.take f.results.length ++ callerRemainder) st
         | .Break (_+1) _ _  =>
           .Invalid "Unexpected break targeting scope out of function"
         | .Invalid msg      => .Invalid msg
         | .Trap st msg      => .Trap st msg
         | .OutOfFuel        => .OutOfFuel) := by
  simp only [run, hImp]
  rcases m.funcs[id - m.imports.length]? with _ | f
  · rfl
  · simp only
    rcases exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body env with
      _ | ⟨n, _, _⟩ | _ | _ | _ | _
    · rfl
    · cases n <;> rfl
    all_goals rfl

end Wasm
