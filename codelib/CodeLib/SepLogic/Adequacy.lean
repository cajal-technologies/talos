import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import Iris.BI.Lib.Fixpoint
import Interpreter.Wasm

namespace Wasm.SepLogic
open Iris Wasm Std
variable [inst : WasmHeapGS]

structure WasmState where
  m      : Module
  st     : Store Unit
  locals : Locals
  prog   : Program
  env    : HostEnv Unit
  Q      : Store Unit → List Value → Prop

def wp_wasm_F (Φ : LeibnizO WasmState → IProp WasmHeapGF)
    (s : LeibnizO WasmState) : IProp WasmHeapGF :=
  let ws := s.car
  match ws.prog with
  | [] =>
      iprop% ⌜ws.Q ws.st []⌝
  | .ret :: _ =>
      iprop% ⌜ws.Q ws.st ws.locals.values⌝
  | instr :: rest =>
      iprop% ∀ σ : WasmHeapMap (Option UInt8),
        genHeapInterp σ ==∗
          ∃ σ' : WasmHeapMap (Option UInt8),
          ∃ st' : Store Unit,
          ∃ locals' : Locals,
            ⌜execOne 1 ws.m ws.st ws.locals instr ws.env = .Fallthrough st' locals'⌝ ∗
            genHeapInterp σ' ∗
            Φ ⟨{ m := ws.m, st := st', locals := locals',
                 prog := rest, env := ws.env, Q := ws.Q }⟩

def wp_wasm (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : IProp WasmHeapGF :=
  bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩

instance instBIMonoPredWasmF :
    BIMonoPred (PROP := IProp WasmHeapGF) (A := LeibnizO WasmState) wp_wasm_F where
  mono_pred := by
    intro Φ Ψ hΦ hΨ
    iintro #HΦΨ %s
    obtain ⟨ws⟩ := s
    unfold wp_wasm_F
    simp only [LeibnizO.car]
    split
    · iintro H; iexact H
    · iintro H; iexact H
    · next instr rest =>
      iintro Hwp
      iintro %σ₀
      iintro Hσ₀
      imod Hwp $$ % σ₀ Hσ₀ with ⟨%σ', %st₁, %locals₁, hexec, Hσ', HΦ⟩
      imodintro
      iexists σ', st₁, locals₁
      isplitl [hexec]
      · iexact hexec
      · isplitl [Hσ']
        · iexact Hσ'
        · iapply HΦΨ
          iexact HΦ
  mono_pred_ne.ne _ _ _ H :=
    (OFE.eq_of_eqv (OFE.discrete H)) ▸ OFE.Dist.rfl

private theorem exec_cons {m : Module} {st : Store Unit} {locals : Locals}
    {env : HostEnv Unit} {head : Instruction} {rest : Program}
    {st₁ : Store Unit} {locals₁ : Locals}
    {Q : Store Unit → List Value → Prop}
    (hexec : execOne 1 m st locals head env = .Fallthrough st₁ locals₁)
    (hrest : wp_wasm_prop m st₁ locals₁ rest env Q) :
    wp_wasm_prop m st locals (head :: rest) env Q := by
  obtain ⟨n, hn⟩ := hrest
  refine ⟨n + 1, ?_⟩
  have hne1 : execOne 1 m st locals head env ≠ .OutOfFuel := by simp [hexec]
  have h1 : execOne (n + 1) m st locals head env = .Fallthrough st₁ locals₁ :=
    (execOne_fuel_mono (by omega) hne1).trans hexec
  have hne2 : exec n m st₁ locals₁ rest env ≠ .OutOfFuel := by
    intro h; simp [h] at hn
  have h2 : exec (n + 1) m st₁ locals₁ rest env = exec n m st₁ locals₁ rest env :=
    exec_fuel_mono (by omega) hne2
  simp only [exec, h1, h2]
  exact hn

theorem wp_wasm_step
    {m : Module} {st st' : Store Unit} {locals locals' : Locals}
    {instr₀ : Instruction} {rest₀ : Program}
    {env : HostEnv Unit} {Q : Store Unit → List Value → Prop}
    (hexec : execOne 1 m st locals instr₀ env = .Fallthrough st' locals')
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st' locals' rest₀ env Q) :
    ⊢ wp_wasm m st locals (instr₀ :: rest₀) env Q := by
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  -- simp only (not unfold): leaves non-applied wp_wasm_F inside bi_least_fixpoint named,
  -- so iexact Hwp can unify the recursive call after unfold wp_wasm at hstep below
  simp only [wp_wasm_F]
  split
  · -- nil: instr₀ :: rest₀ = [] is impossible
    contradiction
  · -- ret: instr₀ = .ret, contradicts hexec
    next tail h =>
    obtain ⟨rfl, _⟩ := List.cons.inj h
    simp [execOne] at hexec
  · -- general: subst equalities, then iris proof
    next instr rest h =>
    obtain ⟨h1, h2⟩ := List.cons.inj h
    subst h1; subst h2
    -- unfold wp_wasm in the Lean hypothesis before entering iris mode
    -- so Hwp arrives with the bi_least_fixpoint form iexact can unify
    unfold wp_wasm at hstep
    iintro %σ Hσ
    imod (hstep σ) $$ Hσ with ⟨%σ', Hσ', Hwp⟩
    imodintro
    iexists σ', st', locals'
    isplitl []
    · exact BI.pure_intro hexec
    · isplitl [Hσ']
      · iexact Hσ'
      · iexact Hwp

theorem wasm_adequacy
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ : WasmHeapMap (Option UInt8)) :
    genHeapInterp σ ∗ wp_wasm m st locals prog env Q ⊢
      ⌜wp_wasm_prop m st locals prog env Q⌝ := by
  unfold wp_wasm
  let Ψ : LeibnizO WasmState → IProp WasmHeapGF :=
    fun s => iprop% ∀ σ' : WasmHeapMap (Option UInt8), genHeapInterp σ' -∗
      ⌜wp_wasm_prop s.car.m s.car.st s.car.locals s.car.prog s.car.env s.car.Q⌝
  haveI hΨ : OFE.NonExpansive Ψ :=
    ⟨fun _ _ _ H => (OFE.eq_of_eqv (OFE.discrete H)) ▸ OFE.Dist.rfl⟩
  have hstep : ⊢ □ (∀ y : LeibnizO WasmState, wp_wasm_F Ψ y -∗ Ψ y) := by
    iintro !> %s
    obtain ⟨⟨m', st', locals', prog', env', Q'⟩⟩ := s
    unfold wp_wasm_F Ψ
    simp only [LeibnizO.car]
    split
    · refine BI.entails_wand (BI.pure_elim' fun h =>
        BI.forall_intro fun _ => BI.wand_intro (BI.pure_intro ⟨0, ?_⟩))
      simp only [exec]; exact h
    · refine BI.entails_wand (BI.pure_elim' fun h =>
        BI.forall_intro fun _ => BI.wand_intro (BI.pure_intro ⟨1, ?_⟩))
      simp only [exec, execOne]; exact h
    · next instr rest =>
      iintro Hwp
      iintro %σ_any
      iintro Hσ_any
      imod Hwp $$ % σ_any Hσ_any with ⟨%σ₁, %st₁, %locals₁, hexec, Hσ₁, Hcont⟩
      icases hexec with %hexec_lean
      icases Hcont $$ % σ₁ Hσ₁ with %hwp_lean
      exact BI.pure_intro (exec_cons hexec_lean hwp_lean)
  have hfp : bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩ ⊢
      Ψ ⟨{ m, st, locals, prog, env, Q }⟩ :=
    BI.sep_elim_emp_valid_left hstep
      (BI.wand_elim ((BI.wand_entails (least_fixpoint_iter (F := wp_wasm_F))).trans
        (BI.forall_elim (⟨{ m, st, locals, prog, env, Q }⟩ : LeibnizO WasmState))))
  exact ((BI.sep_mono_right hfp).trans
    (BI.sep_mono_right (BI.forall_elim σ))).trans BI.wand_elim_right

-- call rule: if the callee terminates with a postcondition that implies the
-- continuation terminates, the whole call sequence terminates.
theorem wp_wasm_prop_call
    {m : Module} {st : Store Unit} {locals : Locals}
    {callid : Nat} {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (htw : TerminatesWith env m callid st locals.values
           (fun st' vs => wp_wasm_prop m st' { locals with values := vs } rest env Q)) :
    wp_wasm_prop m st locals (.call callid :: rest) env Q := by
  obtain ⟨N, hN⟩ := htw
  obtain ⟨vs', st', hrun, hwp⟩ := hN N le_rfl
  obtain ⟨fuel_rest, hfuel⟩ := hwp
  have hrun_ne : run N m callid st locals.values env ≠ .OutOfFuel := by
    rw [hrun]; intro h; cases h
  have hfuel_ne : exec fuel_rest m st' { locals with values := vs' } rest env ≠ .OutOfFuel := by
    intro h; simp only [h] at hfuel
  refine ⟨max N fuel_rest + 1, ?_⟩
  have hrun' : run (max N fuel_rest) m callid st locals.values env = .Success vs' st' :=
    (run_fuel_mono (Nat.le_max_left N fuel_rest) hrun_ne).trans hrun
  have hfuel' : exec (max N fuel_rest + 1) m st' { locals with values := vs' } rest env
      = exec fuel_rest m st' { locals with values := vs' } rest env :=
    exec_fuel_mono (by omega) hfuel_ne
  simp only [exec_call_cons, hrun', hfuel']
  exact hfuel

-- block rule: body either falls through or breaks to label 0;
-- both cases produce the same trimmed continuation locals.
theorem wp_wasm_prop_block
    {m : Module} {st : Store Unit} {locals : Locals}
    {bt bl : Nat} {body : Program} {rest : Program}
    {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (hbody : ∃ N, ∀ fuel ≥ N,
      (∃ st' s', exec fuel m st locals body env = .Fallthrough st' s' ∧
        wp_wasm_prop m st' { s' with values := s'.values.take bl ++ locals.values.drop bt }
          rest env Q) ∨
      (∃ st' s', exec fuel m st locals body env = .Break 0 st' s' ∧
        wp_wasm_prop m st' { s' with values := s'.values.take bl ++ locals.values.drop bt }
          rest env Q)) :
    wp_wasm_prop m st locals (.block bt bl body :: rest) env Q := by
  obtain ⟨N, hN⟩ := hbody
  rcases hN N le_rfl with ⟨st', s', hbody_result, hwp⟩ | ⟨st', s', hbody_result, hwp⟩ <;> {
    obtain ⟨fuel_rest, hfuel⟩ := hwp
    have hbody_ne : exec N m st locals body env ≠ .OutOfFuel := by
      rw [hbody_result]; intro h; cases h
    have hfuel_ne : exec fuel_rest m st'
        { s' with values := s'.values.take bl ++ locals.values.drop bt } rest env ≠ .OutOfFuel := by
      intro h; simp only [h] at hfuel
    refine ⟨max N fuel_rest + 1, ?_⟩
    have hbody' : exec (max N fuel_rest) m st locals body env = exec N m st locals body env :=
      exec_fuel_mono (Nat.le_max_left N fuel_rest) hbody_ne
    have hfuel' : exec (max N fuel_rest + 1) m st'
        { s' with values := s'.values.take bl ++ locals.values.drop bt } rest env =
        exec fuel_rest m st'
        { s' with values := s'.values.take bl ++ locals.values.drop bt } rest env :=
      exec_fuel_mono (by omega) hfuel_ne
    simp only [exec_block_cons, hbody', hbody_result, hfuel']
    exact hfuel }

-- loop rule: invariant I and measure μ; body either falls through (exit) or
-- breaks to label 0 (re-enter) with I re-established and μ decreased.
theorem wp_wasm_prop_loop
    {m : Module} {st : Store Unit} {locals : Locals}
    {ps rs : Nat} {body : Program} {rest : Program}
    {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (I : Store Unit → Locals → Prop)
    (μ : Store Unit → Locals → Nat)
    (hinit : I st locals)
    (hstep : ∀ stA locA, I stA locA →
      ∃ N, ∀ fuel ≥ N,
        (∃ stB sB, exec fuel m stA locA body env = .Fallthrough stB sB ∧
          wp_wasm_prop m stB { sB with values := sB.values.take rs ++ locA.values.drop ps }
            rest env Q) ∨
        (∃ stB sB, exec fuel m stA locA body env = .Break 0 stB sB ∧
          I stB { sB with values := sB.values.take ps ++ locA.values.drop ps } ∧
          μ stB { sB with values := sB.values.take ps ++ locA.values.drop ps } < μ stA locA) ∨
        (∃ stB vs, exec fuel m stA locA body env = .Return stB vs ∧
          Q stB vs)) :
    wp_wasm_prop m st locals (.loop ps rs body :: rest) env Q := by
  -- restate exec_loop_cons_unfold (private in Loop.lean) using execOne_loop_succ
  have exec_loop_unfold : ∀ (f : Nat) (stA : Store Unit) (sA : Locals),
      exec (f + 1) m stA sA (.loop ps rs body :: rest) env =
      match exec f m stA sA body env with
      | .Fallthrough r' s' =>
        exec (f + 1) m r' { s' with values := s'.values.take rs ++ sA.values.drop ps } rest env
      | .Break 0 r' s' =>
        match execOne f m r' { s' with values := s'.values.take ps ++ sA.values.drop ps }
            (.loop ps rs body) env with
        | .Fallthrough r'' s'' => exec (f + 1) m r'' s'' rest env
        | other => other
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other := by
    intro f stA sA
    simp only [exec, execOne_loop_succ]
    rcases exec f m stA sA body env with
      ⟨_, _⟩ | ⟨n, _, _⟩ | ⟨_, _⟩ | _ | _ | _ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩
    · rfl
    · cases n with
      | zero =>
        simp only
        rcases execOne f m _ _ (.loop ps rs body) env with
          ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | _ | _ | _ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩ <;> rfl
      | succ _ => rfl
    all_goals rfl
  suffices key : ∀ n, ∀ stA : Store Unit, ∀ sA : Locals,
      I stA sA → μ stA sA = n →
      wp_wasm_prop m stA sA (.loop ps rs body :: rest) env Q by
    exact key _ st locals hinit rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA sA hI hμ
    obtain ⟨N, hN⟩ := hstep stA sA hI
    rcases hN N le_rfl with ⟨stB, sB, hbody, hwp⟩ | ⟨stB, sB, hbody, hI', hμ'⟩
        | ⟨stB, vs, hbody, hQ⟩
    · -- Fallthrough: body exits, compose fuels for body and rest
      obtain ⟨fuel_rest, hfuel⟩ := hwp
      have hbody_ne : exec N m stA sA body env ≠ .OutOfFuel := by
        rw [hbody]; intro h; cases h
      have hfuel_ne : exec fuel_rest m stB
          { sB with values := sB.values.take rs ++ sA.values.drop ps } rest env ≠ .OutOfFuel := by
        intro h; simp only [h] at hfuel
      have hbody' : exec (max N fuel_rest) m stA sA body env = .Fallthrough stB sB :=
        (exec_fuel_mono (Nat.le_max_left N fuel_rest) hbody_ne).trans hbody
      have hfuel' : exec (max N fuel_rest + 1) m stB
          { sB with values := sB.values.take rs ++ sA.values.drop ps } rest env =
          exec fuel_rest m stB
          { sB with values := sB.values.take rs ++ sA.values.drop ps } rest env :=
        exec_fuel_mono (by omega) hfuel_ne
      refine ⟨max N fuel_rest + 1, ?_⟩
      have heq : exec (max N fuel_rest + 1) m stA sA (.loop ps rs body :: rest) env =
          exec fuel_rest m stB { sB with values := sB.values.take rs ++ sA.values.drop ps } rest env := by
        simp only [exec_loop_unfold (max N fuel_rest) stA sA, hbody', hfuel']
      rw [heq]; exact hfuel
    · -- Break 0: re-entry; apply IH at the smaller measure
      set trimmed : Locals :=
        { sB with values := sB.values.take ps ++ sA.values.drop ps } with htrimmed
      have hμ_lt : μ stB trimmed < n := hμ ▸ hμ'
      obtain ⟨fuel_loop, hfuel_loop⟩ := IH (μ stB trimmed) hμ_lt stB trimmed hI' rfl
      have hbody_ne : exec N m stA sA body env ≠ .OutOfFuel := by
        rw [hbody]; intro h; cases h
      have hfuel_ne : exec fuel_loop m stB trimmed (.loop ps rs body :: rest) env ≠ .OutOfFuel := by
        intro h; simp only [h] at hfuel_loop
      have hexecOne_ne : execOne fuel_loop m stB trimmed (.loop ps rs body) env ≠ .OutOfFuel := by
        intro h; exact hfuel_ne (by simp only [exec, h])
      have hbody' : exec (max N fuel_loop) m stA sA body env = .Break 0 stB sB :=
        (exec_fuel_mono (Nat.le_max_left N fuel_loop) hbody_ne).trans hbody
      have hexecOne_mono : execOne (max N fuel_loop) m stB trimmed (.loop ps rs body) env =
          execOne fuel_loop m stB trimmed (.loop ps rs body) env :=
        execOne_fuel_mono (Nat.le_max_right N fuel_loop) hexecOne_ne
      have hexecOne_ne2 : execOne (max N fuel_loop) m stB trimmed (.loop ps rs body) env ≠ .OutOfFuel := by
        rwa [hexecOne_mono]
      have hexecOne_succ : execOne (max N fuel_loop + 1) m stB trimmed (.loop ps rs body) env =
          execOne (max N fuel_loop) m stB trimmed (.loop ps rs body) env :=
        execOne_fuel_mono (Nat.le_succ _) hexecOne_ne2
      -- execOne at (stA, sA) agrees with execOne at (stB, trimmed):
      -- body takes Break 0 at stA landing exactly at trimmed
      have hexecOne_eq : execOne (max N fuel_loop + 1) m stA sA (.loop ps rs body) env =
          execOne (max N fuel_loop + 1) m stB trimmed (.loop ps rs body) env := by
        conv_lhs => rw [execOne_loop_succ]
        simp only [hbody', ← htrimmed]
        exact hexecOne_succ.symm
      -- both exec calls on (.loop :: rest) reduce via the same execOne
      have heq : exec (max N fuel_loop + 1) m stA sA (.loop ps rs body :: rest) env =
          exec (max N fuel_loop + 1) m stB trimmed (.loop ps rs body :: rest) env := by
        simp only [exec, hexecOne_eq]
      refine ⟨max N fuel_loop + 1, ?_⟩
      rw [heq,
        exec_fuel_mono (Nat.le_trans (Nat.le_max_right N fuel_loop) (Nat.le_succ _)) hfuel_ne]
      exact hfuel_loop
    · -- Return: body exits via .Return; the loop's "other => other" arm propagates it straight out
      refine ⟨N + 1, ?_⟩
      simp only [exec_loop_unfold N stA sA, hbody]
      exact hQ

-- toy: empty-body loop always exits immediately, validating wp_wasm_prop_loop
private example (m : Module) (st : Store Unit) (locals : Locals) :
    wp_wasm_prop m st locals [.loop 0 0 []] {} (fun _ _ => True) := by
  apply wp_wasm_prop_loop (I := fun _ _ => True) (μ := fun _ _ => 0)
  · trivial
  · intro stA sA _
    refine ⟨0, fun fuel _ => Or.inl ⟨stA, sA, ?_, ⟨0, ?_⟩⟩⟩
    · simp only [exec]
    · simp only [List.take_zero, List.nil_append, List.drop_zero, exec]

-- per-instruction iProp rules for wp_wasm
-- each wraps wp_wasm_step and discharges the execOne obligation

theorem wp_wasm_globalGet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value}
    (hget : st.globals.globals[i]? = some v)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.globalGet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hget]) hstep

theorem wp_wasm_globalSet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value} {vs : List Value} {old : Value}
    (hstack : locals.values = v :: vs)
    (hbound : st.globals.globals[i]? = some old)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m
          { st with globals := { globals := st.globals.globals.set i v } }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.globalSet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack, hbound]) hstep

theorem wp_wasm_localGet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value}
    (hget : locals.get i = some v)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.localGet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hget]) hstep

theorem wp_wasm_localSet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value} {vs : List Value} {locals' : Locals}
    (hstack : locals.values = v :: vs)
    (hset : locals.set? i v = some locals')
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals' with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.localSet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack, hset]) hstep

theorem wp_wasm_const
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (v : UInt32)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.const v :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def]) hstep

theorem wp_wasm_add
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (a + b) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.add :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_sub
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (b - a) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.sub :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_mul
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (a * b) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.mul :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_eqz
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (if a = 0 then 1 else 0) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.eqz :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_ltU
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 b :: .i32 a :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (if a < b then 1 else 0) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.ltU :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_leU
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 b :: .i32 a :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (if a ≤ b then 1 else 0) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.leU :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_gtU
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 b :: .i32 a :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (if a > b then 1 else 0) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.gtU :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_geU
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 b :: .i32 a :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (if a ≥ b then 1 else 0) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.geU :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_and
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (a &&& b) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.and :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_shl
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 b :: .i32 a :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (a <<< (b % 32)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.shl :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_load64
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st
          { locals with values := .i64 (st.mem.read64 (addr + off)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.load64 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_store64
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {v : UInt64} {vs : List Value}
    (hstack : locals.values = .i64 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m
          { st with mem := st.mem.write64 (addr + off) v }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.store64 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_load32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st
          { locals with values := .i32 (st.mem.read32 (addr + off)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.load32 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_store32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {v : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m
          { st with mem := st.mem.write32 (addr + off) v }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.store32 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_prop_to_TerminatesWith
    {m : Module} {id : Nat} {f : Function}
    {initial : Store Unit} {args : List Value}
    {P : Store Unit → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (himp : m.imports[id]? = none)
    (hresults : f.results.length = 0)
    (hlen : args.length ≤ f.numParams)
    (hcompat : ∀ st' vals, P st' vals → P st' [])
    (hwp : wp_wasm_prop m initial
        (f.toLocals (args.take f.numParams).reverse)
        f.body {} P) :
    TerminatesWith {} m id initial args P := by
  obtain ⟨fuel₀, hwp_fuel⟩ := hwp
  have hcr : args.drop f.numParams = [] := List.drop_eq_nil_of_le hlen
  cases hexec : exec fuel₀ m initial (f.toLocals (args.take f.numParams).reverse) f.body {} with
  | Fallthrough st' s' =>
    rw [hexec] at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr])
      hwp_fuel
  | Return st' vals =>
    rw [hexec] at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr])
      (hcompat st' vals hwp_fuel)
  | Break n st' s' => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | Trap msg => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | Invalid msg => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | OutOfFuel => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | ReturnCall fid st' vs => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | Throwing tag targs st' s' => rw [hexec] at hwp_fuel; exact hwp_fuel.elim

-- bridge: iris WP + ghost heap → wp_wasm_prop
theorem wasm_heap_adequacy_with_mem
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ₀ : WasmHeapMap (Option UInt8))
    (hwp : ⊢ genHeapInterp σ₀ ∗ wp_wasm m st locals prog env Q) :
    wp_wasm_prop m st locals prog env Q :=
  pure_soundness (hwp.trans (wasm_adequacy m st locals prog env Q σ₀))

-- update all 4 ghost bytes of a u32 cell
private theorem pointsTo_u32_update
    (σ : WasmHeapMap (Option UInt8)) (addr old_v new_v : UInt32) :
    genHeapInterp σ ∗ pointsTo_u32 addr old_v ==∗
    ∃ σ' : WasmHeapMap (Option UInt8), genHeapInterp σ' ∗ pointsTo_u32 addr new_v := by
  simp only [pointsTo_u32]
  iintro ⟨Hσ, ⟨Hb0, ⟨Hb1, ⟨Hb2, Hb3⟩⟩⟩⟩
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 0) % 256, by omega⟩)
    $$ [$Hσ $Hb0] with ⟨Hσ, Hb0⟩
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 1) % 256, by omega⟩)
    $$ [$Hσ $Hb1] with ⟨Hσ, Hb1⟩
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 2) % 256, by omega⟩)
    $$ [$Hσ $Hb2] with ⟨Hσ, Hb2⟩
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 3) % 256, by omega⟩)
    $$ [$Hσ $Hb3] with ⟨Hσ, Hb3⟩
  imodintro
  iexists _
  isplitl [Hσ]
  · iexact Hσ
  · isplitl [Hb0]
    · iexact Hb0
    · isplitl [Hb1]
      · iexact Hb1
      · isplitl [Hb2]
        · iexact Hb2
        · iexact Hb3

-- step rule: pure instruction, no ghost heap change
theorem wp_iProp_step
    {m : Module} {st st' : Store Unit} {locals locals' : Locals}
    {instr : Instruction} {rest : Program}
    {env : HostEnv Unit} {Q : Store Unit → List Value → Prop}
    {P : IProp WasmHeapGF}
    (hexec : execOne 1 m st locals instr env = .Fallthrough st' locals')
    (hcont : P ⊢ wp_wasm m st' locals' rest env Q) :
    P ⊢ wp_wasm m st locals (instr :: rest) env Q := by
  unfold wp_wasm at *
  iintro HP
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  split
  · contradiction
  · next tail h =>
    obtain ⟨rfl, _⟩ := List.cons.inj h
    simp [execOne] at hexec
  · next instr' rest' h =>
    obtain ⟨h1, h2⟩ := List.cons.inj h
    subst h1; subst h2
    iintro %σ Hσ
    imodintro
    iexists σ, st', locals'
    isplitl []
    · exact BI.pure_intro hexec
    · isplitl [Hσ]
      · iexact Hσ
      · exact hcont

-- load32 with frame: reads a value from memory, frame unchanged
theorem wp_iProp_load32_sep
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr off : UInt32} {vs : List Value}
    {F : IProp WasmHeapGF}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hcont : F ⊢
             wp_wasm m st { locals with values := .i32 (st.mem.read32 (addr + off)) :: vs }
             rest env Q) :
    F ⊢ wp_wasm m st locals (.load32 off :: rest) env Q :=
  wp_iProp_step (hexec := by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)]) hcont

-- store32 rule: transfers ghost ownership from old to new value
theorem wp_iProp_store32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr off v old_v : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hcont : pointsTo_u32 (addr + off) v ⊢
             wp_wasm m { st with mem := st.mem.write32 (addr + off) v }
             { locals with values := vs } rest env Q) :
    pointsTo_u32 (addr + off) old_v ⊢
    wp_wasm m st locals (.store32 off :: rest) env Q := by
  unfold wp_wasm at *
  iintro Hpt
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  iintro %σ Hσ
  imod (pointsTo_u32_update σ (addr + off) old_v v) $$ [$Hσ $Hpt] with ⟨%σ', Hσ', Hpt'⟩
  imodintro
  iexists σ', { st with mem := st.mem.write32 (addr + off) v }, { locals with values := vs }
  isplitl []
  · exact BI.pure_intro (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
  · isplitl [Hσ']
    · iexact Hσ'
    · exact hcont

-- store32 with frame: like wp_iProp_store32 but preserves a frame resource F alongside the cell
theorem wp_iProp_store32_sep
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr off v old_v : UInt32} {vs : List Value}
    {F : IProp WasmHeapGF}
    (hstack : locals.values = .i32 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hcont : pointsTo_u32 (addr + off) v ∗ F ⊢
             wp_wasm m { st with mem := st.mem.write32 (addr + off) v }
             { locals with values := vs } rest env Q) :
    pointsTo_u32 (addr + off) old_v ∗ F ⊢
    wp_wasm m st locals (.store32 off :: rest) env Q := by
  unfold wp_wasm at *
  iintro ⟨Hpt, HF⟩
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  iintro %σ Hσ
  imod (pointsTo_u32_update σ (addr + off) old_v v) $$ [$Hσ $Hpt] with ⟨%σ', Hσ', Hpt'⟩
  imodintro
  iexists σ', { st with mem := st.mem.write32 (addr + off) v }, { locals with values := vs }
  isplitl []
  · exact BI.pure_intro (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
  · isplitl [Hσ']
    · iexact Hσ'
    · exact (BI.sep_comm.mp.trans hcont)

-- ret rule: closes wp for .ret, any remaining ghost resource is discarded (affine)
theorem wp_iProp_ret
    {P : IProp WasmHeapGF}
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (hQ : Q st locals.values) :
    P ⊢ wp_wasm m st locals (.ret :: rest) env Q := by
  unfold wp_wasm
  iintro _
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  exact BI.pure_intro hQ

-- iProp loop rule: thread ghost ownership through loop iterations.
-- Conclusion: Prop-level wp_wasm_prop for the loop.
--
-- Why Prop-level conclusion: wp_wasm (iris fixpoint) uses execOne 1, which gives
-- exec 0 for the loop body — always OutOfFuel for non-empty bodies. The fixpoint
-- therefore cannot express loop termination. wp_wasm_prop (∃ fuel, exec fuel ...)
-- CAN express it, and is what the adequacy chain ultimately needs.
--
-- Mirrors wp_wasm_prop_loop exactly; replaces the Prop invariant I : Store → Locals → Prop
-- with an iProp invariant I : Nat → Store → Locals → IProp witnessed by a ghost state:
--   "∃ σ, ⊢ genHeapInterp σ ∗ I n stA locA"
-- The n-indexed measure plays the role of μ from wp_wasm_prop_loop.
--
-- Usage: to prove hstep, do iris reasoning about the body using
-- wp_iProp_store32_sep / wp_iProp_load32_sep / wp_iProp_step, then apply
-- wasm_heap_adequacy_with_mem to convert to exec-level facts; exhibit the
-- updated ghost heap σ' as the witness for the next invariant.
theorem wp_wasm_iProp_loop
    {m : Module} {st : Store Unit} {locals : Locals}
    {ps rs : Nat} {body : Program} {rest : Program}
    {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (measure : Nat)
    (I : Nat → Store Unit → Locals → IProp WasmHeapGF)
    (σ₀ : WasmHeapMap (Option UInt8))
    (hinit : ⊢ genHeapInterp σ₀ ∗ I measure st locals)
    (hstep : ∀ n stA locA,
        (∃ σ : WasmHeapMap (Option UInt8), ⊢ genHeapInterp σ ∗ I n stA locA) →
        ∃ N, ∀ fuel ≥ N,
          (∃ stB sB,
            exec fuel m stA locA body env = .Fallthrough stB sB ∧
            wp_wasm_prop m stB
              { sB with values := sB.values.take rs ++ locA.values.drop ps }
              rest env Q) ∨
          (∃ stB sB,
            exec fuel m stA locA body env = .Break 0 stB sB ∧
            ∃ n' : Nat, n' < n ∧
            ∃ σ' : WasmHeapMap (Option UInt8),
              ⊢ genHeapInterp σ' ∗
                I n' stB { sB with values := sB.values.take ps ++ locA.values.drop ps }) ∨
          (∃ stB vs,
            exec fuel m stA locA body env = .Return stB vs ∧ Q stB vs)) :
    wp_wasm_prop m st locals (.loop ps rs body :: rest) env Q := by
  -- same exec_loop_unfold helper as in wp_wasm_prop_loop
  have exec_loop_unfold : ∀ (f : Nat) (stA : Store Unit) (sA : Locals),
      exec (f + 1) m stA sA (.loop ps rs body :: rest) env =
      match exec f m stA sA body env with
      | .Fallthrough r' s' =>
        exec (f + 1) m r' { s' with values := s'.values.take rs ++ sA.values.drop ps } rest env
      | .Break 0 r' s' =>
        match execOne f m r' { s' with values := s'.values.take ps ++ sA.values.drop ps }
            (.loop ps rs body) env with
        | .Fallthrough r'' s'' => exec (f + 1) m r'' s'' rest env
        | other => other
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other := by
    intro f stA sA
    simp only [exec, execOne_loop_succ]
    rcases exec f m stA sA body env with
      ⟨_, _⟩ | ⟨n, _, _⟩ | ⟨_, _⟩ | _ | _ | _ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩
    · rfl
    · cases n with
      | zero =>
        simp only
        rcases execOne f m _ _ (.loop ps rs body) env with
          ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | _ | _ | _ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩ <;> rfl
      | succ _ => rfl
    all_goals rfl
  -- reduce to strong induction: key n says "any ghost-witnessed I n implies loop wp"
  suffices key : ∀ n stA locA,
      (∃ σ : WasmHeapMap (Option UInt8), ⊢ genHeapInterp σ ∗ I n stA locA) →
      wp_wasm_prop m stA locA (.loop ps rs body :: rest) env Q from
    key measure st locals ⟨σ₀, hinit⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA locA ⟨σ, hI⟩
    obtain ⟨N, hN⟩ := hstep n stA locA ⟨σ, hI⟩
    rcases hN N le_rfl with ⟨stB, sB, hbody, hwp⟩ | ⟨stB, sB, hbody, n', hn', σ', hI'⟩
        | ⟨stB, vs, hbody, hQ⟩
    · -- Fallthrough: body exits, compose fuels for body and rest
      obtain ⟨fuel_rest, hfuel⟩ := hwp
      have hbody_ne : exec N m stA locA body env ≠ .OutOfFuel := by
        rw [hbody]; intro h; cases h
      have hfuel_ne : exec fuel_rest m stB
          { sB with values := sB.values.take rs ++ locA.values.drop ps } rest env ≠ .OutOfFuel := by
        intro h; simp only [h] at hfuel
      have hbody' : exec (max N fuel_rest) m stA locA body env = .Fallthrough stB sB :=
        (exec_fuel_mono (Nat.le_max_left N fuel_rest) hbody_ne).trans hbody
      have hfuel' : exec (max N fuel_rest + 1) m stB
          { sB with values := sB.values.take rs ++ locA.values.drop ps } rest env =
          exec fuel_rest m stB
          { sB with values := sB.values.take rs ++ locA.values.drop ps } rest env :=
        exec_fuel_mono (by omega) hfuel_ne
      refine ⟨max N fuel_rest + 1, ?_⟩
      have heq : exec (max N fuel_rest + 1) m stA locA (.loop ps rs body :: rest) env =
          exec fuel_rest m stB
          { sB with values := sB.values.take rs ++ locA.values.drop ps } rest env := by
        simp only [exec_loop_unfold (max N fuel_rest) stA locA, hbody', hfuel']
      rw [heq]; exact hfuel
    · -- Break 0: re-entry; apply IH with smaller measure and new ghost state
      set trimmed : Locals :=
        { sB with values := sB.values.take ps ++ locA.values.drop ps } with htrimmed
      obtain ⟨fuel_loop, hfuel_loop⟩ := IH n' hn' stB trimmed ⟨σ', hI'⟩
      have hbody_ne : exec N m stA locA body env ≠ .OutOfFuel := by
        rw [hbody]; intro h; cases h
      have hfuel_ne : exec fuel_loop m stB trimmed (.loop ps rs body :: rest) env ≠ .OutOfFuel := by
        intro h; simp only [h] at hfuel_loop
      have hexecOne_ne : execOne fuel_loop m stB trimmed (.loop ps rs body) env ≠ .OutOfFuel := by
        intro h; exact hfuel_ne (by simp only [exec, h])
      have hbody' : exec (max N fuel_loop) m stA locA body env = .Break 0 stB sB :=
        (exec_fuel_mono (Nat.le_max_left N fuel_loop) hbody_ne).trans hbody
      have hexecOne_mono : execOne (max N fuel_loop) m stB trimmed (.loop ps rs body) env =
          execOne fuel_loop m stB trimmed (.loop ps rs body) env :=
        execOne_fuel_mono (Nat.le_max_right N fuel_loop) hexecOne_ne
      have hexecOne_ne2 : execOne (max N fuel_loop) m stB trimmed (.loop ps rs body) env ≠ .OutOfFuel := by
        rwa [hexecOne_mono]
      have hexecOne_succ : execOne (max N fuel_loop + 1) m stB trimmed (.loop ps rs body) env =
          execOne (max N fuel_loop) m stB trimmed (.loop ps rs body) env :=
        execOne_fuel_mono (Nat.le_succ _) hexecOne_ne2
      have hexecOne_eq : execOne (max N fuel_loop + 1) m stA locA (.loop ps rs body) env =
          execOne (max N fuel_loop + 1) m stB trimmed (.loop ps rs body) env := by
        conv_lhs => rw [execOne_loop_succ]
        simp only [hbody', ← htrimmed]
        exact hexecOne_succ.symm
      have heq : exec (max N fuel_loop + 1) m stA locA (.loop ps rs body :: rest) env =
          exec (max N fuel_loop + 1) m stB trimmed (.loop ps rs body :: rest) env := by
        simp only [exec, hexecOne_eq]
      refine ⟨max N fuel_loop + 1, ?_⟩
      rw [heq,
        exec_fuel_mono (Nat.le_trans (Nat.le_max_right N fuel_loop) (Nat.le_succ _)) hfuel_ne]
      exact hfuel_loop
    · -- Return: body exits via .Return; loop's "other => other" arm propagates it out
      refine ⟨N + 1, ?_⟩
      simp only [exec_loop_unfold N stA locA, hbody]
      exact hQ

-- iProp block rule: for a block containing a single loop,
-- where the loop body's Break 1 exits the block (Fallthrough at block level),
-- Break 0 restarts the loop (measure decreases), and Return propagates.
-- Same proof structure as wp_wasm_iProp_loop; mirrors "Handle Break 1 as Break 0 at block level".
theorem wp_wasm_iProp_block
    {m : Module} {st : Store Unit} {locals : Locals}
    {bt bl : Nat} {loopBody : Program} {rest : Program}
    {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (measure : Nat)
    (I : Nat → Store Unit → Locals → IProp WasmHeapGF)
    (σ₀ : WasmHeapMap (Option UInt8))
    (hinit : ⊢ genHeapInterp σ₀ ∗ I measure st locals)
    -- For bt = 0 this is trivially true; for general bt it requires bt ≤ sB.values.length.
    -- In the merge sort application bt = bl = 0, so the caller proves this by simp.
    (h_drop_eq : ∀ (vs ws : List Value),
        (vs.take bt ++ ws.drop bt).drop bt = ws.drop bt)
    (hstep : ∀ n stA locA,
        (∃ σ : WasmHeapMap (Option UInt8), ⊢ genHeapInterp σ ∗ I n stA locA) →
        ∃ N, ∀ fuel ≥ N,
          -- Loop body Break 1 → loop gives Break 0 → block Fallthroughs → rest
          (∃ stB sB, exec fuel m stA locA loopBody env = .Break 1 stB sB ∧
            wp_wasm_prop m stB
              { sB with values := sB.values.take bl ++ locA.values.drop bt }
              rest env Q) ∨
          -- Loop body Break 0 → loop restarts (measure decreases, ghost state updated)
          (∃ stB sB, exec fuel m stA locA loopBody env = .Break 0 stB sB ∧
            ∃ n' : Nat, n' < n ∧
            ∃ σ' : WasmHeapMap (Option UInt8),
              ⊢ genHeapInterp σ' ∗
                I n' stB { sB with values := sB.values.take bt ++ locA.values.drop bt }) ∨
          -- Loop body Return → propagates through loop and block
          (∃ stB vs, exec fuel m stA locA loopBody env = .Return stB vs ∧ Q stB vs)) :
    wp_wasm_prop m st locals (.block bt bl [.loop bt bl loopBody] :: rest) env Q := by
  suffices key : ∀ n stA locA,
      (∃ σ : WasmHeapMap (Option UInt8), ⊢ genHeapInterp σ ∗ I n stA locA) →
      wp_wasm_prop m stA locA (.block bt bl [.loop bt bl loopBody] :: rest) env Q from
    key measure st locals ⟨σ₀, hinit⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA locA ⟨σ, hI⟩
    obtain ⟨N, hN⟩ := hstep n stA locA ⟨σ, hI⟩
    rcases hN N le_rfl with ⟨stB, sB, hbody, hwp⟩ | ⟨stB, sB, hbody, n', hn', σ', hI'⟩
        | ⟨stB, vs, hbody, hQ⟩
    · -- Break 1: loop body gives Break 1 → loop exits as Break 0 → block Fallthroughs
      obtain ⟨fuel_rest, hfuel⟩ := hwp
      have hbody_ne : exec N m stA locA loopBody env ≠ .OutOfFuel := by
        rw [hbody]; intro h; cases h
      have hfuel_ne : exec fuel_rest m stB
          { sB with values := sB.values.take bl ++ locA.values.drop bt } rest env ≠ .OutOfFuel := by
        intro h; simp only [h] at hfuel
      -- execOne (N+1) (.loop ..) = .Break 0 stB sB  (Break 1 propagates as Break 0)
      have h_execOne : execOne (N + 1) m stA locA (.loop bt bl loopBody) env = .Break 0 stB sB := by
        simp only [execOne_loop_succ, hbody]
      -- exec (N+1) [.loop ..] = .Break 0 stB sB  (use list notation to match exec_block_cons)
      have h_loop : exec (N + 1) m stA locA [.loop bt bl loopBody] env = .Break 0 stB sB := by
        simp only [exec, h_execOne]
      have h_loop_ne : exec (N + 1) m stA locA [.loop bt bl loopBody] env ≠ .OutOfFuel := by
        rw [h_loop]; intro h; cases h
      -- Monotone: exec (max (N+1) fuel_rest) [.loop ..] = .Break 0
      have h_loop' : exec (max (N + 1) fuel_rest) m stA locA [.loop bt bl loopBody] env = .Break 0 stB sB :=
        (exec_fuel_mono (Nat.le_max_left (N + 1) fuel_rest) h_loop_ne).trans h_loop
      -- Rest fuel monotone
      have hfuel' : exec (max (N + 1) fuel_rest + 1) m stB
          { sB with values := sB.values.take bl ++ locA.values.drop bt } rest env =
          exec fuel_rest m stB
          { sB with values := sB.values.take bl ++ locA.values.drop bt } rest env :=
        exec_fuel_mono (by omega) hfuel_ne
      -- Assemble via exec_block_cons: .Break 0 from loop → Fallthrough from block → rest
      refine ⟨max (N + 1) fuel_rest + 1, ?_⟩
      simp only [exec_block_cons, h_loop', hfuel']
      exact hfuel
    · -- Break 0: loop body restarts; apply IH with smaller measure
      set trimmed : Locals :=
        { sB with values := sB.values.take bt ++ locA.values.drop bt } with htrimmed
      obtain ⟨fuel_IH, hfuel_IH⟩ := IH n' hn' stB trimmed ⟨σ', hI'⟩
      have hfuel_IH_ne : exec fuel_IH m stB trimmed
          (.block bt bl [.loop bt bl loopBody] :: rest) env ≠ .OutOfFuel := by
        intro h; simp only [h] at hfuel_IH
      have hbody_ne : exec N m stA locA loopBody env ≠ .OutOfFuel := by
        rw [hbody]; intro h; cases h
      -- trimmed.values.drop bt = locA.values.drop bt (by h_drop_eq, since trimmed.values = sB.values.take bt ++ locA.values.drop bt)
      have h_drop : trimmed.values.drop bt = locA.values.drop bt :=
        h_drop_eq sB.values locA.values
      -- fuel_IH ≥ 1: exec 0 (.block :: rest) = OutOfFuel by definition
      have hfuel_IH_pos : 0 < fuel_IH := by
        apply Nat.pos_of_ne_zero
        rintro rfl
        exact hfuel_IH_ne (by simp only [exec.eq_def, execOne.eq_def])
      -- exec (fuel_IH - 1) [.loop ..] at stB trimmed ≠ OutOfFuel
      have h_loop_ne : exec (fuel_IH - 1) m stB trimmed [.loop bt bl loopBody] env ≠ .OutOfFuel := by
        intro h
        apply hfuel_IH_ne
        rw [show fuel_IH = fuel_IH - 1 + 1 from (Nat.succ_pred_eq_of_pos hfuel_IH_pos).symm]
        simp only [exec_block_cons, h]
      -- execOne (fuel_IH - 1) (.loop ..) at stB trimmed ≠ OutOfFuel
      have h_execOne_ne : execOne (fuel_IH - 1) m stB trimmed (.loop bt bl loopBody) env ≠ .OutOfFuel := by
        intro h; apply h_loop_ne; simp only [exec, h]
      -- Monotone execOne up to max N fuel_IH
      have h_execOne_mono : execOne (max N fuel_IH) m stB trimmed (.loop bt bl loopBody) env =
          execOne (fuel_IH - 1) m stB trimmed (.loop bt bl loopBody) env :=
        execOne_fuel_mono (by omega) h_execOne_ne
      have h_execOne_ne2 : execOne (max N fuel_IH) m stB trimmed (.loop bt bl loopBody) env ≠ .OutOfFuel := by
        rw [h_execOne_mono]; exact h_execOne_ne
      -- exec (max N fuel_IH) loopBody at stA = .Break 0
      have hbody' : exec (max N fuel_IH) m stA locA loopBody env = .Break 0 stB sB :=
        (exec_fuel_mono (Nat.le_max_left N fuel_IH) hbody_ne).trans hbody
      -- execOne (max N fuel_IH + 1) (.loop ..) at stB trimmed = execOne at max N fuel_IH
      have h_execOne_succ : execOne (max N fuel_IH + 1) m stB trimmed (.loop bt bl loopBody) env =
          execOne (max N fuel_IH) m stB trimmed (.loop bt bl loopBody) env :=
        execOne_fuel_mono (Nat.le_succ _) h_execOne_ne2
      -- execOne (max N fuel_IH + 1) (.loop ..) at stA = at stB trimmed  (restart equality)
      have h_execOne_eq : execOne (max N fuel_IH + 1) m stA locA (.loop bt bl loopBody) env =
          execOne (max N fuel_IH + 1) m stB trimmed (.loop bt bl loopBody) env := by
        conv_lhs => rw [execOne_loop_succ]
        simp only [hbody', ← htrimmed]
        exact h_execOne_succ.symm
      -- exec (max N fuel_IH + 1) [.loop ..] at stA = at stB trimmed
      have h_loop_eq : exec (max N fuel_IH + 1) m stA locA [.loop bt bl loopBody] env =
          exec (max N fuel_IH + 1) m stB trimmed [.loop bt bl loopBody] env := by
        simp only [exec, h_execOne_eq]
      -- exec (max N fuel_IH + 2) (.block :: rest) at stA = at stB trimmed  (via loop equality + drop eq)
      have h_block_eq : exec (max N fuel_IH + 2) m stA locA
          (.block bt bl [.loop bt bl loopBody] :: rest) env =
          exec (max N fuel_IH + 2) m stB trimmed
          (.block bt bl [.loop bt bl loopBody] :: rest) env := by
        simp only [exec_block_cons, h_loop_eq, h_drop]
      -- exec (max N fuel_IH + 2) (.block :: rest) at stB trimmed = exec fuel_IH  (mono)
      have h_block_mono : exec (max N fuel_IH + 2) m stB trimmed
          (.block bt bl [.loop bt bl loopBody] :: rest) env =
          exec fuel_IH m stB trimmed
          (.block bt bl [.loop bt bl loopBody] :: rest) env :=
        exec_fuel_mono (by omega) hfuel_IH_ne
      refine ⟨max N fuel_IH + 2, ?_⟩
      rw [h_block_eq, h_block_mono]; exact hfuel_IH
    · -- Return: loop body returns → execOne returns → block propagates
      have h_execOne_ret : execOne (N + 1) m stA locA (.loop bt bl loopBody) env = .Return stB vs := by
        simp only [execOne_loop_succ, hbody]
      have h_loop_ret : exec (N + 1) m stA locA [.loop bt bl loopBody] env = .Return stB vs := by
        simp only [exec, h_execOne_ret]
      refine ⟨N + 2, ?_⟩
      simp only [exec_block_cons, h_loop_ret]
      exact hQ

end Wasm.SepLogic
