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

/-- WP functional for the iProp-level `wp_wasm` fixpoint.

**Scope:** the step case demands `execOne 1 … = .Fallthrough …` — one
instruction at fuel 1, completing by fallthrough. This covers straight-line
instructions (const, add, local/global get/set, load/store, …) but NOT
`.call`/`.block`/`.loop` with non-empty bodies (`execOne 1` runs their body
at fuel 0 → `.OutOfFuel`) nor instructions producing `.Break`/`.Return`
(only `.ret` has a dedicated terminal case). Control flow is currently
handled at the Prop level by `wp_wasm_prop_call`/`_block`/`_loop`, composed
with this fixpoint through the adequacy bridge. Generalizing the step case
over the full `ExecResult` (with a fuel-monotone continuation) is the
intended future shape.

**Ghost state:** the ghost heap σ threaded through the step case is not
(yet) tied to the physical `st.mem` — see the status note in
`WasmRules.lean`. Memory facts enter the load/store rules below as pure
hypotheses about `st.mem`. -/
def wp_wasm_F (Φ : DiscreteO WasmState → IProp WasmHeapGF)
    (s : DiscreteO WasmState) : IProp WasmHeapGF :=
  let ws := s.car
  match ws.prog with
  | [] =>
      iprop% ⌜ws.Q ws.st []⌝
  | .ret :: _ =>
      iprop% ⌜ws.Q ws.st ws.locals.values⌝
  | instr :: rest =>
      iprop% ∀ σ : WasmHeapMap (Option UInt8),
        ⌜heapAgreesWithMem σ ws.st.mem⌝ -∗
        genHeapInterp σ ==∗
          ∃ σ' : WasmHeapMap (Option UInt8),
          ∃ st' : Store Unit,
          ∃ locals' : Locals,
            ⌜execOne 1 ws.m ws.st ws.locals instr ws.env = .Fallthrough st' locals'⌝ ∗
            ⌜heapAgreesWithMem σ' st'.mem⌝ ∗
            genHeapInterp σ' ∗
            Φ ⟨{ m := ws.m, st := st', locals := locals',
                 prog := rest, env := ws.env, Q := ws.Q }⟩

def wp_wasm (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : IProp WasmHeapGF :=
  bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩

instance instBIMonoPredWasmF :
    BIMonoPred (PROP := IProp WasmHeapGF) (A := DiscreteO WasmState) wp_wasm_F where
  mono_pred := by
    intro Φ Ψ hΦ hΨ
    iintro #HΦΨ %s
    obtain ⟨ws⟩ := s
    unfold wp_wasm_F
    simp only []
    split
    · iintro H; iexact H
    · iintro H; iexact H
    · next instr rest =>
      iintro Hwp
      iintro %σ₀
      iintro hagree
      iintro Hσ₀
      imod Hwp $$ % σ₀ hagree Hσ₀ with ⟨%σ', %st₁, %locals₁, hexec, hagree', Hσ', HΦ⟩
      imodintro
      iexists σ', st₁, locals₁
      isplitl [hexec]
      · iexact hexec
      · isplitl [hagree']
        · iexact hagree'
        · isplitl [Hσ']
          · iexact Hσ'
          · iapply HΦΨ
            iexact HΦ
  mono_pred_ne.ne _ _ _ H :=
    (DiscreteO.ext (DiscreteO.dist_inj H)) ▸ OFE.Dist.rfl

omit inst in
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
    (hmem : st'.mem = st.mem)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗ wp_wasm m st' locals' rest₀ env Q) :
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
    iintro %σ %hagree Hσ
    imod (hstep σ) $$ Hσ with ⟨Hσ', Hwp⟩
    imodintro
    iexists σ, st', locals'
    isplitl []
    · exact BI.pure_intro hexec
    · isplitl []
      · exact BI.pure_intro (hmem ▸ hagree)
      · isplitl [Hσ']
        · iexact Hσ'
        · iexact Hwp

-- linter false positive: `DiscreteO.car` below is a structural projection
-- reduction the subsequent `split` depends on, but unusedSimpArgs flags it
set_option linter.unusedSimpArgs false in
theorem wasm_adequacy
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ : WasmHeapMap (Option UInt8))
    (hagree : heapAgreesWithMem σ st.mem) :
    genHeapInterp σ ∗ wp_wasm m st locals prog env Q ⊢
      ⌜wp_wasm_prop m st locals prog env Q⌝ := by
  unfold wp_wasm
  let Ψ : DiscreteO WasmState → IProp WasmHeapGF :=
    fun s => iprop% ∀ σ' : WasmHeapMap (Option UInt8),
      ⌜heapAgreesWithMem σ' s.car.st.mem⌝ -∗ genHeapInterp σ' -∗
      ⌜wp_wasm_prop s.car.m s.car.st s.car.locals s.car.prog s.car.env s.car.Q⌝
  haveI hΨ : OFE.NonExpansive Ψ :=
    ⟨fun _ _ _ H => (DiscreteO.ext (DiscreteO.dist_inj H)) ▸ OFE.Dist.rfl⟩
  have hstep : ⊢ □ (∀ y : DiscreteO WasmState, wp_wasm_F Ψ y -∗ Ψ y) := by
    iintro !> %s
    obtain ⟨⟨m', st', locals', prog', env', Q'⟩⟩ := s
    unfold wp_wasm_F Ψ
    simp only [DiscreteO.car]
    split
    · refine BI.entails_wand (BI.pure_elim' fun h =>
        BI.forall_intro fun _ => BI.wand_intro (BI.wand_intro (BI.pure_intro ⟨0, ?_⟩)))
      simp only [exec]; exact h
    · refine BI.entails_wand (BI.pure_elim' fun h =>
        BI.forall_intro fun _ => BI.wand_intro (BI.wand_intro (BI.pure_intro ⟨1, ?_⟩)))
      simp only [exec, execOne]; exact h
    · next instr rest =>
      iintro Hwp
      iintro %σ_any
      iintro hagree_any
      iintro Hσ_any
      imod Hwp $$ % σ_any hagree_any Hσ_any with ⟨%σ₁, %st₁, %locals₁, hexec, hagree₁, Hσ₁, Hcont⟩
      icases hexec with %hexec_lean
      icases Hcont $$ % σ₁ hagree₁ Hσ₁ with %hwp_lean
      exact BI.pure_intro (exec_cons hexec_lean hwp_lean)
  have hfp : bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩ ⊢
      Ψ ⟨{ m, st, locals, prog, env, Q }⟩ :=
    BI.sep_elim_emp_valid_left hstep
      (BI.wand_elim ((BI.wand_entails (least_fixpoint_iter (F := wp_wasm_F))).trans
        (BI.forall_elim (⟨{ m, st, locals, prog, env, Q }⟩ : DiscreteO WasmState))))
  exact ((BI.sep_mono_right hfp).trans
    (BI.sep_mono_right (BI.forall_elim σ))).trans
    ((BI.sep_mono_right (BI.sep_elim_emp_valid_left (BI.pure_intro hagree) BI.wand_elim_right)).trans
    BI.wand_elim_right)

-- call rule: if the callee terminates with a postcondition that implies the
-- continuation terminates, the whole call sequence terminates.
omit inst in
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
-- A single body fuel suffices: the rule lifts it via `exec_fuel_mono`
-- internally. Scope: bodies that exit via an outward break (`Break (k+1)`)
-- or `Return` are not covered — trace those at the exec level and hop over
-- them with `wp_wasm_prop_of_exec_eq` (as swap's `func1` does).
omit inst in
theorem wp_wasm_prop_block
    {m : Module} {st : Store Unit} {locals : Locals}
    {bt bl : Nat} {body : Program} {rest : Program}
    {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (hbody : ∃ N,
      (∃ st' s', exec N m st locals body env = .Fallthrough st' s' ∧
        wp_wasm_prop m st' { s' with values := s'.values.take bl ++ locals.values.drop bt }
          rest env Q) ∨
      (∃ st' s', exec N m st locals body env = .Break 0 st' s' ∧
        wp_wasm_prop m st' { s' with values := s'.values.take bl ++ locals.values.drop bt }
          rest env Q)) :
    wp_wasm_prop m st locals (.block bt bl body :: rest) env Q := by
  obtain ⟨N, hN⟩ := hbody
  rcases hN with ⟨st', s', hbody_result, hwp⟩ | ⟨st', s', hbody_result, hwp⟩ <;> {
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
-- As with the block rule, a single body fuel per iteration suffices.
omit inst in
theorem wp_wasm_prop_loop
    {m : Module} {st : Store Unit} {locals : Locals}
    {ps rs : Nat} {body : Program} {rest : Program}
    {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (I : Store Unit → Locals → Prop)
    (μ : Store Unit → Locals → Nat)
    (hinit : I st locals)
    (hstep : ∀ stA locA, I stA locA →
      ∃ N,
        (∃ stB sB, exec N m stA locA body env = .Fallthrough stB sB ∧
          wp_wasm_prop m stB { sB with values := sB.values.take rs ++ locA.values.drop ps }
            rest env Q) ∨
        (∃ stB sB, exec N m stA locA body env = .Break 0 stB sB ∧
          I stB { sB with values := sB.values.take ps ++ locA.values.drop ps } ∧
          μ stB { sB with values := sB.values.take ps ++ locA.values.drop ps } < μ stA locA)) :
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
    rcases hN with ⟨stB, sB, hbody, hwp⟩ | ⟨stB, sB, hbody, hI', hμ'⟩
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

-- toy: empty-body loop always exits immediately, validating wp_wasm_prop_loop
private example (m : Module) (st : Store Unit) (locals : Locals) :
    wp_wasm_prop m st locals [.loop 0 0 []] {} (fun _ _ => True) := by
  apply wp_wasm_prop_loop (I := fun _ _ => True) (μ := fun _ _ => 0)
  · trivial
  · intro stA sA _
    refine ⟨0, Or.inl ⟨stA, sA, ?_, ⟨0, ?_⟩⟩⟩
    · simp only [exec]
    · simp only [List.take_zero, List.nil_append, List.drop_zero, exec]

-- toy: empty block body falls through, validating the block rule's
-- Fallthrough disjunct
private example (m : Module) (st : Store Unit) (locals : Locals) :
    wp_wasm_prop m st locals [.block 0 0 []] {} (fun _ _ => True) := by
  apply wp_wasm_prop_block
  refine ⟨0, Or.inl ⟨st, locals, ?_, ⟨0, ?_⟩⟩⟩
  · simp only [exec]
  · simp only [exec]

-- toy: `br 0` body breaks to the block label, validating the Break-0 disjunct
private example (m : Module) (st : Store Unit) (locals : Locals) :
    wp_wasm_prop m st locals [.block 0 0 [.br 0]] {} (fun _ _ => True) := by
  apply wp_wasm_prop_block
  refine ⟨1, Or.inr ⟨st, locals, ?_, ⟨0, ?_⟩⟩⟩
  · simp [exec, execOne]
  · simp only [exec]

omit inst in
/-- `TerminatesWith` is monotone in its postcondition. Stated here (rather
than in the interpreter's `Spec/Defs.lean`) so the SepLogic layer stays
self-contained; the main consumer is `wp_wasm_prop_call`, whose callee spec
must be weakened to "the continuation's WP holds". -/
theorem _root_.Wasm.TerminatesWith.mono {α : Type} {env : HostEnv α} {m : Module}
    {id : Nat} {initial : Store α} {args : List Value}
    {P P' : Store α → List Value → Prop}
    (h : TerminatesWith env m id initial args P)
    (himp : ∀ st vs, P st vs → P' st vs) :
    TerminatesWith env m id initial args P' := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun fuel hf =>
    let ⟨vs, st, hrun, hp⟩ := hN fuel hf
    ⟨vs, st, hrun, himp st vs hp⟩⟩

omit inst in
/-- Transport `wp_wasm_prop` along a fuel-indexed execution equation: if
`prog` from `(st, locals)` always reduces to `prog'` from `(st', locals')`
(with structural fuel offsets `K` and `c` fixed by the instructions crossed),
then a WP for the reduct is a WP for the original. Program proofs use this
to hop over an already-traced straight-line or block prefix to the next
composition point (typically a `.call` handled by `wp_wasm_prop_call`)
without threading concrete fuel values. -/
theorem wp_wasm_prop_of_exec_eq
    {m : Module} {st st' : Store Unit} {locals locals' : Locals}
    {prog prog' : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop} (K c : Nat)
    (h : ∀ fuel, exec (fuel + K) m st locals prog env
               = exec (fuel + c) m st' locals' prog' env)
    (hwp : wp_wasm_prop m st' locals' prog' env Q) :
    wp_wasm_prop m st locals prog env Q := by
  obtain ⟨n, hn⟩ := hwp
  have hne : exec n m st' locals' prog' env ≠ .OutOfFuel := by
    intro ho; simp only [ho] at hn
  refine ⟨n + K, ?_⟩
  rw [h n, exec_fuel_mono (Nat.le_add_right n c) hne]
  exact hn

/-- Discharge the ghost-update obligation of a per-instruction rule when the
step leaves the ghost heap untouched — every current rule: memory facts enter
the load/store rules as pure hypotheses (see the note on `wp_wasm_F`), so the
heap resource passes through unchanged. Collapses the per-step
`iintro/imodintro/iexists` boilerplate of program proofs to a single
combinator: `wp_wasm_localGet hget (ghost_id ?_)`. -/
theorem ghost_id {P : IProp WasmHeapGF} (h : ⊢ P) :
    ∀ σ : WasmHeapMap (Option UInt8),
      ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8), genHeapInterp σ' ∗ P := by
  intro σ
  iintro Hσ
  imodintro
  iexists σ
  isplitl [Hσ]
  · iexact Hσ
  · exact h

/-- Terminal rule: a program at `.ret` satisfies the WP when the
postcondition holds of the current store and value stack. Closes the
per-instruction chain of a program proof. -/
theorem wp_wasm_ret
    {m : Module} {st : Store Unit} {locals : Locals} {rest : Program}
    {env : HostEnv Unit} {Q : Store Unit → List Value → Prop}
    (h : Q st locals.values) :
    ⊢ wp_wasm m st locals (.ret :: rest) env Q := by
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  unfold wp_wasm_F
  dsimp only []
  exact BI.pure_intro h

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
        genHeapInterp σ ∗
        wp_wasm m st { locals with values := v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.globalGet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hget]) rfl hstep

theorem wp_wasm_globalSet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value} {vs : List Value} {old : Value}
    (hstack : locals.values = v :: vs)
    (hbound : st.globals.globals[i]? = some old)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗ wp_wasm m
          { st with globals := { globals := st.globals.globals.set i v } }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.globalSet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack, hbound])
    (show { st with globals := { globals := st.globals.globals.set i v } }.mem = st.mem from rfl)
    hstep

theorem wp_wasm_localGet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value}
    (hget : locals.get i = some v)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗
        wp_wasm m st { locals with values := v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.localGet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hget]) rfl hstep

theorem wp_wasm_localSet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value} {vs : List Value} {locals' : Locals}
    (hstack : locals.values = v :: vs)
    (hset : locals.set? i v = some locals')
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗
        wp_wasm m st { locals' with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.localSet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack, hset]) rfl hstep

theorem wp_wasm_const
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (v : UInt32)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗
        wp_wasm m st { locals with values := .i32 v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.const v :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def]) rfl hstep

theorem wp_wasm_add
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗
        wp_wasm m st { locals with values := .i32 (a + b) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.add :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) rfl hstep

theorem wp_wasm_sub
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗
        wp_wasm m st { locals with values := .i32 (b - a) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.sub :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) rfl hstep

theorem wp_wasm_load64
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗ wp_wasm m st
          { locals with values := .i64 (st.mem.read64 (addr + off)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.load64 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    rfl hstep

theorem wp_wasm_store64
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {v : UInt64} {vs : List Value}
    (hstack : locals.values = .i64 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        heapAgreesWithMem σ st.mem →
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        ⌜heapAgreesWithMem σ' (st.mem.write64 (addr + off) v)⌝ ∗ genHeapInterp σ' ∗ wp_wasm m
          { st with mem := st.mem.write64 (addr + off) v }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.store64 off :: rest) env Q := by
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  -- concrete prog means simp already evaluated the match to the step case
  unfold wp_wasm at hstep
  iintro %σ %hagree Hσ
  imod (hstep σ hagree) $$ Hσ with ⟨%σ', hagree', Hσ', Hwp⟩
  imodintro
  iexists σ', { st with mem := st.mem.write64 (addr + off) v }, { locals with values := vs }
  isplitl []
  · exact BI.pure_intro (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
  · isplitl [hagree']
    · iexact hagree'
    · isplitl [Hσ']
      · iexact Hσ'
      · iexact Hwp

theorem wp_wasm_load32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        genHeapInterp σ ∗ wp_wasm m st
          { locals with values := .i32 (st.mem.read32 (addr + off)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.load32 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    rfl hstep

theorem wp_wasm_store32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {v : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        heapAgreesWithMem σ st.mem →
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        ⌜heapAgreesWithMem σ' (st.mem.write32 (addr + off) v)⌝ ∗ genHeapInterp σ' ∗ wp_wasm m
          { st with mem := st.mem.write32 (addr + off) v }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.store32 off :: rest) env Q := by
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  -- concrete prog means simp already evaluated the match to the step case
  unfold wp_wasm at hstep
  iintro %σ %hagree Hσ
  imod (hstep σ hagree) $$ Hσ with ⟨%σ', hagree', Hσ', Hwp⟩
  imodintro
  iexists σ', { st with mem := st.mem.write32 (addr + off) v }, { locals with values := vs }
  isplitl []
  · exact BI.pure_intro (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
  · isplitl [hagree']
    · iexact hagree'
    · isplitl [Hσ']
      · iexact Hσ'
      · iexact Hwp


omit inst in

theorem wp_iProp_load64 [WasmHeapGS]
    {σ : WasmHeapMap (Option UInt8)} {addr : UInt32} {v : UInt64} {mem : Mem}
    (hagree : heapAgreesWithMem σ mem)
    (hnw : addr.toNat + 8 ≤ 2 ^ 32) :
    genHeapInterp σ ∗ pointsTo_u64 addr v ==∗
      genHeapInterp σ ∗ pointsTo_u64 addr v ∗ ⌜mem.read64 addr = v⌝ := by
  simp only [pointsTo_u64]
  iintro ⟨Hσ, Hpt0, Hpt1, Hpt2, Hpt3, Hpt4, Hpt5, Hpt6, Hpt7⟩
  have haddr0 : addr + UInt32.ofNat 0 = addr := by
    apply UInt32.toNat.inj; rw [toNat_add_ofNat addr 0 (by omega)]; simp
  ihave %Hget0 : ⌜get? σ addr = some (some (byte64 v 0))⌝ $$ [Hσ Hpt0]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt0]; itrivial
  ihave %Hget1 : ⌜get? σ (addr + 1) = some (some (byte64 v 1))⌝ $$ [Hσ Hpt1]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt1]; itrivial
  ihave %Hget2 : ⌜get? σ (addr + 2) = some (some (byte64 v 2))⌝ $$ [Hσ Hpt2]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt2]; itrivial
  ihave %Hget3 : ⌜get? σ (addr + 3) = some (some (byte64 v 3))⌝ $$ [Hσ Hpt3]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt3]; itrivial
  ihave %Hget4 : ⌜get? σ (addr + 4) = some (some (byte64 v 4))⌝ $$ [Hσ Hpt4]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt4]; itrivial
  ihave %Hget5 : ⌜get? σ (addr + 5) = some (some (byte64 v 5))⌝ $$ [Hσ Hpt5]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt5]; itrivial
  ihave %Hget6 : ⌜get? σ (addr + 6) = some (some (byte64 v 6))⌝ $$ [Hσ Hpt6]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt6]; itrivial
  ihave %Hget7 : ⌜get? σ (addr + 7) = some (some (byte64 v 7))⌝ $$ [Hσ Hpt7]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt7]; itrivial
  have hmem : mem.read64 addr = v :=
    read64_sound σ mem addr v hnw hagree (fun i hi => by
      have h8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases h8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · simp only [haddr0]; exact Hget0
      · exact Hget1
      · exact Hget2
      · exact Hget3
      · exact Hget4
      · exact Hget5
      · exact Hget6
      · exact Hget7)
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hpt0 Hpt1 Hpt2 Hpt3 Hpt4 Hpt5 Hpt6 Hpt7]
  · isplitl [Hpt0]; · iexact Hpt0
    isplitl [Hpt1]; · iexact Hpt1
    isplitl [Hpt2]; · iexact Hpt2
    isplitl [Hpt3]; · iexact Hpt3
    isplitl [Hpt4]; · iexact Hpt4
    isplitl [Hpt5]; · iexact Hpt5
    isplitl [Hpt6]; · iexact Hpt6
    iexact Hpt7
  · ipureintro; exact hmem

theorem wp_iProp_store64 [WasmHeapGS]
    {σ : WasmHeapMap (Option UInt8)} {addr : UInt32} {v_old v_new : UInt64} {mem : Mem}
    (hagree : heapAgreesWithMem σ mem)
    (hnw : addr.toNat + 8 ≤ 2 ^ 32) :
    genHeapInterp σ ∗ pointsTo_u64 addr v_old ==∗
      ∃ σ' : WasmHeapMap (Option UInt8),
        ⌜heapAgreesWithMem σ' (mem.write64 addr v_new)⌝ ∗
        genHeapInterp σ' ∗ pointsTo_u64 addr v_new := by
  let σ' : WasmHeapMap (Option UInt8) :=
    insert (insert (insert (insert (insert (insert (insert (insert σ
      addr (some (byte64 v_new 0)))
      (addr + 1) (some (byte64 v_new 1)))
      (addr + 2) (some (byte64 v_new 2)))
      (addr + 3) (some (byte64 v_new 3)))
      (addr + 4) (some (byte64 v_new 4)))
      (addr + 5) (some (byte64 v_new 5)))
      (addr + 6) (some (byte64 v_new 6)))
      (addr + 7) (some (byte64 v_new 7))
  have haddr0 : addr + UInt32.ofNat 0 = addr := by
    apply UInt32.toNat.inj; rw [toNat_add_ofNat addr 0 (by omega)]; simp
  simp only [pointsTo_u64]
  iintro ⟨Hσ, Hpt0, Hpt1, Hpt2, Hpt3, Hpt4, Hpt5, Hpt6, Hpt7⟩
  imod genHeap_update (v₂ := some (byte64 v_new 0)) $$ [$Hσ $Hpt0] with ⟨Hσ, Hpt0⟩
  imod genHeap_update (v₂ := some (byte64 v_new 1)) $$ [$Hσ $Hpt1] with ⟨Hσ, Hpt1⟩
  imod genHeap_update (v₂ := some (byte64 v_new 2)) $$ [$Hσ $Hpt2] with ⟨Hσ, Hpt2⟩
  imod genHeap_update (v₂ := some (byte64 v_new 3)) $$ [$Hσ $Hpt3] with ⟨Hσ, Hpt3⟩
  imod genHeap_update (v₂ := some (byte64 v_new 4)) $$ [$Hσ $Hpt4] with ⟨Hσ, Hpt4⟩
  imod genHeap_update (v₂ := some (byte64 v_new 5)) $$ [$Hσ $Hpt5] with ⟨Hσ, Hpt5⟩
  imod genHeap_update (v₂ := some (byte64 v_new 6)) $$ [$Hσ $Hpt6] with ⟨Hσ, Hpt6⟩
  imod genHeap_update (v₂ := some (byte64 v_new 7)) $$ [$Hσ $Hpt7] with ⟨Hσ, Hpt7⟩
  ihave %Hget0 : ⌜get? σ' addr = some (some (byte64 v_new 0))⌝ $$ [Hσ Hpt0]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt0]; itrivial
  ihave %Hget1 : ⌜get? σ' (addr + 1) = some (some (byte64 v_new 1))⌝ $$ [Hσ Hpt1]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt1]; itrivial
  ihave %Hget2 : ⌜get? σ' (addr + 2) = some (some (byte64 v_new 2))⌝ $$ [Hσ Hpt2]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt2]; itrivial
  ihave %Hget3 : ⌜get? σ' (addr + 3) = some (some (byte64 v_new 3))⌝ $$ [Hσ Hpt3]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt3]; itrivial
  ihave %Hget4 : ⌜get? σ' (addr + 4) = some (some (byte64 v_new 4))⌝ $$ [Hσ Hpt4]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt4]; itrivial
  ihave %Hget5 : ⌜get? σ' (addr + 5) = some (some (byte64 v_new 5))⌝ $$ [Hσ Hpt5]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt5]; itrivial
  ihave %Hget6 : ⌜get? σ' (addr + 6) = some (some (byte64 v_new 6))⌝ $$ [Hσ Hpt6]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt6]; itrivial
  ihave %Hget7 : ⌜get? σ' (addr + 7) = some (some (byte64 v_new 7))⌝ $$ [Hσ Hpt7]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt7]; itrivial
  have hagree' : heapAgreesWithMem σ' (mem.write64 addr v_new) :=
    write64_agree σ σ' mem addr v_new hnw hagree
      (fun i hi => by
        have h8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
        rcases h8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · simp only [haddr0]; exact Hget0
        · exact Hget1
        · exact Hget2
        · exact Hget3
        · exact Hget4
        · exact Hget5
        · exact Hget6
        · exact Hget7)
      (fun k w hk hne => by
        have ne0 : addr ≠ k := fun h => hne 0 (by omega) (h.symm.trans haddr0.symm)
        have ne1 : (addr + 1 : UInt32) ≠ k := Ne.symm (hne 1 (by omega))
        have ne2 : (addr + 2 : UInt32) ≠ k := Ne.symm (hne 2 (by omega))
        have ne3 : (addr + 3 : UInt32) ≠ k := Ne.symm (hne 3 (by omega))
        have ne4 : (addr + 4 : UInt32) ≠ k := Ne.symm (hne 4 (by omega))
        have ne5 : (addr + 5 : UInt32) ≠ k := Ne.symm (hne 5 (by omega))
        have ne6 : (addr + 6 : UInt32) ≠ k := Ne.symm (hne 6 (by omega))
        have ne7 : (addr + 7 : UInt32) ≠ k := Ne.symm (hne 7 (by omega))
        have heq : σ' = insert (insert (insert (insert (insert (insert (insert (insert σ
            addr (some (byte64 v_new 0))) (addr + 1) (some (byte64 v_new 1)))
            (addr + 2) (some (byte64 v_new 2))) (addr + 3) (some (byte64 v_new 3)))
            (addr + 4) (some (byte64 v_new 4))) (addr + 5) (some (byte64 v_new 5)))
            (addr + 6) (some (byte64 v_new 6))) (addr + 7) (some (byte64 v_new 7)) := rfl
        rw [heq] at hk
        rwa [get?_insert_ne ne7, get?_insert_ne ne6, get?_insert_ne ne5,
             get?_insert_ne ne4, get?_insert_ne ne3, get?_insert_ne ne2,
             get?_insert_ne ne1, get?_insert_ne ne0] at hk)
  imodintro
  iexists σ'
  isplitl []
  · ipureintro; exact hagree'
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hpt0]
  · iexact Hpt0
  isplitl [Hpt1]
  · iexact Hpt1
  isplitl [Hpt2]
  · iexact Hpt2
  isplitl [Hpt3]
  · iexact Hpt3
  isplitl [Hpt4]
  · iexact Hpt4
  isplitl [Hpt5]
  · iexact Hpt5
  isplitl [Hpt6]
  · iexact Hpt6
  iexact Hpt7

theorem wp_iProp_load32 [WasmHeapGS]
    {σ : WasmHeapMap (Option UInt8)} {addr : UInt32} {v : UInt32} {mem : Mem}
    (hagree : heapAgreesWithMem σ mem)
    (hnw : addr.toNat + 4 ≤ 2 ^ 32) :
    genHeapInterp σ ∗ pointsTo_u32 addr v ==∗
      genHeapInterp σ ∗ pointsTo_u32 addr v ∗ ⌜mem.read32 addr = v⌝ := by
  simp only [pointsTo_u32]
  iintro ⟨Hσ, Hpt0, Hpt1, Hpt2, Hpt3⟩
  have haddr0 : addr + UInt32.ofNat 0 = addr := by
    apply UInt32.toNat.inj; rw [toNat_add_ofNat addr 0 (by omega)]; simp
  ihave %Hget0 : ⌜get? σ addr = some (some (byte32 v 0))⌝ $$ [Hσ Hpt0]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt0]; itrivial
  ihave %Hget1 : ⌜get? σ (addr + 1) = some (some (byte32 v 1))⌝ $$ [Hσ Hpt1]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt1]; itrivial
  ihave %Hget2 : ⌜get? σ (addr + 2) = some (some (byte32 v 2))⌝ $$ [Hσ Hpt2]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt2]; itrivial
  ihave %Hget3 : ⌜get? σ (addr + 3) = some (some (byte32 v 3))⌝ $$ [Hσ Hpt3]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt3]; itrivial
  have hmem : mem.read32 addr = v :=
    read32_sound σ mem addr v hnw hagree (fun i hi => by
      have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h4 with rfl|rfl|rfl|rfl
      · simp only [haddr0]; exact Hget0
      · exact Hget1
      · exact Hget2
      · exact Hget3)
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hpt0 Hpt1 Hpt2 Hpt3]
  · isplitl [Hpt0]; · iexact Hpt0
    isplitl [Hpt1]; · iexact Hpt1
    isplitl [Hpt2]; · iexact Hpt2
    iexact Hpt3
  · ipureintro; exact hmem

theorem wp_iProp_store32 [WasmHeapGS]
    {σ : WasmHeapMap (Option UInt8)} {addr : UInt32} {v_old v_new : UInt32} {mem : Mem}
    (hagree : heapAgreesWithMem σ mem)
    (hnw : addr.toNat + 4 ≤ 2 ^ 32) :
    genHeapInterp σ ∗ pointsTo_u32 addr v_old ==∗
      ∃ σ' : WasmHeapMap (Option UInt8),
        ⌜heapAgreesWithMem σ' (mem.write32 addr v_new)⌝ ∗
        genHeapInterp σ' ∗ pointsTo_u32 addr v_new := by
  let σ' : WasmHeapMap (Option UInt8) :=
    insert (insert (insert (insert σ
      addr (some (byte32 v_new 0)))
      (addr + 1) (some (byte32 v_new 1)))
      (addr + 2) (some (byte32 v_new 2)))
      (addr + 3) (some (byte32 v_new 3))
  have haddr0 : addr + UInt32.ofNat 0 = addr := by
    apply UInt32.toNat.inj; rw [toNat_add_ofNat addr 0 (by omega)]; simp
  simp only [pointsTo_u32]
  iintro ⟨Hσ, Hpt0, Hpt1, Hpt2, Hpt3⟩
  imod genHeap_update (v₂ := some (byte32 v_new 0)) $$ [$Hσ $Hpt0] with ⟨Hσ, Hpt0⟩
  imod genHeap_update (v₂ := some (byte32 v_new 1)) $$ [$Hσ $Hpt1] with ⟨Hσ, Hpt1⟩
  imod genHeap_update (v₂ := some (byte32 v_new 2)) $$ [$Hσ $Hpt2] with ⟨Hσ, Hpt2⟩
  imod genHeap_update (v₂ := some (byte32 v_new 3)) $$ [$Hσ $Hpt3] with ⟨Hσ, Hpt3⟩
  ihave %Hget0 : ⌜get? σ' addr = some (some (byte32 v_new 0))⌝ $$ [Hσ Hpt0]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt0]; itrivial
  ihave %Hget1 : ⌜get? σ' (addr + 1) = some (some (byte32 v_new 1))⌝ $$ [Hσ Hpt1]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt1]; itrivial
  ihave %Hget2 : ⌜get? σ' (addr + 2) = some (some (byte32 v_new 2))⌝ $$ [Hσ Hpt2]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt2]; itrivial
  ihave %Hget3 : ⌜get? σ' (addr + 3) = some (some (byte32 v_new 3))⌝ $$ [Hσ Hpt3]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt3]; itrivial
  have hagree' : heapAgreesWithMem σ' (mem.write32 addr v_new) :=
    write32_agree σ σ' mem addr v_new hnw hagree
      (fun i hi => by
        have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases h4 with rfl|rfl|rfl|rfl
        · simp only [haddr0]; exact Hget0
        · exact Hget1
        · exact Hget2
        · exact Hget3)
      (fun k w hk hne => by
        have ne0 : addr ≠ k := fun h => hne 0 (by omega) (h.symm.trans haddr0.symm)
        have ne1 : (addr + 1 : UInt32) ≠ k := Ne.symm (hne 1 (by omega))
        have ne2 : (addr + 2 : UInt32) ≠ k := Ne.symm (hne 2 (by omega))
        have ne3 : (addr + 3 : UInt32) ≠ k := Ne.symm (hne 3 (by omega))
        have heq : σ' = insert (insert (insert (insert σ
            addr (some (byte32 v_new 0))) (addr + 1) (some (byte32 v_new 1)))
            (addr + 2) (some (byte32 v_new 2))) (addr + 3) (some (byte32 v_new 3)) := rfl
        rw [heq] at hk
        rwa [get?_insert_ne ne3, get?_insert_ne ne2,
             get?_insert_ne ne1, get?_insert_ne ne0] at hk)
  imodintro
  iexists σ'
  isplitl []
  · ipureintro; exact hagree'
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hpt0]
  · iexact Hpt0
  isplitl [Hpt1]
  · iexact Hpt1
  isplitl [Hpt2]
  · iexact Hpt2
  iexact Hpt3


theorem wp_wasm_prop_to_TerminatesWith
    {m : Module} {id : Nat} {f : Function}
    {initial : Store Unit} {args : List Value}
    {env : HostEnv Unit}
    {P : Store Unit → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (himp : m.imports[id]? = none)
    (hresults : f.results.length = 0)
    (hlen : args.length ≤ f.numParams)
    (hcompat : ∀ st' vals, P st' vals → P st' [])
    (hwp : wp_wasm_prop m initial
        (f.toLocals (args.take f.numParams).reverse)
        f.body env P) :
    TerminatesWith env m id initial args P := by
  obtain ⟨fuel₀, hwp_fuel⟩ := hwp
  have hcr : args.drop f.numParams = [] := List.drop_eq_nil_of_le hlen
  cases hexec : exec fuel₀ m initial (f.toLocals (args.take f.numParams).reverse) f.body env with
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

-- Bridge: iProp wp_wasm proof → Prop wp_wasm_prop
-- Creates ghost state internally via genHeap_init_names,
-- applies the iProp proof, then extracts the pure result.
-- This is HeapLang's heap_adequacy pattern.
omit inst in
theorem wasm_heap_adequacy
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (hwp : ∀ [WasmHeapGS], ⊢ wp_wasm m st locals prog env Q) :
    wp_wasm_prop m st locals prog env Q := by
  apply pure_soundness (PROP := IProp WasmHeapGF)
  have hbupd : emp ⊢ (|==> ⌜wp_wasm_prop m st locals prog env Q⌝ : IProp WasmHeapGF) := by
    refine (genHeap_init (L := UInt32) (V := Option UInt8)
        (GF := WasmHeapGF) (H := WasmHeapMap) ∅).trans ?_
    apply bupd_mono
    apply BI.exists_elim
    intro G
    letI inst : WasmHeapGS := WasmHeapGS.mk (togenHeapGS := G)
    apply BI.sep_elim_left.trans
    apply (BI.sep_intro_emp_valid_right .rfl hwp).trans
    exact wasm_adequacy m st locals prog env Q ∅ (fun addr _ h => by
      have he : get? (∅ : WasmHeapMap (Option UInt8)) addr = none := rfl
      simp [he] at h)
  exact hbupd.trans bupd_elim

-- Adequacy with memory footprint: allocates ghost state from σ, hands
-- ownership tokens to hwp via a wand, then extracts the pure result.
-- Use when the proof needs pointsTo_u64 / pointsTo_u32 for memory reads/writes.
theorem wasm_heap_adequacy_with_mem
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ : WasmHeapMap (Option UInt8))
    (hagree : heapAgreesWithMem σ st.mem)
    (hwp : ∀ [inst : WasmHeapGS],
        ⊢ ([∗map] l ↦ v ∈ σ, pointsTo l (DFrac.own 1) v) -∗
          wp_wasm m st locals prog env Q) :
    wp_wasm_prop m st locals prog env Q := by
  apply pure_soundness (PROP := IProp WasmHeapGF)
  have hbupd : emp ⊢ (|==> ⌜wp_wasm_prop m st locals prog env Q⌝ : IProp WasmHeapGF) := by
    refine (genHeap_init (L := UInt32) (V := Option UInt8)
        (GF := WasmHeapGF) (H := WasmHeapMap) σ).trans ?_
    apply bupd_mono
    apply BI.exists_elim
    intro G
    letI inst : WasmHeapGS := WasmHeapGS.mk (togenHeapGS := G)
    apply (BI.sep_mono_right BI.sep_elim_left).trans
    exact (BI.sep_mono_right (BI.sep_elim_emp_valid_left hwp BI.wand_elim_left)).trans
      (wasm_adequacy m st locals prog env Q σ hagree)
  exact hbupd.trans bupd_elim

end Wasm.SepLogic
