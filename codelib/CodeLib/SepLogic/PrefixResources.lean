import CodeLib.SepLogic.SequentialExecution
import Iris.ProgramLogic.Adequacy

/-!
# Physical facts at arbitrary execution prefixes

Forward replay retains a caller's frame and the interpretation of the actual
reached store, even when execution is still running. A physical fact follows
only from a supplied, valid readout of that store and retained ownership.
Page snapshots provide lower bounds; cap tokens provide physical upper bounds.
Nothing here turns a snapshot into an exact or exclusive page count.
-/

namespace Wasm.SmallStep

open Wasm.SepLogic Iris Iris.ProgramLogic Language.Notation

variable {α : Type} {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) prefixTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

section Replay

variable [WasmSmallStepGS hlc α]

local instance (priority := high) prefixTerminalIrisGS :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      prefixTerminalLanguage (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }

/-- Read a fact about a reached physical store while retaining the actual
state, residual total WP, and arbitrary caller frame. No terminal endpoint or
completed execution is assumed. The readout is an explicit proof obligation. -/
theorem twp_prefix_readout
    {initial reached : Config α} {trace : List StepKind}
    (execution : Steps initial trace reached)
    (ns : Nat) (observations : List StepKind) (threads : Nat)
    (frame : IProp (WasmHeapGF α)) (fact : MachineStore α → Prop)
    (readout : ∀ store ns observations threads,
      stateInterp (GF := WasmHeapGF α) store ns observations threads ∗ frame ⊢
        iprop(⌜fact store⌝))
    {s : Stuckness} {E : CoPset} {post : Terminal → IProp (WasmHeapGF α)} :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ∗ frame ={E}=∗
      stateInterp (GF := WasmHeapGF α) reached.store
        (ns + trace.length) observations threads ∗
      WP reached.expr @ s; E [{ post }] ∗ frame ∗ ⌜fact reached.store⌝ := by
  iintro ⟨Hstate, Hwp, Hframe⟩
  imod twp_replay_steps execution ns observations threads $$ [Hstate Hwp] with
    ⟨Hstate, Hwp⟩
  · iframe Hstate Hwp
  ihave %hfact := readout reached.store (ns + trace.length) observations threads $$
      [Hstate Hframe]
  · iframe Hstate Hframe
  imodintro
  iframe Hstate Hwp Hframe
  ipureexact hfact

/-- Persistent physical ownership bounds every actual execution prefix. The
lower endpoint comes from the page snapshot and the upper endpoint from the
actual cap slot; they need not be equal. -/
theorem twp_prefix_page_interval
    {initial reached : Config α} {trace : List StepKind}
    (execution : Steps initial trace reached)
    (ns : Nat) (observations : List StepKind) (threads lower cap : Nat)
    {s : Stuckness} {E : CoPset} {post : Terminal → IProp (WasmHeapGF α)} :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ∗
      memoryCapOwn 0 cap ∗ memoryPagesOwn lower ={E}=∗
      stateInterp (GF := WasmHeapGF α) reached.store
        (ns + trace.length) observations threads ∗
      WP reached.expr @ s; E [{ post }] ∗
      (memoryCapOwn 0 cap ∗ memoryPagesOwn lower) ∗
      ⌜lower ≤ reached.store.wasm.mem.pages ∧
        reached.store.wasm.mem.pages ≤ cap⌝ := by
  iapply twp_prefix_readout execution ns observations threads
    iprop(memoryCapOwn 0 cap ∗ memoryPagesOwn lower)
    (fun store => lower ≤ store.wasm.mem.pages ∧ store.wasm.mem.pages ≤ cap)
  intro store ns observations threads
  iintro ⟨Hstate, Hcap, Hpages⟩
  ihave %hcap := stateInterp_memoryCap_primary
      store ns observations threads cap $$ [Hstate Hcap]
  · iframe Hstate Hcap
  imod stateInterp_memoryPages_agree store ns observations threads lower $$
      [Hstate Hpages] with ⟨_, _, %hlower⟩
  · iframe Hstate Hpages
  ipureexact ⟨hlower, hcap.2⟩

/-- A retained frozen authority gives an exact count at every actual prefix.
The state interpretation supplies the readout; no extra readout premise,
terminal endpoint, page monotonicity or label filter is assumed. -/
theorem twp_prefix_frozen_pages
    {initial reached : Config α} {trace : List StepKind}
    (execution : Steps initial trace reached)
    (ns : Nat) (observations : List StepKind) (threads pages : Nat)
    {s : Stuckness} {E : CoPset} {post : Terminal → IProp (WasmHeapGF α)} :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ∗ memoryPagesFrozen pages ={E}=∗
      stateInterp (GF := WasmHeapGF α) reached.store
        (ns + trace.length) observations threads ∗
      WP reached.expr @ s; E [{ post }] ∗ memoryPagesFrozen pages ∗
      ⌜reached.store.wasm.mem.pages = pages⌝ :=
  twp_prefix_readout execution ns observations threads (memoryPagesFrozen pages)
    (fun store => store.wasm.mem.pages = pages)
    (fun store ns observations threads =>
      stateInterp_memoryPages_frozen_agree store ns observations threads pages)

end Replay

/-- Pure invariance for any supplied Wasm prefix, including a running endpoint.
The setup allocates its state interpretation and must provide a sound readout
at the reached store. The total WP is used through its partial-WP projection;
the conclusion does not require or assert that this prefix is terminal. -/
theorem twp_prefix_invariance
    [InvGpreS (WasmHeapGF α)]
    (initial reached : Config α) (trace : List StepKind) (fact : Prop)
    (setup : ∀ [InvGS_gen .hasLC (WasmHeapGF α)] (observations : List StepKind),
      ⊢ iprop(|={⊤}=>
        ∃ (stateI : MachineStore α → List StepKind → Nat → IProp (WasmHeapGF α))
          (forkPost : Terminal → IProp (WasmHeapGF α)),
        letI _ : IrisGS_gen .hasLC (Expr α) (WasmHeapGF α) :=
          .mk (toStateInterp := ⟨fun store _ => stateI store⟩)
            (fun _ => 0) forkPost (fun _ _ _ _ => fupd_intro)
        iprop(stateI initial.store observations 0 ∗
          WP initial.expr @ Stuckness.NotStuck; ⊤ [{ _value, iprop(True) }] ∗
          (stateI reached.store [] 0 -∗
            ∃ E : CoPset, |={⊤,E}=> ⌜fact⌝))))
    (execution : Steps initial trace reached) : fact := by
  apply wp_invariance_gen (GF := WasmHeapGF α) (hlc := .hasLC)
    Stuckness.NotStuck initial.expr initial.store reached.store
    [reached.expr] fact (Hsteps := execution.to_languageErasedSteps)
  intro inv observations
  imod setup observations with ⟨%stateI, %forkPost, Hstate, Hwp, Hread⟩
  letI : IrisGS_gen .hasLC (Expr α) (WasmHeapGF α) :=
    .mk (toStateInterp := ⟨fun store _ => stateI store⟩)
      (fun _ => 0) forkPost (fun _ _ _ _ => fupd_intro)
  iexists stateI, forkPost
  imodintro
  isplitl_exact Hstate
  isplitl [Hwp]
  · iapply twp.to_wp
    iexact Hwp
  isimp only [List.length_singleton, Nat.pred_succ]
  iexact Hread

end Wasm.SmallStep
