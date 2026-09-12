import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Sequential execution with physical resources

A certificate records an actual Wasm trace and resources for exactly its final
physical store. Composition feeds that store to the next certificate. This is
not a weakest precondition and does not permit an intermediate store to be
replaced without proving a corresponding execution and resource update.
-/

namespace Wasm.SmallStep

open Wasm.SepLogic Iris Iris.ProgramLogic Language.Notation

/-- Determinism identifies endpoints after the same number of actual steps.
The initial configuration, including its caller context, must be identical. -/
theorem Steps.final_eq_of_length_eq
    {initial left right : Config α} {leftTrace rightTrace : List StepKind}
    (leftRun : Steps initial leftTrace left)
    (rightRun : Steps initial rightTrace right)
    (lengths : leftTrace.length = rightTrace.length) : left = right := by
  induction leftRun generalizing right rightTrace with
  | refl =>
      cases rightRun with
      | refl => rfl
      | cons => simp at lengths
  | cons leftHead leftTail ih =>
      cases rightRun with
      | refl => simp at lengths
      | cons rightHead rightTail =>
          obtain ⟨rfl, rfl⟩ := step_deterministic leftHead rightHead
          exact ih rightTail (by simpa only [List.length_cons, Nat.succ.injEq] using lengths)

variable [WasmSmallStepGS hlc α]

/-- A finite execution result with a step budget and matching final resources.
The observations argument is the Iris observation tail; Wasm step labels remain
in the separate authoritative trace. -/
def SequentialExecution (initial : Config α) (ns : Nat)
    (observations : List StepKind) (threads budget : Nat)
    (post : Config α → IProp (WasmHeapGF α)) : IProp (WasmHeapGF α) :=
  iprop(∃ (trace : List StepKind) (final : Config α),
    ⌜Steps initial trace final ∧ trace.length ≤ budget⌝ ∗
    stateInterp (GF := WasmHeapGF α) final.store (ns + trace.length) observations threads ∗
    post final)

namespace SequentialExecution

theorem of_steps {initial final : Config α} {trace : List StepKind}
    (ns : Nat) (observations : List StepKind) (threads budget : Nat)
    (post : Config α → IProp (WasmHeapGF α))
    (execution : Steps initial trace final) (bound : trace.length ≤ budget) :
    stateInterp (GF := WasmHeapGF α) final.store (ns + trace.length) observations threads ∗
      post final ⊢ SequentialExecution initial ns observations threads budget post := by
  unfold SequentialExecution
  iintro ⟨Hstate, Hpost⟩
  iexists trace, final
  iframe_pureexact using [Hstate Hpost] => ⟨execution, bound⟩

theorem refl (initial : Config α) (ns : Nat) (observations : List StepKind)
    (threads : Nat) (post : Config α → IProp (WasmHeapGF α)) :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      post initial ⊢ SequentialExecution initial ns observations threads 0 post := by
  exact of_steps ns observations threads 0 post (.refl initial) (by decide)

/-- Sequential composition opens only the final state actually produced by
the first trace. Budgets add and all labels are retained by concatenation. -/
theorem bind (initial : Config α) (ns : Nat) (observations : List StepKind)
    (threads firstBudget secondBudget : Nat)
    (middlePost finalPost : Config α → IProp (WasmHeapGF α))
    (next : ∀ (middle : Config α) (nextSteps : Nat),
      stateInterp (GF := WasmHeapGF α) middle.store nextSteps observations threads ∗
        middlePost middle ==∗
          SequentialExecution middle nextSteps observations threads secondBudget finalPost) :
    SequentialExecution initial ns observations threads firstBudget middlePost ==∗
      SequentialExecution initial ns observations threads (firstBudget + secondBudget) finalPost := by
  unfold SequentialExecution at next ⊢
  iintro ⟨%firstTrace, %middle, %hfirst, Hstate, Hmiddle⟩
  imod next middle (ns + firstTrace.length) $$ [Hstate Hmiddle] with
    ⟨%secondTrace, %final, %hsecond, Hstate, Hfinal⟩
  · iframe
  imodintro
  iexists firstTrace ++ secondTrace, final
  isplitr_pureexact ⟨hfirst.1.trans hsecond.1, by
    simp only [List.length_append]
    exact Nat.add_le_add hfirst.2 hsecond.2⟩
  isimp only [List.length_append, Nat.add_assoc] at Hstate
  isimp only [List.length_append, Nat.add_assoc]
  iframe

/-- The same composition rule for a continuation obtained by total-WP
replay, which exposes a fancy update at the existing mask. -/
theorem bind_fupd (initial : Config α) (ns : Nat) (observations : List StepKind)
    (threads firstBudget secondBudget : Nat) (E : CoPset)
    (middlePost finalPost : Config α → IProp (WasmHeapGF α))
    (next : ∀ (middle : Config α) (nextSteps : Nat),
      stateInterp (GF := WasmHeapGF α) middle.store nextSteps observations threads ∗
        middlePost middle ={E}=∗
          SequentialExecution middle nextSteps observations threads secondBudget finalPost) :
    SequentialExecution initial ns observations threads firstBudget middlePost ={E}=∗
      SequentialExecution initial ns observations threads (firstBudget + secondBudget) finalPost := by
  unfold SequentialExecution at next ⊢
  iintro ⟨%firstTrace, %middle, %hfirst, Hstate, Hmiddle⟩
  imod next middle (ns + firstTrace.length) $$ [Hstate Hmiddle] with
    ⟨%secondTrace, %final, %hsecond, Hstate, Hfinal⟩
  · iframe
  imodintro
  iexists firstTrace ++ secondTrace, final
  isplitr_pureexact ⟨hfirst.1.trans hsecond.1, by
    simp only [List.length_append]
    exact Nat.add_le_add hfirst.2 hsecond.2⟩
  isimp only [List.length_append, Nat.add_assoc] at Hstate
  isimp only [List.length_append, Nat.add_assoc]
  iframe

theorem frame (initial : Config α) (ns : Nat) (observations : List StepKind)
    (threads budget : Nat) (post : Config α → IProp (WasmHeapGF α))
    (frame : IProp (WasmHeapGF α)) :
    SequentialExecution initial ns observations threads budget post ∗ frame ⊢
      SequentialExecution initial ns observations threads budget
        (fun final => iprop(post final ∗ frame)) := by
  unfold SequentialExecution
  iintro ⟨⟨%trace, %final, %hexecution, Hstate, Hpost⟩, Hframe⟩
  iexists trace, final
  isplitr_pureexact hexecution
  isplitl_exact Hstate
  isplitl_exact Hpost
  iexact Hframe

theorem mono (initial : Config α) (ns : Nat) (observations : List StepKind)
    (threads oldBudget newBudget : Nat)
    (post post' : Config α → IProp (WasmHeapGF α))
    (hbudget : oldBudget ≤ newBudget) (hpost : ∀ final, post final ⊢ post' final) :
    SequentialExecution initial ns observations threads oldBudget post ⊢
      SequentialExecution initial ns observations threads newBudget post' := by
  unfold SequentialExecution
  iintro ⟨%trace, %final, %hexecution, Hstate, Hpost⟩
  ihave Hpost' := hpost final $$ Hpost
  iexists trace, final
  iframe_pureexact using [Hstate Hpost'] =>
    ⟨hexecution.1, Nat.le_trans hexecution.2 hbudget⟩

end SequentialExecution

section TotalWpReplay

variable {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) replayTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

local instance (priority := high) replayTerminalIrisGS :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      replayTerminalLanguage (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }

variable {s : Stuckness} {E : CoPset}
variable {post : Terminal → IProp (WasmHeapGF α)}

/-- Forward replay of an existing total WP along one actual Wasm step. This
uses the supplied initial physical state and produces its actual successor.
The direction from a fixed-store execution to a total WP is not provided. -/
theorem twp_replay_step {initial final : Config α} {kind : StepKind}
    (execution : Step initial kind final)
    (ns : Nat) (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ={E}=∗
      stateInterp (GF := WasmHeapGF α) final.store (ns + 1) observations threads ∗
        WP final.expr @ s; E [{ post }] := by
  have hprim : (initial.expr, initial.store) -<([] : List StepKind)>->
      (final.expr, final.store, ([] : List (Expr α))) :=
    ⟨rfl, kind, rfl, execution⟩
  have hnone := Language.val_stuck hprim
  iintro ⟨Hstate, Hwp⟩
  ihave Hpre := twp.unfold.mp $$ Hwp
  isimp only [twp.pre, hnone] at Hpre
  imod Hpre $$ %initial.store %ns %observations %threads Hstate with ⟨_, Hnext⟩
  imod Hnext $$ %([] : List StepKind) %final.expr %final.store
      %([] : List (Expr α)) %hprim with
    ⟨_, Hstate, Hwp, _⟩
  imodintro
  isimp only [List.length_nil, Nat.add_zero] at Hstate
  iframe

/-- Reuse a total-WP proof along a supplied finite authoritative trace. At a
running endpoint this returns its residual total WP, not resources hidden in
the terminal postcondition. -/
theorem twp_replay_steps {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final)
    (ns : Nat) (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ={E}=∗
      stateInterp (GF := WasmHeapGF α) final.store (ns + trace.length) observations threads ∗
        WP final.expr @ s; E [{ post }] := by
  induction execution generalizing ns with
  | refl =>
      iintro H
      imodintro
      iexact H
  | cons head tail ih =>
      iintro H
      imod twp_replay_step head ns observations threads $$ H with H
      imod ih (ns + 1) $$ H with H
      imodintro
      isimp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] at H
      iexact H

/-- At a genuine value endpoint, forward replay exposes the original total
WP's client postcondition and retains the interpretation of the actual final
store. No normalization or endpoint-value assumption is synthesized. -/
theorem twp_replay_value {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final) (value : Terminal)
    (hvalue : Language.IntoVal final.expr value)
    (ns : Nat) (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ={E}=∗
      stateInterp (GF := WasmHeapGF α) final.store (ns + trace.length) observations threads ∗
        post value := by
  iintro H
  imod twp_replay_steps execution ns observations threads $$ H with ⟨Hstate, Hwp⟩
  imod (twp.value_fupd hvalue).mp $$ Hwp with Hpost
  imodintro
  iframe

/-- Existing total WP supplies the resource evolution along an independently
proved trace. The sequential certificate retains a residual WP when the
endpoint is running. In particular, this is a forward adapter, not a rule
turning a fixed-state certificate into an ordinary WP. -/
theorem SequentialExecution.of_twp_steps
    {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final) (budget : Nat)
    (bound : trace.length ≤ budget)
    (ns : Nat) (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) initial.store ns observations threads ∗
      WP initial.expr @ s; E [{ post }] ={E}=∗
      SequentialExecution initial ns observations threads budget
        (fun reached => iprop(⌜reached = final⌝ ∗ WP reached.expr @ s; E [{ post }])) := by
  iintro H
  imod twp_replay_steps execution ns observations threads $$ H with ⟨Hstate, Hwp⟩
  imodintro
  iapply SequentialExecution.of_steps ns observations threads budget _ execution bound
  iframe_pureexact using [Hstate Hwp] => rfl

end TotalWpReplay

end Wasm.SmallStep
