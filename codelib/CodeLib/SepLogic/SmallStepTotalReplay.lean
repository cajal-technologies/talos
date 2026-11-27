import CodeLib.SepLogic.SmallStepTotalLifting

/-! # Total-WP replay at finite execution prefixes -/

namespace Wasm.SmallStep

open Wasm.SepLogic Iris Iris.ProgramLogic Language.Notation

variable {α : Type}
variable [WasmSmallStepGS hlc α]

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

end Wasm.SmallStep
