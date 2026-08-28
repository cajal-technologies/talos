import Mathlib
import CodeLib

namespace Submission.TotalHelpers

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

/-- Total zero-offset byte store rule. -/
theorem twp_store8_zero {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {address value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldByte : UInt8) :
    (⟨0, address⟩ ↦w oldByte) -∗
    ((⟨0, address⟩ ↦w value.toUInt8) -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
      .store8 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] := by
  iintro Hpt Hnext
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %HinBounds :
      ⌜address.toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_inBounds store ns obs nt address oldByte
        $$ [$Hσ $Hpt] with %HinBounds
    ipureintro
    exact HinBounds
  have hbound : address.toNat + (0 : UInt32).toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    norm_num
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 address value.toUInt8 } },
      [], ⟨rfl, .instruction (.store8 0), rfl,
        by simpa only [UInt32.add_zero, Wasm.SmallStep.setMemory_eq] using
          (Step.store8 (α := α) (value := value) hbound)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store8 0 :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store8 0))
      ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write8 address value.toUInt8 } }⟩ :=
    by simpa only [UInt32.add_zero, Wasm.SmallStep.setMemory_eq] using
      (Step.store8 (α := α) (value := value) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_store8 store ns obs nt address oldByte value.toUInt8
      HinBounds $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  imodintro
  isplit
  · itrivial
  isplit
  · itrivial
  isplitl [Hσ]
  · iexact Hσ
  · iapply Hnext
    iexact Hpt

end Submission.TotalHelpers
