import Mathlib
import CodeLib
import HexEncodeStdio.Grow

namespace Submission.TotalGrow

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

/-- Total-WP counterpart of `Submission.Grow.wp_memoryGrow_owned`.  It splits
the concrete allocator outcome and exposes ownership of the newly addressable
range on success. -/
theorem twp_memoryGrow_owned {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (hbound : ∀ (store : MachineStore α) (memory : Mem)
        (previousPages : Nat),
      store.wasm.mem.grow delta
          (store.wasm.memoryCap store.runtime.currentModule 0) =
        some (memory, previousPages) →
      (previousPages + delta.toNat) * 65536 < UInt32.size)
    (Hfail : runtimeModuleOwn instanceId runtimeModule -∗
      heapFrontierOwn UInt32.size -∗
      WP (.running ⟨⟨params, localValues,
          .i32 (0xFFFFFFFF : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }])
    (Hsuccess : ∀ (memory : Mem) (previousPages : Nat),
      pointsToBytes 0 (UInt32.ofNat (previousPages * 65536))
          (Submission.Grow.bytesAt memory
            (UInt32.ofNat (previousPages * 65536)) (delta.toNat * 65536)) -∗
      runtimeModuleOwn instanceId runtimeModule -∗
      heapFrontierOwn UInt32.size -∗
      WP (.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule -∗
    heapFrontierOwn UInt32.size -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hruntime HheapFrontierOwn
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 (0xFFFFFFFF : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩, store, [],
        ⟨rfl, .instruction .memoryGrow, rfl, Step.memoryGrowFailure hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ :=
      step_deterministic (Step.memoryGrowFailure hg) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod Hclose
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · iapply Hfail $$ Hruntime HheapFrontierOwn
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem := memory } }, [],
        ⟨rfl, .instruction .memoryGrow, rfl, by
          simpa only [Wasm.SmallStep.setMemory_eq] using
            Step.memoryGrowSuccess hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    have expectedStep : Step
        ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ := by
      simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg
    obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod Hclose
    icombine Hσ HheapFrontierOwn as Hinput
    imod Submission.Grow.stateInterp_memoryGrow_owned store ns obs nt delta
      (store.wasm.memoryCap store.runtime.currentModule 0)
      memory previousPages hg (hbound store memory previousPages hg) $$ Hinput with
      ⟨Hσ, Hnew, HheapFrontierOwn⟩
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · iapply Hsuccess memory previousPages $$ Hnew Hruntime HheapFrontierOwn

end Submission.TotalGrow
