import Project.SwapElements.SwapSepLogic
import Project.SwapElementsOpt3.SmallStepEquivalence

/-!
# Equivalence of the two `swap_elements` builds (`opt-level = 0` vs `opt-level = 3`)

Small-step port of the big-step equivalence between the two builds of
`arr.swap(i, j)`: `mod0` (shadow stack + scratch slot, export at func 4) and
`mod3` (fully inlined, export at func 0), stated as
`SmallStep.ObservationallyEquivOn` over the authoritative machine.

The observation is the caller-visible slice, `Mem.words64` over the `len`
elements at `ptr`. The two builds therefore agree on every element, not only
the swapped pair. The opt0 build's private scratch and spill cells are outside
the observation; its side keeps ownership of them and of global 0 as
hypotheses, as in `SwapSepLogic.func4_store_terminatesWith_array`.
-/

namespace Project.SwapElementsOpt3.Equivalence

open Iris Iris.BI
open Wasm Wasm.SepLogic

/-- **Program equivalence of the two `swap_elements` builds**, observed as the
whole caller slice `store.wasm.mem.words64 ptr xs.length`. -/
def SwapOptEquiv : Prop :=
  ∀ (wasm : Store Unit) (ptr len i j : UInt32)
    (xs : List UInt64)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value),
    xs.length = len.toNat →
    i < len → j < len →
    ptr.toNat + 8 * xs.length < UInt32.size →
    ptr.toNat + 8 * xs.length ≤ wasm.mem.pages * 65536 →
    heapAgreesWithMem σ
      (Wasm.SmallStep.storeResolve
        (SmallStepEquivalence.opt3ConfigFromStore wasm ptr len i j).store) →
    heapAddressesInBounds σ
      (Wasm.SmallStep.storeResolve
        (SmallStepEquivalence.opt3ConfigFromStore wasm ptr len i j).store) →
    globalHeapAgrees globalσ wasm.globals →
    (∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      array64At 0 ptr xs) →
    (∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) →
    SmallStep.ObservationallyEquivOn
      (Project.SwapElements.SwapSepLogic.func4ConfigFromStore wasm ptr len i j)
      (SmallStepEquivalence.opt3ConfigFromStore wasm ptr len i j)
      (fun store => store.wasm.mem.words64 ptr xs.length)

theorem swap_opt_equiv : SwapOptEquiv := by
  intro wasm ptr len i j xs oldSpillPtr oldSpillLen oldScratch σ globalσ
    hlen hi hj hroom hbound hagree hinBounds hglobals hresources hglobalOwn
  have hresources' : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      array64At 0 ptr xs :=
    fun [WasmHeapGS Unit] => hresources.trans (by iintro ⟨_, _, _, HA⟩; iexact HA)
  apply SmallStep.ObservationallyEquivOn.of_common_outcome
    (o := (xs.set i.toNat (xs.getD j.toNat 0)).set j.toNat (xs.getD i.toNat 0))
  · refine (Project.SwapElements.SwapSepLogic.func4_store_terminatesWith_array
      wasm ptr len i j xs oldSpillPtr oldSpillLen oldScratch σ globalσ
      hlen hi hj hroom hagree hinBounds hglobals hresources hglobalOwn).mono ?_
    rintro values store ⟨hv, h⟩
    exact ⟨hv, by rw [Mem.readWords64_eq_words64] at h; exact h⟩
  · refine (SmallStepEquivalence.opt3_func0_store_terminatesWith_array
      wasm ptr len i j xs σ globalσ hlen hi hj hroom hbound
      hagree hinBounds hglobals hresources').mono ?_
    rintro values store ⟨hv, h⟩
    exact ⟨hv, by rw [Mem.readWords64_eq_words64] at h; exact h⟩

end Project.SwapElementsOpt3.Equivalence
