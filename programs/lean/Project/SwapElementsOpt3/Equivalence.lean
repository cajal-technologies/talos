import Project.SwapElements.SmallStepSpec
import Project.SwapElementsOpt3.SmallStepEquivalence

/-!
# Equivalence of the two `swap_elements` builds (`opt-level = 0` vs `opt-level = 3`)

Small-step port of the big-step equivalence between the two builds of
`arr.swap(i, j)`: `mod0` (shadow stack + scratch slot, export at func 4) and
`mod3` (fully inlined, export at func 0), stated as
`SmallStep.ObservationallyEquivOn` over the authoritative machine.

## What is observed — and a known weakening relative to the big-step theorem

The observation here is the pair of **swapped elements only**:

    fun store => (store.wasm.mem.read64 (elemAddr ptr i),
                  store.wasm.mem.read64 (elemAddr ptr j))

(with `elemAddr ptr k = (k <<< 3) + ptr`), plus the returned values and
co-termination that `ObservationallyEquivOn` builds in.

The big-step theorem this file replaces observed strictly more: the **whole
caller array plus host state**, `fun st => (st.host, st.mem.words64 ptr
len.toNat)` — i.e. it additionally guaranteed the two builds agree on every
*untouched* element `k ∉ {i, j}`. That whole-array observation has **not**
yet been restored in the small-step port. The reason is structural: the
small-step contracts this proof composes
(`Project.SwapElements.SmallStepSpec.swap_elements_distinct_terminates_correct`
and `SmallStepEquivalence.opt3_func0_distinct_store_terminatesWith`)
characterize only the two swapped words in the terminal store. Extending them
to the whole array requires re-deriving both builds' store-level adequacy
theorems with a parametric per-element `pointsTo_u64` footprint for the
unswapped words (framed through the TWP proofs) plus a `Mem.words64`
reconstruction of the terminal memory from those per-word facts. Until that
is done, this equivalence says nothing about elements other than `i` and `j`;
the host state is `Unit` here, so its agreement is trivial as well.

This gap is tracked in `programs/lean/M8_MIGRATION_LEDGER.md` (Deferred).
-/

namespace Project.SwapElementsOpt3.Equivalence

open Iris Iris.BI
open Wasm Wasm.SepLogic

/-- **Program equivalence of the two `swap_elements` builds**, observed at the
two swapped elements. NOTE: this is deliberately documented as weaker than the
retired big-step theorem, which observed the whole caller array
(`Mem.words64 ptr len.toNat`); see the module docstring for what would be
needed to restore that. -/
def SwapOptEquiv : Prop :=
  ∀ (wasm : Store Unit) (ptr len i j : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value),
    i < len → j < len →
    ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536 →
    ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536 →
    wasm.mem.pages ≤ 65536 →
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
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB) →
    (∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) →
    SmallStep.ObservationallyEquivOn
      (Project.SwapElements.SwapSepLogic.func4ConfigFromStore wasm ptr len i j)
      (SmallStepEquivalence.opt3ConfigFromStore wasm ptr len i j)
      (fun store =>
        (store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr),
         store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr)))

theorem swap_opt_equiv : SwapOptEquiv := by
  intro wasm ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
    σ globalσ hi hj hboundI hboundJ hpages hagree hinBounds hglobals
    hresources hglobalOwn
  have hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hresources' : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB :=
    fun [WasmHeapGS Unit] => hresources.trans (by iintro ⟨_, _, _, HA, HB⟩; iframe)
  apply SmallStep.ObservationallyEquivOn.of_common_outcome (o := (oldB, oldA))
  · refine (Project.SwapElements.SmallStepSpec.swap_elements_distinct_terminates_correct
      wasm ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
      σ globalσ hi hj hroomI hroomJ hagree hinBounds hglobals
      hresources hglobalOwn).mono ?_
    rintro values store ⟨hv, hA, hB⟩
    exact ⟨hv, Prod.ext hA hB⟩
  · refine (SmallStepEquivalence.opt3_func0_distinct_store_terminatesWith
      wasm ptr len i j oldA oldB σ globalσ hi hj hboundI hboundJ hroomI hroomJ
      hagree hinBounds hglobals hresources').mono ?_
    rintro values store ⟨hv, hA, hB⟩
    exact ⟨hv, Prod.ext hA hB⟩

end Project.SwapElementsOpt3.Equivalence
