import Project.SwapElements.SwapSepLogic

/-!
# Small-step specification for `swap_elements`

This is the public migration target for the exported function.  Unlike the
legacy `Project.SwapElements.Spec`, it is stated over the authoritative
small-step machine and expresses partial correctness through iris-lean.

The footprint hypotheses expose precisely the mutable resources used by the
generated wrapper: its scratch word, two spill slots, and the two distinct
array elements.  Because the byte points-to assertions are exclusive, this
contract cannot be instantiated with overlapping element addresses.
-/

namespace Project.SwapElements.SmallStepSpec

open Iris
open Iris.BI
open Wasm
open Wasm.SepLogic

/-- Public small-step contract for the non-aliasing case of the generated
`swap_elements` export.  The conclusion describes the physical memory in every
successfully reached terminal store; it is not merely a ghost-state result. -/
@[spec_of "rust-exported-small-step" "swap_elements::swap_elements"]
def SwapElementsDistinctSpec : Prop :=
  ∀ (wasm : Store Unit) (ptr len i j : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value),
    i < len →
    j < len →
    ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 →
    ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 →
    heapAgreesWithMem σ wasm.mem →
    heapAddressesInBounds σ wasm.mem →
    globalHeapAgrees globalσ wasm.globals →
    (∀ [WasmHeapGS],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB) →
    (∀ [WasmGlobalGS],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576)) →
    Wasm.SmallStep.PartiallyMeets
      (SwapSepLogic.func4ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldB ∧
          store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr) = oldA)

@[proves SwapElementsDistinctSpec]
theorem swap_elements_distinct_correct : SwapElementsDistinctSpec := by
  intro wasm ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
    σ globalσ hi hj hroomI hroomJ hagree hinBounds hglobals
    hresources hglobalOwn
  exact SwapSepLogic.func4_distinct_store_partiallyMeets
    wasm ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
    σ globalσ hi hj hroomI hroomJ hagree hinBounds hglobals
    hresources hglobalOwn

/-- Public small-step contract for equal indices.  It deliberately asks for
one array-word owner, so it remains usable with exclusive byte ownership. -/
@[spec_of "rust-exported-small-step" "swap_elements::swap_elements_alias"]
def SwapElementsAliasSpec : Prop :=
  ∀ (wasm : Store Unit) (ptr len i : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value),
    i < len →
    ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 →
    heapAgreesWithMem σ wasm.mem →
    heapAddressesInBounds σ wasm.mem →
    globalHeapAgrees globalσ wasm.globals →
    (∀ [WasmHeapGS],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue) →
    (∀ [WasmGlobalGS],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576)) →
    Wasm.SmallStep.PartiallyMeets
      (SwapSepLogic.func4ConfigFromStore wasm ptr len i i)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldValue)

@[proves SwapElementsAliasSpec]
theorem swap_elements_alias_correct : SwapElementsAliasSpec := by
  intro wasm ptr len i oldSpillPtr oldSpillLen oldScratch oldValue
    σ globalσ hi hroom hagree hinBounds hglobals hresources hglobalOwn
  exact SwapSepLogic.func4_alias_store_partiallyMeets
    wasm ptr len i oldSpillPtr oldSpillLen oldScratch oldValue
    σ globalσ hi hroom hagree hinBounds hglobals hresources hglobalOwn

end Project.SwapElements.SmallStepSpec
