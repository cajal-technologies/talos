import Project.Mergesort.Adequacy
import Project.Mergesort.BoundedDriverFacts

/-!
# Physical allocation frontier at every driver outcome

The cursor word in the actual terminal memory is bounded by the retained
allocation lineage. This is an allocation-frontier bound, not a bound on
physical pages and not an exclusion of the driver's OOM alternative.
-/

namespace Project.Mergesort.AllocationBound

open Wasm Wasm.SmallStep Wasm.SepLogic Iris Iris.ProgramLogic
open Project.Mergesort.Representations Project.Mergesort.Adequacy
open Project.Mergesort.MemoryBounds

/-- Interpret the allocator's zero sentinel in the actual physical memory. -/
def allocationFrontier (store : MachineStore Universal.State) : Nat :=
  let cursor := store.wasm.mem.read32 allocatorCursor
  if cursor = 0 then heapBase.toNat else cursor.toNat

/-- For a nonempty word input, the retained bound is linear in word count. -/
theorem workArraysFrontierBound_words (input : List UInt32) (h : 0 < input.length) :
    workArraysFrontierBound (serialize input).length =
      heapBase.toNat + 24 * input.length + 6 := by
  rw [serialize_length]
  unfold workArraysFrontierBound inputFrontierBound
  rw [max_eq_left (by omega : 8 ≤ 2 * (4 * input.length))]
  omega

theorem BumpHeap_physical_frontier [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (store : MachineStore Universal.State)
    (observations : List StepKind) :
    BumpHeap heapId storedCursor frontier history -∗
      stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜allocationFrontier store = frontier⌝ := by
  iintro Hbump Hstate
  iunfold BumpHeap at Hbump
  icases Hbump with
    ⟨Hcursor, _Hfrontier, _Hmetadata, _Hretired, %pages, _Hpages, %hfacts⟩
  imod stateInterp_pointsTo_u32_facts store 0 observations 0
    allocatorCursor storedCursor (by decide) (by decide) (by decide) $$
      [$Hstate $Hcursor] with %hread
  ipureintro
  unfold allocationFrontier
  rw [hread.1]
  by_cases hz : storedCursor = 0
  · rw [if_pos hz]
    exact ((hfacts.2.2.1.mp hz).2).symm
  · rw [if_neg hz]
    exact hfacts.2.2.2.1 hz

theorem DriverSuccess_frontier [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32)
    (store : MachineStore Universal.State) (observations : List StepKind) :
    DriverSuccess heapId input -∗
      stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜allocationFrontier store ≤ workArraysFrontierBound (serialize input).length⌝ := by
  iintro Hsuccess Hstate
  iunfold DriverSuccess at Hsuccess
  icases Hsuccess with
    ⟨%sorted, %stackBytes, %storedCursor, %frontier, %history,
      %hfacts, _Hsp, _Hstack, Hbump, _Hstreams⟩
  ihave %hfrontier := BumpHeap_physical_frontier heapId storedCursor frontier
    history store observations $$ Hbump Hstate
  ipureexact (by rw [hfrontier]; exact hfacts.2.2.2)

theorem DriverOOM_frontier [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32)
    (store : MachineStore Universal.State) (observations : List StepKind) :
    (∃ phase : DriverOOMPhase, DriverOOMState heapId input phase) -∗
      stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜allocationFrontier store ≤ workArraysFrontierBound (serialize input).length⌝ := by
  iintro ⟨%phase, Hoom⟩ Hstate
  cases phase with
  | reserve =>
      iunfold DriverOOMState at Hoom
      iunfold DriverReserveOOM at Hoom
      icases Hoom with
        ⟨%capacity, %ptr, %appended, %current, %remaining, %chunkTail,
          %outputBytes, %shadow, %storedCursor, %frontier, %history,
          %hfacts, _Hsp, _Hreserve, _Hframe, Hbump, _Hstreams⟩
      ihave %hfrontier := BumpHeap_physical_frontier heapId storedCursor frontier
        history store observations $$ Hbump Hstate
      ipureintro
      have hbound := BoundedGeometricVecFacts.frontier_le _ _ _ _ _ _ _
        hfacts.2.2.2.2.2.2
      rw [hfrontier]
      unfold workArraysFrontierBound
      omega
  | values =>
      iunfold DriverOOMState at Hoom
      iunfold DriverValuesOOM at Hoom
      icases Hoom with
        ⟨%capacity, %ptr, %chunkBytes, %outputBytes, %shadow,
          %storedCursor, %frontier, %history, %hfacts,
          _Hsp, _Hreserve, _Hframe, Hbump, _Hstreams⟩
      ihave %hfrontier := BumpHeap_physical_frontier heapId storedCursor frontier
        history store observations $$ Hbump Hstate
      ipureintro
      have hbound := BoundedGeometricVecFacts.frontier_le _ _ _ _ _ _ _ hfacts.2
      rw [hfrontier]
      unfold workArraysFrontierBound
      omega
  | scratch =>
      iunfold DriverOOMState at Hoom
      iunfold DriverScratchOOM at Hoom
      icases Hoom with
        ⟨%capacity, %ptr, %valuesPtr, %valuesId, %chunkBytes,
          %outputBytes, %shadow, %storedCursor, %frontier, %history,
          %hfacts, _Hsp, _Hreserve, _Hframe, _Hvalues, Hbump, _Hstreams⟩
      ihave %hfrontier := BumpHeap_physical_frontier heapId storedCursor frontier
        history store observations $$ Hbump Hstate
      ipureexact (by rw [hfrontier]; exact BoundedDriverFacts.ScratchLineage.frontier_le hfacts.2)

def boundedEntryPost (input : List UInt32) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  entryPost input outcome store ∧
    allocationFrontier store ≤ workArraysFrontierBound (serialize input).length

theorem DriverSuccess_public_bound [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32) :
    DriverSuccess heapId input -∗
      ∀ (store : MachineStore Universal.State) (observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
        ⌜boundedEntryPost input (.done []) store⌝ := by
  iintro Hsuccess %store %observations Hstate
  ihave %hbound :
      ⌜allocationFrontier store ≤ workArraysFrontierBound (serialize input).length⌝ $$
      [Hsuccess Hstate]
  · iapply DriverSuccess_frontier heapId input store observations $$ Hsuccess Hstate
  ihave Hpost := DriverSuccess_public heapId input $$ Hsuccess
  ihave %hpost := Hpost $$ %store %observations Hstate
  ipureexact ⟨hpost, hbound⟩

theorem DriverOOM_public_bound [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32) :
    (∃ phase : DriverOOMPhase, DriverOOMState heapId input phase) -∗
      ∀ (store : MachineStore Universal.State) (observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
        ⌜boundedEntryPost input (.trapped (.host OOM.trapMessage)) store⌝ := by
  iintro Hoom %store %observations Hstate
  ihave %hbound :
      ⌜allocationFrontier store ≤ workArraysFrontierBound (serialize input).length⌝ $$
      [Hoom Hstate]
  · iapply DriverOOM_frontier heapId input store observations $$ Hoom Hstate
  ihave Hpost := DriverOOM_public heapId input $$ Hoom
  ihave %hpost := Hpost $$ %store %observations Hstate
  ipureexact ⟨hpost, hbound⟩

end Project.Mergesort.AllocationBound
