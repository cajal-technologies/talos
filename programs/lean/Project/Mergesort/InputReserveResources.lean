import Project.Mergesort.InputLoopCost
import Project.Mergesort.ReserveCostResources

/-! # Preservation through reserve, append and the next actual input read -/

namespace Project.Mergesort.InputReserveResources

open Wasm Wasm.SmallStep Project.Mergesort.Representations
open Project.Mergesort.InputCost Project.Mergesort.InputControlCost
open Project.Mergesort.InputLoopCost Project.Mergesort.MemoryBounds

def reservedState (v : State) (base finish : UInt32) (nextHistory : AllocationHistory) : State :=
  { v with
    capacity := UInt32.ofNat (selectedCapacity v.length v.current v.capacity.toNat)
    dataPtr := base
    storedCursor := finish
    frontier := finish.toNat
    history := nextHistory }

def reservedStore (store : MachineStore Universal.State) (v : State) (base finish : UInt32) :
    MachineStore Universal.State :=
  ReserveCost.finalStore store v.capacity v.dataPtr
    (UInt32.ofNat (selectedCapacity v.length v.current v.capacity.toNat)) base finish

/-- The next loop state preserves the entire initial physical invariant.
Classification and the actual history update are pure local facts; neither is
an assumption of future execution. -/
theorem reserve_invariant {total : Nat} {store : MachineStore Universal.State} {v : State}
    (h : Invariant total store v) (hpositive : 0<v.current)
    (hnonfit : v.capacity.toNat<v.length+v.current)
    (base finish : UInt32) (nextHistory : AllocationHistory)
    (hclassify : classifyBump v.frontier
      { size := selectedCapacity v.length v.current v.capacity.toNat,alignment := 1 }=
      .success base finish)
    (hhistory : VecReserveHistory v.history nextHistory v.capacity v.dataPtr base
      { size := selectedCapacity v.length v.current v.capacity.toNat,alignment := 1 }) :
    let grown := reservedStore store v base finish
    let next := reservedState v base finish nextHistory
    Invariant total (fittingStore grown next) (fittingState grown next) ∧
      2*v.capacity.toNat≤next.capacity.toNat ∧
      store.wasm.mem.pages≤(fittingStore grown next).wasm.mem.pages := by
  intro grown next
  let selected := selectedCapacity v.length v.current v.capacity.toNat
  have hfresh := DriverProof.geometricVec_frontier_ge_heapBase _ _ _ _ _ _ _ h.lineage
  obtain ⟨_hfrontierWord,_hbase,hbaseNat,hendWord,hendSigned,hfinish⟩ :=
    classifyBump_success_align1 v.frontier selected base finish hclassify
  have hselectedWord : selected<UInt32.size := by omega
  have hselectedNat : next.capacity.toNat=selected := UInt32.toNat_ofNat_of_lt' hselectedWord
  have hlength : v.length+v.current≤selected := by unfold selected selectedCapacity; omega
  have hdoubled : 2*v.capacity.toNat≤selected := by unfold selected selectedCapacity; omega
  have hfinishSigned : finish.toNat<2147483648 := by omega
  have hfinishPositive : 0<finish.toNat := by
    have : 0<heapBase.toNat := by decide
    omega
  have hfinishNonnull : finish≠0 := by
    intro hz
    have : finish.toNat=0 := by rw [hz]; rfl
    omega
  have hbase : allocatorCursor.toNat+4≤base.toNat := by
    have : allocatorCursor.toNat+4≤heapBase.toNat := by decide
    omega
  have hpages : grown.wasm.mem.pages=max store.wasm.mem.pages (allocatorRequiredPages finish).toNat :=
    ReserveCostResources.finalStore_pages _ _ _ _ _ _
  have hgrow : store.wasm.mem.pages≤grown.wasm.mem.pages := by rw [hpages]; exact Nat.le_max_left _ _
  have hframe := ReserveCostResources.finalStore_frame store v.capacity v.dataPtr
    (UInt32.ofNat selected) base finish
  have hruntime : grown.runtime=store.runtime := hframe.1
  have hhostState : grown.wasm.host=store.wasm.host := hframe.2.2.2.1
  have hglobals : globalAt? grown 0=globalAt? store 0 := by
    unfold grown reservedStore ReserveCost.finalStore ReserveCost.growFinalStore
      ReserveCost.growResultStore ReserveCost.allocationStore
    split <;> rfl
  have hcap : grown.wasm.memoryCap grown.runtime.currentModule 0=Module.memoryHardCap := by
    unfold grown reservedStore ReserveCost.finalStore ReserveCost.growFinalStore
      ReserveCost.growResultStore ReserveCost.allocationStore
    split <;> exact h.cap
  have hword : base.toNat+v.length<UInt32.size := by omega
  have haddress := byteOffset_toNat base v.length hword
  have hheap : heapBase.toNat≤(next.dataPtr+UInt32.ofNat next.length).toNat := by
    change heapBase.toNat≤(base+UInt32.ofNat v.length).toNat
    rw [haddress]; omega
  have hheaderCap : (fittingStore grown next).wasm.mem.read32 driverBase=next.capacity := by
    rw [fittingStore_metadata grown next driverBase
      (le_trans (by decide : driverBase.toNat+4≤heapBase.toNat) hheap) (by decide) (by decide)]
    exact ReserveCostResources.finalStore_capacity _ _ _ _ _ _
  have hheaderPtr : (fittingStore grown next).wasm.mem.read32 (driverBase+4)=next.dataPtr := by
    rw [fittingStore_metadata grown next (driverBase+4)
      (le_trans (by decide : (driverBase+4).toNat+4≤heapBase.toNat) hheap) (by decide) (by decide)]
    exact ReserveCostResources.finalStore_pointer _ _ _ _ _ _
  have hheaderLength : (fittingStore grown next).wasm.mem.read32 (driverBase+8)=
      UInt32.ofNat (v.length+v.current) := by
    unfold fittingStore
    rw [readResult_metadata _ _ _ _ (Or.inl (by decide))]
    exact appendedStore_length _ _ _ _
  have hcursor : (fittingStore grown next).wasm.mem.read32 allocatorCursor=finish := by
    rw [fittingStore_metadata grown next allocatorCursor
      (le_trans (by decide : allocatorCursor.toNat+4≤heapBase.toNat) hheap) (by decide) (by decide)]
    exact ReserveCostResources.finalStore_cursor _ _ _ _ _ _ hbase
  have hremaining : (fittingState grown next).current+
      (fittingStore grown next).wasm.host.stdio.input.length=store.wasm.host.stdio.input.length := by
    rw [fittingStore_input,List.length_drop]
    change readCount grown 256+(grown.wasm.host.stdio.input.length-readCount grown 256)=_
    have hc : readCount grown 256≤grown.wasm.host.stdio.input.length := min_le_right _ _
    rw [hhostState] at hc ⊢
    omega
  have hgeo := BoundedGeometricVecFacts.reserveSuccess total v.length v.current
    store.wasm.host.stdio.input.length v.capacity v.dataPtr base finish v.frontier v.history
    nextHistory h.lineage h.chunk_shape hpositive hnonfit hclassify hhistory
  refine ⟨{
    total_eq := ?_,chunk_shape := ?_,lineage := ?_,
    header_capacity := hheaderCap,header_pointer := hheaderPtr,header_length := hheaderLength,
    cursor := hcursor,effective := ?_,module := ?_,host := ?_,cap := hcap,global := ?_,
    pages_lower := ?_,pages_upper := ?_,length_capacity := ?_,allocation_frontier := ?_,
    frontier_physical := ?_,frontier_signed := hfinishSigned,heap_pointer := ?_ },
    by rw [hselectedNat];exact hdoubled,hgrow⟩
  · have ht := h.total_eq
    change total=(v.length+v.current)+_+_
    rw [Nat.add_assoc,hremaining]
    exact ht
  · rw [hremaining]
    change readCount grown 256=min 256 store.wasm.host.stdio.input.length
    unfold readCount
    rw [hhostState]
    rfl
  · change BoundedGeometricVecFacts total (v.length+v.current)
      ((fittingState grown next).current+(fittingStore grown next).wasm.host.stdio.input.length)
      next.capacity base finish.toNat nextHistory
    rw [hremaining]
    exact hgeo
  · change (if finish≠0 then finish else heapBase)=UInt32.ofNat finish.toNat
    simp [hfinishNonnull]
  · change grown.runtime.currentModule=Project.Mergesort.module
    rw [hruntime];exact h.module
  · change grown.runtime.currentHost=Universal.envFor Project.Mergesort.module
    rw [hruntime];exact h.host
  · change globalAt? grown 0=some (.i32 driverBase)
    rw [hglobals];exact h.global
  · exact h.pages_lower.trans hgrow
  · change grown.wasm.mem.pages≤Module.memoryHardCap
    rw [hpages]
    exact max_le h.pages_upper ((allocatorRequiredPages_le_signedLimit finish hfinishSigned).trans (by decide))
  · change v.length+v.current≤next.capacity.toNat
    rw [hselectedNat];exact hlength
  · change base.toNat+next.capacity.toNat≤finish.toNat
    rw [hselectedNat,hbaseNat,hfinish]
  · change finish.toNat≤grown.wasm.mem.pages*65536
    rw [hpages]
    exact (allocatorRequiredPages_covers finish hfinishSigned).trans
      (Nat.mul_le_mul_right 65536 (Nat.le_max_right _ _))
  · intro _
    change heapBase.toNat≤base.toNat
    omega

end Project.Mergesort.InputReserveResources
