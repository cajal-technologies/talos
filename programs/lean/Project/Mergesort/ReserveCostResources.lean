import Project.Mergesort.ReserveCost

/-! # Physical postconditions of the actual reserve execution

The metadata facts refer to the concrete returned store, including the cursor
commit, old-allocation copy, grow-result writes and vector-header replacement.
-/

namespace Project.Mergesort.ReserveCostResources

open Wasm Wasm.SmallStep Project.Mergesort.Representations
open Project.Mergesort.ReserveCost

private theorem copy_read32_before (memory : Mem) (destination source count : Nat)
    (address : UInt32) (h : address.toNat+4≤destination) :
    (memory.copy destination source count).read32 address=memory.read32 address := by
  have h0 : ¬ destination≤address.toNat := by omega
  have h1 : ¬ destination≤address.toNat+1 := by omega
  have h2 : ¬ destination≤address.toNat+2 := by omega
  have h3 : ¬ destination≤address.toNat+3 := by omega
  simp [Mem.read32,Mem.copy,h0,h1,h2,h3]

/-- All non-memory fields, including physical global aliases, are retained. -/
theorem finalStore_frame (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish : UInt32) :
    let result := finalStore store oldCapacity oldPtr newCapacity base finish
    result.runtime=store.runtime ∧ result.wasm.globals=store.wasm.globals ∧
    result.wasm.globalIds=store.wasm.globalIds ∧ result.wasm.host=store.wasm.host ∧
    result.wasm.memoryCaps=store.wasm.memoryCaps ∧ result.wasm.memoryIds=store.wasm.memoryIds := by
  unfold finalStore growFinalStore growResultStore allocationStore
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Reserve reaches exactly the pages selected by the physical allocator. -/
theorem finalStore_pages (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish : UInt32) :
    (finalStore store oldCapacity oldPtr newCapacity base finish).wasm.mem.pages=
      max store.wasm.mem.pages (allocatorRequiredPages finish).toNat := by
  unfold finalStore growFinalStore growResultStore allocationStore
  split <;> rfl

theorem finalStore_pointer (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish : UInt32) :
    (finalStore store oldCapacity oldPtr newCapacity base finish).wasm.mem.read32
      (driverBase+4)=base := Mem.read32_write32_same _ _ _

theorem finalStore_capacity (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish : UInt32) :
    (finalStore store oldCapacity oldPtr newCapacity base finish).wasm.mem.read32
      driverBase=newCapacity := by
  unfold finalStore
  rw [Mem.read32_write32_disjoint _ _ _ _ (by decide :
    driverBase.toNat+4≤(driverBase+4).toNat ∨ (driverBase+4).toNat+4≤driverBase.toNat)]
  exact Mem.read32_write32_same _ _ _

/-- The actual cursor survives the old-allocation copy and all result/header
writes. The classifier's freshness fact provides the separation premise. -/
theorem finalStore_cursor (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish : UInt32)
    (hbase : allocatorCursor.toNat+4≤base.toNat) :
    (finalStore store oldCapacity oldPtr newCapacity base finish).wasm.mem.read32
      allocatorCursor=finish := by
  unfold finalStore growFinalStore growResultStore
  repeat rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)]
  unfold allocationStore
  split
  · exact AllocatorExecution.finalStore_cursor _ _
  · exact ReallocatorExecution.finalStore_cursor _ _ _ _ _ hbase

/-- The length word and each word of the stack read buffer lie in this
unchanged interval above the two replaced header fields and below the cursor. -/
theorem finalStore_stack_word (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish address : UInt32)
    (hbase : allocatorCursor.toNat+4≤base.toNat)
    (hlow : (driverBase+8).toNat≤address.toNat)
    (hhigh : address.toNat+4≤allocatorCursor.toNat) :
    (finalStore store oldCapacity oldPtr newCapacity base finish).wasm.mem.read32 address=
      store.wasm.mem.read32 address := by
  have hheader : (driverBase+4).toNat+4≤address.toNat := hlow
  have hfirst : driverBase.toNat+4≤address.toNat := by
    have : driverBase.toNat+4≤(driverBase+8).toNat := by decide
    omega
  have hresult0 : (reserveBase+4).toNat+4≤address.toNat := by
    have : (reserveBase+4).toNat+4≤(driverBase+8).toNat := by decide
    omega
  have hresult4 : ((reserveBase+4)+4).toNat+4≤address.toNat := by
    have : ((reserveBase+4)+4).toNat+4≤(driverBase+8).toNat := by decide
    omega
  have hresult8 : ((reserveBase+4)+8).toNat+4≤address.toNat := by
    have : ((reserveBase+4)+8).toNat+4≤(driverBase+8).toNat := by decide
    omega
  unfold finalStore growFinalStore growResultStore
  rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inr hheader),
    Mem.read32_write32_disjoint _ _ _ _ (Or.inr hfirst),
    Mem.read32_write32_disjoint _ _ _ _ (Or.inr hresult0),
    Mem.read32_write32_disjoint _ _ _ _ (Or.inr hresult8),
    Mem.read32_write32_disjoint _ _ _ _ (Or.inr hresult4)]
  unfold allocationStore
  split
  · unfold AllocatorExecution.finalStore
    rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl hhigh)]
    rfl
  · unfold ReallocatorExecution.finalStore
    rw [copy_read32_before _ _ _ _ _ (by omega),
      Mem.read32_write32_disjoint _ _ _ _ (Or.inl hhigh)]
    rfl

theorem finalStore_length (store : MachineStore α)
    (oldCapacity oldPtr newCapacity base finish : UInt32)
    (hbase : allocatorCursor.toNat+4≤base.toNat) :
    (finalStore store oldCapacity oldPtr newCapacity base finish).wasm.mem.read32 (driverBase+8)=
      store.wasm.mem.read32 (driverBase+8) :=
  finalStore_stack_word _ _ _ _ _ _ _ hbase (by rfl) (by decide)

end Project.Mergesort.ReserveCostResources
