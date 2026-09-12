import Project.Mergesort.InputControlCost
import Project.Mergesort.MemoryBounds

/-!
# Physical invariants for composing the generated input loop

Metadata preservation is proved against the actual byte-copy and host-read
stores. `InputExecutionCost` uses these facts to compose the complete loop
with the actual reserve execution and its numerical postconditions.
-/

namespace Project.Mergesort.InputLoopCost

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO
open Project.Mergesort.DriverProof Project.Mergesort.Representations
open Project.Mergesort.InputCost Project.Mergesort.InputControlCost

structure State where
  capacity : UInt32
  dataPtr : UInt32
  length : Nat
  current : Nat
  storedCursor : UInt32
  frontier : Nat
  history : AllocationHistory

structure Aux where
  aux2 : UInt32 := 4
  aux4 : UInt32 := 0
  aux5 : UInt32 := 0
  aux7 : UInt32 := 0
  aux8 : UInt32 := 0
  aux9 : UInt32 := 0
  aux10 : UInt32 := 0

def stateLocals (v : State) (a : Aux) : Locals :=
  func3AppendLocals v.dataPtr (UInt32.ofNat v.current) (UInt32.ofNat v.length)
    a.aux2 a.aux4 a.aux5 a.aux7 a.aux8 a.aux9 a.aux10 []

/-- Concrete facts at an input-loop head, or after its final EOF transition.
No future execution or numerical certificate is part of this invariant. -/
structure Invariant (total : Nat) (store : MachineStore Universal.State) (v : State) : Prop where
  total_eq : total = v.length + v.current + store.wasm.host.stdio.input.length
  chunk_shape : v.current = min 256 (v.current + store.wasm.host.stdio.input.length)
  lineage : BoundedGeometricVecFacts total v.length
    (v.current + store.wasm.host.stdio.input.length) v.capacity v.dataPtr v.frontier v.history
  header_capacity : store.wasm.mem.read32 driverBase = v.capacity
  header_pointer : store.wasm.mem.read32 (driverBase + 4) = v.dataPtr
  header_length : store.wasm.mem.read32 (driverBase + 8) = UInt32.ofNat v.length
  cursor : store.wasm.mem.read32 allocatorCursor = v.storedCursor
  effective : (if v.storedCursor ≠ 0 then v.storedCursor else heapBase) = UInt32.ofNat v.frontier
  module : store.runtime.currentModule = Project.Mergesort.module
  host : store.runtime.currentHost = Universal.envFor Project.Mergesort.module
  cap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap
  global : globalAt? store 0 = some (.i32 driverBase)
  pages_lower : 17 ≤ store.wasm.mem.pages
  pages_upper : store.wasm.mem.pages ≤ Module.memoryHardCap
  length_capacity : v.length ≤ v.capacity.toNat
  allocation_frontier : v.dataPtr.toNat + v.capacity.toNat ≤ v.frontier
  frontier_physical : v.frontier ≤ store.wasm.mem.pages * 65536
  frontier_signed : v.frontier < 2147483648
  heap_pointer : v.capacity ≠ 0 → heapBase.toNat ≤ v.dataPtr.toNat

def fittingStore (store : MachineStore Universal.State) (v : State) : MachineStore Universal.State :=
  readResult (appendedStore store v.dataPtr v.length v.current) 256 (driverBase + 12)

def fittingState (store : MachineStore Universal.State) (v : State) : State :=
  { v with length := v.length + v.current, current := readCount store 256 }

theorem fittingStore_pages (store : MachineStore Universal.State) (v : State) :
    (fittingStore store v).wasm.mem.pages = store.wasm.mem.pages := rfl

theorem fittingStore_input (store : MachineStore Universal.State) (v : State) :
    (fittingStore store v).wasm.host.stdio.input = store.wasm.host.stdio.input.drop (readCount store 256) := by
  rw [fittingStore, readResult_input]
  rfl

theorem copy_read32_disjoint (memory : Mem) (destination source count : Nat) (address : UInt32)
    (h : address.toNat + 4 ≤ destination ∨ destination + count ≤ address.toNat) :
    (memory.copy destination source count).read32 address = memory.read32 address := by
  have h0 : ¬ (destination ≤ address.toNat ∧ address.toNat < destination + count) := by omega
  have h1 : ¬ (destination ≤ address.toNat + 1 ∧ address.toNat + 1 < destination + count) := by omega
  have h2 : ¬ (destination ≤ address.toNat + 2 ∧ address.toNat + 2 < destination + count) := by omega
  have h3 : ¬ (destination ≤ address.toNat + 3 ∧ address.toNat + 3 < destination + count) := by omega
  simp only [Mem.read32, Mem.copy, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem writeBytes_read32_disjoint (memory : Mem) (destination : Nat) (bytes : List UInt8)
    (address : UInt32)
    (h : address.toNat + 4 ≤ destination ∨ destination + bytes.length ≤ address.toNat) :
    (memory.writeBytes destination bytes).read32 address = memory.read32 address := by
  have h0 : ¬ (destination ≤ address.toNat ∧ address.toNat < destination + bytes.length) := by omega
  have h1 : ¬ (destination ≤ address.toNat + 1 ∧ address.toNat + 1 < destination + bytes.length) := by omega
  have h2 : ¬ (destination ≤ address.toNat + 2 ∧ address.toNat + 2 < destination + bytes.length) := by omega
  have h3 : ¬ (destination ≤ address.toNat + 3 ∧ address.toNat + 3 < destination + bytes.length) := by omega
  simp only [Mem.read32, Mem.writeBytes, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3]

theorem appendedStore_pages (store : MachineStore Universal.State) (dataPtr : UInt32)
    (length current : Nat) :
    (appendedStore store dataPtr length current).wasm.mem.pages = store.wasm.mem.pages := rfl

theorem appendedStore_length (store : MachineStore Universal.State) (dataPtr : UInt32)
    (length current : Nat) :
    (appendedStore store dataPtr length current).wasm.mem.read32 (driverBase + 8) =
      UInt32.ofNat (length + current) := Mem.read32_write32_same _ _ _

/-- Appending into the heap leaves every disjoint metadata word unchanged. -/
theorem appendedStore_metadata (store : MachineStore Universal.State) (dataPtr : UInt32)
    (length current : Nat) (address : UInt32)
    (hheap : address.toNat + 4 ≤ (dataPtr + UInt32.ofNat length).toNat)
    (hheader : address.toNat + 4 ≤ (driverBase + 8).toNat ∨
      (driverBase + 8).toNat + 4 ≤ address.toNat) :
    (appendedStore store dataPtr length current).wasm.mem.read32 address =
      store.wasm.mem.read32 address := by
  unfold appendedStore
  rw [Mem.read32_write32_disjoint _ _ _ _ hheader]
  exact copy_read32_disjoint _ _ _ _ _ (Or.inl hheap)

/-- Host reads preserve every word outside the actual transferred range. -/
theorem readResult_metadata (store : MachineStore Universal.State) (requested pointer address : UInt32)
    (h : address.toNat + 4 ≤ pointer.toNat ∨ pointer.toNat + readCount store requested ≤ address.toNat) :
    (readResult store requested pointer).wasm.mem.read32 address = store.wasm.mem.read32 address := by
  unfold readResult readStore
  apply writeBytes_read32_disjoint
  simpa only [List.length_take, readCount] using h

theorem fittingStore_metadata (store : MachineStore Universal.State) (v : State) (address : UInt32)
    (hheap : address.toNat + 4 ≤ (v.dataPtr + UInt32.ofNat v.length).toNat)
    (hheader : address.toNat + 4 ≤ (driverBase + 8).toNat ∨
      (driverBase + 8).toNat + 4 ≤ address.toNat)
    (hchunk : address.toNat + 4 ≤ (driverBase + 12).toNat ∨
      (driverBase + 12).toNat + 256 ≤ address.toNat) :
    (fittingStore store v).wasm.mem.read32 address = store.wasm.mem.read32 address := by
  unfold fittingStore
  rw [readResult_metadata _ _ _ _ (by
    have hcount := readCount_bound (appendedStore store v.dataPtr v.length v.current)
    omega)]
  exact appendedStore_metadata store v.dataPtr v.length v.current address hheap hheader

set_option maxRecDepth 65536 in
/-- A fitting append and next host read preserve the complete concrete loop
invariant. Word preservation uses physical separation from the heap and chunk
buffer, rather than assuming a future header value. -/
theorem fitting_invariant {total : Nat} {store : MachineStore Universal.State} {v : State}
    (h : Invariant total store v) (hpositive : 0 < v.current)
    (hfits : v.current ≤ v.capacity.toNat - v.length) :
    Invariant total (fittingStore store v) (fittingState store v) := by
  have hlength : v.length + v.current ≤ v.capacity.toNat := by have := h.length_capacity; omega
  have hnonzero : v.capacity ≠ 0 := by
    intro hz
    have hzero : v.capacity.toNat = 0 := by rw [hz]; rfl
    omega
  have hdata := h.heap_pointer hnonzero
  have hword : v.dataPtr.toNat + v.length < UInt32.size := by
    have := h.allocation_frontier
    have := h.frontier_signed
    norm_num [UInt32.size]
    omega
  have haddress := byteOffset_toNat v.dataPtr v.length hword
  have hheap : heapBase.toNat ≤ (v.dataPtr + UInt32.ofNat v.length).toNat := by
    rw [haddress]
    omega
  have hheaderCap : (fittingStore store v).wasm.mem.read32 driverBase = v.capacity := by
    rw [fittingStore_metadata store v driverBase
      (le_trans (by decide : driverBase.toNat + 4 ≤ heapBase.toNat) hheap) (by decide) (by decide)]
    exact h.header_capacity
  have hheaderPtr : (fittingStore store v).wasm.mem.read32 (driverBase + 4) = v.dataPtr := by
    rw [fittingStore_metadata store v (driverBase + 4)
      (le_trans (by decide : (driverBase + 4).toNat + 4 ≤ heapBase.toNat) hheap) (by decide) (by decide)]
    exact h.header_pointer
  have hheaderLength : (fittingStore store v).wasm.mem.read32 (driverBase + 8) =
      UInt32.ofNat (v.length + v.current) := by
    unfold fittingStore
    rw [readResult_metadata _ _ _ _ (Or.inl (by decide))]
    exact appendedStore_length _ _ _ _
  have hcursor : (fittingStore store v).wasm.mem.read32 allocatorCursor = v.storedCursor := by
    rw [fittingStore_metadata store v allocatorCursor
      (le_trans (by decide : allocatorCursor.toNat + 4 ≤ heapBase.toNat) hheap) (by decide) (by decide)]
    exact h.cursor
  have hc : readCount store 256 ≤ store.wasm.host.stdio.input.length := min_le_right _ _
  have hremaining :
      (fittingState store v).current + (fittingStore store v).wasm.host.stdio.input.length =
        store.wasm.host.stdio.input.length := by
    rw [fittingStore_input, List.length_drop]
    change readCount store 256 + (_ - readCount store 256) = _
    omega
  have hgeo := MemoryBounds.BoundedGeometricVecFacts.appendWithoutReserve total v.length v.current
    store.wasm.host.stdio.input.length v.capacity v.dataPtr v.frontier v.history h.lineage hpositive hfits
  refine {
    total_eq := ?_, chunk_shape := ?_, lineage := ?_,
    header_capacity := hheaderCap, header_pointer := hheaderPtr,
    header_length := hheaderLength, cursor := hcursor,
    effective := h.effective, module := h.module, host := h.host, cap := h.cap, global := h.global,
    pages_lower := h.pages_lower, pages_upper := h.pages_upper,
    length_capacity := hlength, allocation_frontier := h.allocation_frontier,
    frontier_physical := h.frontier_physical, frontier_signed := h.frontier_signed,
    heap_pointer := h.heap_pointer }
  · have ht := h.total_eq
    change total = (v.length + v.current) + _ + _
    rw [Nat.add_assoc, hremaining]
    exact ht
  · rw [hremaining]
    rfl
  · change BoundedGeometricVecFacts total (v.length + v.current)
      ((fittingState store v).current + (fittingStore store v).wasm.host.stdio.input.length)
      v.capacity v.dataPtr v.frontier v.history
    rw [hremaining]
    exact hgeo

/-- The active concrete lineage constructively supplies the record retired by
reserve. No arbitrary ghost-history update is assumed. -/
theorem reserve_history_exists {total : Nat} {store : MachineStore Universal.State} {v : State}
    (h : Invariant total store v) (hpositive : 0 < v.current)
    (newPtr : UInt32) (layout : AllocLayout) :
    ∃ nextHistory, VecReserveHistory v.history nextHistory v.capacity v.dataPtr newPtr layout := by
  by_cases hz : v.capacity = 0
  · exact ⟨v.history.allocate newPtr layout, by simp [VecReserveHistory, hz]⟩
  · rcases h.lineage.1 with he | hs | ⟨exponent, hlo, hhi, hcap, hlen, ht, hp, hf, hh⟩
    · exact False.elim (hz he.1)
    · have := hs.1
      omega
    · have hpword : v.dataPtr = UInt32.ofNat (vectorBlockBase exponent) := by
        rw [← hp, UInt32.ofNat_toNat]
      refine ⟨v.history.reallocate (exponent - 8) v.dataPtr
        { size := v.capacity.toNat, alignment := 1 } newPtr layout, ?_⟩
      rw [VecReserveHistory, if_neg hz]
      refine ⟨exponent - 8, ?_, rfl⟩
      rw [hh, hpword, hcap]
      exact geometricHistory_live_lookup exponent hlo

/-- Natural spare-capacity arithmetic agrees with the generated UInt32 test. -/
theorem capacity_test {total : Nat} {store : MachineStore Universal.State} {v : State}
    (h : Invariant total store v) :
    (UInt32.ofNat v.current ≤ v.capacity - UInt32.ofNat v.length) ↔
      v.current ≤ v.capacity.toNat - v.length := by
  have hlen : v.length < UInt32.size := lt_of_le_of_lt h.length_capacity v.capacity.toNat_lt
  have hcurrent : v.current < UInt32.size := by
    have hc : v.current ≤ 256 := h.chunk_shape ▸ min_le_left _ _
    norm_num [UInt32.size]
    omega
  have hle : UInt32.ofNat v.length ≤ v.capacity := by
    rw [UInt32.le_iff_toNat_le_toNat, UInt32.toNat_ofNat_of_lt' hlen]
    exact h.length_capacity
  rw [UInt32.le_iff_toNat_le_toNat, UInt32.toNat_sub_of_le _ _ hle,
    UInt32.toNat_ofNat_of_lt' hlen, UInt32.toNat_ofNat_of_lt' hcurrent]

/-- The initial seventeen pages cover every fixed stack/cursor word and the
full requested chunk buffer, independently of future heap growth. -/
theorem fixed_ranges {total : Nat} {store : MachineStore Universal.State} {v : State}
    (h : Invariant total store v) :
    (driverBase + 12).toNat + 256 ≤ store.wasm.mem.pages * 65536 ∧
      allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by
  have hp := Nat.mul_le_mul_right 65536 h.pages_lower
  constructor <;> exact le_trans (by decide) hp

end Project.Mergesort.InputLoopCost
