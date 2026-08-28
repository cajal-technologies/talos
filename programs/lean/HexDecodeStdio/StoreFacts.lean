import HexDecodeStdio.ReadChunkOperational

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem Mem.read8_writeBytes_disjoint (m : Mem) (off : Nat)
    (bytes : List UInt8) (addr : UInt32)
    (h : addr.toNat < off ∨ off + bytes.length ≤ addr.toNat) :
    (m.writeBytes off bytes).read8 addr = m.read8 addr := by
  simp only [Mem.writeBytes, Mem.read8]
  rw [dif_neg]
  omega

theorem Mem.read32_writeBytes_disjoint (m : Mem) (off : Nat)
    (bytes : List UInt8) (addr : UInt32)
    (h : addr.toNat + 4 ≤ off ∨ off + bytes.length ≤ addr.toNat) :
    (m.writeBytes off bytes).read32 addr = m.read32 addr := by
  simp only [Mem.writeBytes, Mem.read32]
  rw [dif_neg, dif_neg, dif_neg, dif_neg]
  all_goals omega

theorem Mem.grow_success_bytes_eq (m memory : Mem) (delta : UInt32)
    (cap previous : Nat)
    (h : m.grow delta cap = some (memory, previous)) :
    memory.bytes = m.bytes := by
  simp only [Mem.grow] at h
  split at h
  · symm
    simpa using congrArg (fun pair => pair.1.bytes) (Option.some.inj h)
  · contradiction

theorem Mem.grow_success_read8_eq (m memory : Mem) (delta : UInt32)
    (cap previous : Nat)
    (h : m.grow delta cap = some (memory, previous)) (addr : UInt32) :
    memory.read8 addr = m.read8 addr := by
  simp only [Mem.read8, Mem.grow_success_bytes_eq m memory delta cap previous h]

theorem Mem.grow_success_read32_eq (m memory : Mem) (delta : UInt32)
    (cap previous : Nat)
    (h : m.grow delta cap = some (memory, previous)) (addr : UInt32) :
    memory.read32 addr = m.read32 addr := by
  simp only [Mem.read32, Mem.grow_success_bytes_eq m memory delta cap previous h]

theorem UInt32.toInt32_not_negative_of_small (x : UInt32)
    (h : x.toNat < 2 ^ 31) : ¬x.toInt32 < (0 : UInt32).toInt32 := by
  rw [Int32.lt_iff_toInt_lt]
  have hu : x.toInt32.toBitVec.toNat = x.toNat := rfl
  have hx : x.toInt32.toInt = x.toNat := by
    apply BitVec.toInt_eq_toNat_of_lt
    rw [hu]
    omega
  have hz : ((0 : UInt32).toInt32).toInt = 0 := by decide
  rw [hx, hz]
  omega

theorem readAdapterResultStore_read_tag
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8)
    (hnext : (out + 4).toNat = out.toNat + 4) :
    (readAdapterResultStore store out pointer bytes).wasm.mem.read8 out = 4 := by
  simp only [readAdapterResultStore, universalReadStore, Mem.read8, Mem.write32,
    Mem.write8]
  have h0 : out.toNat ≠ (out + 4).toNat := by omega
  have h1 : out.toNat ≠ (out + 4).toNat + 1 := by omega
  have h2 : out.toNat ≠ (out + 4).toNat + 2 := by omega
  have h3 : out.toNat ≠ (out + 4).toNat + 3 := by omega
  have hmod : (out.toNat + 4) % UInt32.size = out.toNat + 4 := by
    simpa using hnext
  split_ifs <;> first | rfl | omega

theorem readAdapterResultStore_read_count
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8) :
    (readAdapterResultStore store out pointer bytes).wasm.mem.read32 (out + 4) =
      UInt32.ofNat bytes.length := by
  simp [readAdapterResultStore, universalReadStore]

theorem readAdapterResultStore_read32_disjoint
    (store : MachineStore Universal.State) (out pointer addr : UInt32)
    (bytes : List UInt8)
    (hbuffer : addr.toNat + 4 ≤ pointer.toNat ∨
      pointer.toNat + bytes.length ≤ addr.toNat)
    (htag : addr.toNat + 4 ≤ out.toNat ∨ out.toNat + 1 ≤ addr.toNat)
    (hcount : addr.toNat + 4 ≤ (out + 4).toNat ∨
      (out + 4).toNat + 4 ≤ addr.toNat) :
    (readAdapterResultStore store out pointer bytes).wasm.mem.read32 addr =
      store.wasm.mem.read32 addr := by
  simp only [readAdapterResultStore, universalReadStore]
  rw [Mem.read32_write32_disjoint _ (out + 4) addr _ (by
        rcases hcount with h | h <;> omega)]
  simp only [Mem.read32, Mem.write8]
  rw [if_neg, if_neg, if_neg, if_neg]
  · exact Mem.read32_writeBytes_disjoint _ _ _ _ hbuffer
  all_goals omega

theorem readAdapterResultStore_globalAt
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8) (index : Nat) :
    globalAt? (readAdapterResultStore store out pointer bytes) index =
      globalAt? store index := by
  rfl

theorem readAdapterResultStore_input
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8) :
    (readAdapterResultStore store out pointer bytes).wasm.host.stdio.input =
      store.wasm.host.stdio.input.drop bytes.length := by
  simp [readAdapterResultStore, universalReadStore, afterUniversalRead]

theorem ByteGrowSuccess.fresh_preserves_read32
    {store final : MachineStore Universal.State}
    {oldPtr newCapacity oldBump addr : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr newCapacity oldBump final)
    (haddr : addr.toNat + 4 ≤ 1053960) :
    final.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
  cases h with
  | freshNoGrow hzero hfit =>
      simp only [allocatorBumpStore]
      exact Mem.read32_write32_disjoint _ 1053960 addr _ (Or.inl haddr)
  | freshGrow hzero memory previousPages hgrow =>
      simp only [allocatorBumpStore, allocatorGrownStore]
      rw [Mem.read32_write32_disjoint _ 1053960 addr _ (Or.inl haddr)]
      exact Mem.grow_success_read32_eq _ _ _ _ _ hgrow addr
  | reallocNoGrow hnonzero hfit => contradiction
  | reallocGrow hnonzero memory previousPages hgrow => contradiction

theorem reserveFinishStore_read_length_of_fresh
    {store allocStore : MachineStore Universal.State}
    (frame vector oldPtr newCapacity oldBump length : UInt32)
    (hsuccess : ByteGrowSuccess store 0 oldPtr newCapacity oldBump allocStore)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (hstack : (vector + 8).toNat + 4 ≤ 1053960)
    (hframe0 : (vector + 8).toNat + 4 ≤ (frame + 4).toNat ∨
      (frame + 4).toNat + 4 ≤ (vector + 8).toNat)
    (hframe1 : (vector + 8).toNat + 4 ≤ ((frame + 4) + 4).toNat ∨
      ((frame + 4) + 4).toNat + 4 ≤ (vector + 8).toNat)
    (hframe2 : (vector + 8).toNat + 4 ≤ ((frame + 4) + 8).toNat ∨
      ((frame + 4) + 8).toNat + 4 ≤ (vector + 8).toNat)
    (hvecNo1 : (vector + 8).toNat + 4 ≤ vector.toNat ∨
      vector.toNat + 4 ≤ (vector + 8).toNat)
    (hvecNo2 : (vector + 8).toNat + 4 ≤ (vector + 4).toNat ∨
      (vector + 4).toNat + 4 ≤ (vector + 8).toNat) :
    (reserveFinishStore
      (growResultOkStore allocStore (frame + 4)
        (allocatorPtr oldBump 1) newCapacity)
      vector (allocatorPtr oldBump 1) newCapacity (frame + 16)).wasm.mem.read32
        (vector + 8) = length := by
  simp only [reserveFinishStore, reserveVectorStore, growResultOkStore]
  rw [Mem.read32_write32_disjoint _ (vector + 4) (vector + 8) _ hvecNo2]
  rw [Mem.read32_write32_disjoint _ vector (vector + 8) _ hvecNo1]
  rw [Mem.read32_write32_disjoint _ (frame + 4) (vector + 8) _ hframe0]
  rw [Mem.read32_write32_disjoint _ ((frame + 4) + 4) (vector + 8) _ hframe1]
  rw [Mem.read32_write32_disjoint _ ((frame + 4) + 8) (vector + 8) _ hframe2]
  exact hsuccess.fresh_preserves_read32 hstack |>.trans hlength

theorem reserveFinishStore_read_data
    (store : MachineStore Universal.State)
    (vector data capacity sp : UInt32) :
    (reserveFinishStore store vector data capacity sp).wasm.mem.read32
      (vector + 4) = data := by
  simp only [reserveFinishStore, reserveVectorStore]
  exact Mem.read32_write32_same _ _ _

@[simp] theorem reserveFinishStore_pages
    (store : MachineStore Universal.State)
    (vector data capacity sp : UInt32) :
    (reserveFinishStore store vector data capacity sp).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

theorem reserveFinishStore_global_zero
    (store : MachineStore Universal.State)
    (vector data capacity sp old : UInt32)
    (hglobal : globalAt? store 0 = some (.i32 old)) :
    globalAt? (reserveFinishStore store vector data capacity sp) 0 =
      some (.i32 sp) := by
  simp only [globalAt?, canonicalGlobalIndex_zero] at hglobal ⊢
  have hzero : 0 < store.wasm.globals.globals.length :=
    (getElem?_eq_some_iff.mp hglobal).1
  simpa [reserveFinishStore, reserveVectorStore] using
    (List.getElem?_set_eq_of_lt (.i32 sp) hzero)

theorem readChunkFrameStore_read32_after_frame
    (store : MachineStore Universal.State) (frame addr : UInt32)
    (h8 : (frame + 8).toNat + 8 ≤ addr.toNat)
    (h16 : (frame + 16).toNat + 8 ≤ addr.toNat)
    (h24 : (frame + 24).toNat + 8 ≤ addr.toNat)
    (h32 : (frame + 32).toNat + 8 ≤ addr.toNat) :
    (readChunkFrameStore store frame).wasm.mem.read32 addr =
      store.wasm.mem.read32 addr := by
  simp only [readChunkFrameStore]
  rw [Mem.read32_write64_disjoint _ addr (frame + 8) _ (Or.inr h8)]
  rw [Mem.read32_write64_disjoint _ addr (frame + 16) _ (Or.inr h16)]
  rw [Mem.read32_write64_disjoint _ addr (frame + 24) _ (Or.inr h24)]
  rw [Mem.read32_write64_disjoint _ addr (frame + 32) _ (Or.inr h32)]

theorem readChunkFrameStore_global_zero
    (store : MachineStore Universal.State) (frame old : UInt32)
    (hglobal : globalAt? store 0 = some (.i32 old)) :
    globalAt? (readChunkFrameStore store frame) 0 = some (.i32 frame) := by
  simp only [globalAt?, canonicalGlobalIndex_zero] at hglobal ⊢
  have hzero : 0 < store.wasm.globals.globals.length :=
    (getElem?_eq_some_iff.mp hglobal).1
  simpa [readChunkFrameStore] using
    (List.getElem?_set_eq_of_lt (.i32 frame) hzero)

end Project.HexDecodeStdio
