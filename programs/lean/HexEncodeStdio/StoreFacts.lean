import HexEncodeStdio.ReadChunkOperational
import HexDecodeStdio.StoreFactsBase

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! The store facts that do not mention `ByteGrowSuccess` live in
`HexDecodeStdio.StoreFactsBase`, shared with the decode proofs, and are
re-exported under this namespace. -/
export Project.HexDecodeStdio (
  Mem.read8_writeBytes_disjoint Mem.read32_writeBytes_disjoint
  Mem.grow_success_bytes_eq Mem.grow_success_read8_eq
  Mem.grow_success_read32_eq UInt32.toInt32_not_negative_of_small
  readAdapterResultStore_read_tag readAdapterResultStore_read_count
  readAdapterResultStore_read32_disjoint readAdapterResultStore_globalAt
  readAdapterResultStore_input reserveFinishStore_read_data
  reserveFinishStore_pages reserveFinishStore_global_zero
  readChunkFrameStore_read32_after_frame readChunkFrameStore_global_zero)

theorem ByteGrowSuccess.fresh_preserves_read32
    {store final : MachineStore Universal.State}
    {oldPtr newCapacity oldBump addr : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr newCapacity oldBump final)
    (haddr : addr.toNat + 4 ≤ 1053960) :
    final.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative =>
      simp only [allocatorBumpStore]
      exact Mem.read32_write32_disjoint _ 1053960 addr _ (Or.inl haddr)
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative =>
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

end Project.HexEncodeStdio
