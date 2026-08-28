import HexDecodeStdio.DecodeLoopReserveInvariant
import HexDecodeStdio.ReserveOutcome

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.reserve_reachesOrOOM
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (returningInstance : ModuleInstanceId) :
    ReachesOrOOM
      (decodeLoopReserveConfig store data inputLen ptr outLen seed pending
        returningInstance)
      (fun final => ∃ allocStore,
        ¬(allocatorFinish
          (reserveNewCapacity outLen 1 capacity) 1 bump).toInt32 <
            UInt32.toInt32 0 ∧
        ByteGrowSuccess (reserveFrameStore store (coreFrame - 16)) capacity ptr
          (reserveNewCapacity outLen 1 capacity) bump allocStore ∧
        final = decodeLoopCallConfig
          (decodeLoopAppendStore
            (decodeLoopReservedStore allocStore bump
              (reserveNewCapacity outLen 1 capacity))
            (allocatorPtr bump 1) outLen pending)
          data inputLen (allocatorPtr bump 1) outLen seed pending
          returningInstance) := by
  have hsum : reserveRequired outLen 1 ≥ (1 : UInt32) := by
    apply UInt32.le_iff_toNat_le.mpr
    have hadd : (outLen + (1 : UInt32)).toNat = outLen.toNat + 1 := by
      have h1 : (1 : UInt32).toNat = 1 := by decide
      rw [UInt32.toNat_add, h1, Nat.mod_eq_of_lt]
      have hs := h.capacity_small_when_full hfull
      rw [hfull]
      norm_num at hs ⊢
      omega
    change (1 : UInt32).toNat ≤ (outLen + (1 : UInt32)).toNat
    rw [hadd]
    have h1 : (1 : UInt32).toNat = 1 := by decide
    rw [h1]
    omega
  have hframe : (coreFrame - 16).toNat + 16 ≤
      store.wasm.mem.pages * 65536 := by
    change 1048432 ≤ store.wasm.mem.pages * 65536
    have hp := h.pages_lower
    omega
  have hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536 := by
    have hp := h.pages_lower
    omega
  have hsource : ptr.toNat +
      (reallocatorCopyLen capacity
        (reserveNewCapacity outLen 1 capacity)).toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [h.reserve_copy_length hfull, h.output_end]
    exact h.output_bound
  apply ReachesOrOOM.bind
    (reserve_call_reachesOrOOM store _ _ _ _ _ _ _ _
      (coreFrame + 60) outLen 1 capacity ptr coreFrame bump
      h.runtime_module h.runtime_host h.global_eq hsum h.vector_capacity
      h.vector_pointer h.bump_eq hbumpBound h.pages_upper
      (h.reserve_new_capacity_nonnegative hfull)
      (by rw [h.reserve_allocator_ptr]; exact h.bump_ne_zero)
      hframe (by decide) (by decide) (by decide)
      (by change 1048496 ≤ store.wasm.mem.pages * 65536; omega)
      (by change 1048500 ≤ store.wasm.mem.pages * 65536; omega)
      hsource (h.reserve_destination_bound hfull)
      (h.reserve_grown_copy_bounds hfull))
  intro middle hmiddle
  rcases hmiddle with ⟨allocStore, hfinish, hsuccess, rfl⟩
  let newCapacity := reserveNewCapacity outLen 1 capacity
  let newPtr := allocatorPtr bump 1
  let reserved := decodeLoopReservedStore allocStore bump newCapacity
  have hreserved : DecodeLoopInv input consumed remaining decoded reserved
      inputCapacity data inputLen newPtr newCapacity outLen
      (allocatorFinish newCapacity 1 bump) pending :=
    h.after_reserve hfull hfinish hsuccess
  have hptrRead : reserved.wasm.mem.read32 (coreFrame + 64) = newPtr := by
    simpa [reserved, newPtr, decodeLoopReservedStore] using
      reserveFinishStore_read_data
        (growResultOkStore allocStore ((coreFrame - 16) + 4) newPtr newCapacity)
        (coreFrame + 60) newPtr newCapacity coreFrame
  have hwrite : (newPtr + outLen).toNat + 1 ≤
      allocStore.wasm.mem.pages * 65536 := by
    have hlt : outLen.toNat < newCapacity.toNat := by
      change outLen.toNat <
        (reserveNewCapacity outLen 1 capacity).toNat
      rw [h.reserve_new_capacity_toNat hfull, hfull]
      have hc := h.capacity_pos
      omega
    have hsumNat : (newPtr + outLen).toNat =
        newPtr.toNat + outLen.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
      have hb := UInt32.toNat_lt_signed_limit_of_not_negative _ hfinish
      have hfinishNat := h.reserve_finish_toNat hfull
      have hptrNat : newPtr.toNat = bump.toNat := by
        change (allocatorPtr bump 1).toNat = bump.toNat
        rw [h.reserve_allocator_ptr]
      have hnewNat : newCapacity.toNat = 2 * capacity.toNat :=
        h.reserve_new_capacity_toNat hfull
      norm_num [UInt32.size] at hb ⊢
      omega
    rw [hsumNat]
    calc
      newPtr.toNat + outLen.toNat + 1 ≤
          newPtr.toNat + newCapacity.toNat := by omega
      _ = (allocatorFinish newCapacity 1 bump).toNat := hreserved.output_end
      _ ≤ allocStore.wasm.mem.pages * 65536 := hreserved.output_bound
  apply ReachesOrOOM.of_reaches
    (decode_loop_after_reserve_append allocStore data inputLen ptr outLen bump
      newCapacity seed pending returningInstance
      (le_trans h.pages_lower (by
        have hm := hsuccess.pages_mono
        simpa [reserveFrameStore] using hm)) hptrRead hwrite)
  exact ⟨allocStore, hfinish, hsuccess, rfl⟩

end Submission.HexDecodeStdio
