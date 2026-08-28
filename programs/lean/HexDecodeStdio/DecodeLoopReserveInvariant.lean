import HexDecodeStdio.DecodeLoopReserveArithmetic
import HexDecodeStdio.DecodeLoopReserveOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem Mem.readBytes_copy_before (m : Mem) (off len dst src count : Nat)
    (hbefore : off + len ≤ dst) :
    (m.copy dst src count).readBytes off len = m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range, Mem.copy]
    rw [if_neg]
    omega

theorem ByteGrowSuccess.realloc_preserves_readBytes_before
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (holdCapacity : oldCapacity ≠ 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hcopyLength : reallocatorCopyLen oldCapacity newCapacity = oldCapacity)
    (off len : Nat)
    (hbumpWord : 1053960 + 4 ≤ off)
    (hbefore : off + len ≤ (allocatorPtr oldBump 1).toNat) :
    final.wasm.mem.readBytes off len = store.wasm.mem.readBytes off len := by
  cases h with
  | freshNoGrow hzero hfit => contradiction
  | freshGrow hzero memory previousPages hgrow => contradiction
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore, hptr, hcopyLength, holdCapacity,
        or_false, if_false]
      rw [Mem.readBytes_copy_before _ _ _ _ _ _ hbefore]
      exact Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inr hbumpWord)
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore, hptr, hcopyLength, holdCapacity,
        or_false, if_false, allocatorGrownStore, allocatorBumpStore]
      rw [Mem.readBytes_copy_before _ _ _ _ _ _ hbefore]
      rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inr hbumpWord)]
      simp only [Mem.readBytes, Mem.grow_success_bytes_eq _ _ _ _ _ hgrow]

theorem ByteGrowSuccess.realloc_preserves_read32_before
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump addr : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (holdCapacity : oldCapacity ≠ 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hcopyLength : reallocatorCopyLen oldCapacity newCapacity = oldCapacity)
    (hbumpWord : addr.toNat + 4 ≤ 1053960)
    (hbefore : addr.toNat + 4 ≤ (allocatorPtr oldBump 1).toNat) :
    final.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
  cases h with
  | freshNoGrow hzero hfit => contradiction
  | freshGrow hzero memory previousPages hgrow => contradiction
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore, hptr, hcopyLength, holdCapacity,
        or_false, if_false]
      rw [Mem.read32_copy_before _ _ _ _ _ hbefore]
      exact Mem.read32_write32_disjoint _ _ _ _ (Or.inl hbumpWord)
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore, hptr, hcopyLength, holdCapacity,
        or_false, if_false, allocatorGrownStore, allocatorBumpStore]
      rw [Mem.read32_copy_before _ _ _ _ _ hbefore]
      rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl hbumpWord)]
      exact Mem.grow_success_read32_eq _ _ _ _ _ hgrow addr

theorem decodeLoopReservedStore_read32_other
    (store : MachineStore Universal.State) (oldBump newCapacity addr : UInt32)
    (hvecData : addr.toNat + 4 ≤ ((coreFrame + 60) + 4).toNat ∨
      ((coreFrame + 60) + 4).toNat + 4 ≤ addr.toNat)
    (hvecCap : addr.toNat + 4 ≤ (coreFrame + 60).toNat ∨
      (coreFrame + 60).toNat + 4 ≤ addr.toNat)
    (houtTag : addr.toNat + 4 ≤ ((coreFrame - 16) + 4).toNat ∨
      ((coreFrame - 16) + 4).toNat + 4 ≤ addr.toNat)
    (houtPtr : addr.toNat + 4 ≤ (((coreFrame - 16) + 4) + 4).toNat ∨
      (((coreFrame - 16) + 4) + 4).toNat + 4 ≤ addr.toNat)
    (houtSize : addr.toNat + 4 ≤ (((coreFrame - 16) + 4) + 8).toNat ∨
      (((coreFrame - 16) + 4) + 8).toNat + 4 ≤ addr.toNat) :
    (decodeLoopReservedStore store oldBump newCapacity).wasm.mem.read32 addr =
      store.wasm.mem.read32 addr := by
  simp only [decodeLoopReservedStore, reserveFinishStore, reserveVectorStore,
    growResultOkStore]
  rw [Mem.read32_write32_disjoint _ _ _ _ hvecData,
    Mem.read32_write32_disjoint _ _ _ _ hvecCap,
    Mem.read32_write32_disjoint _ _ _ _ houtTag,
    Mem.read32_write32_disjoint _ _ _ _ houtPtr,
    Mem.read32_write32_disjoint _ _ _ _ houtSize]

theorem decodeLoopReservedStore_readBytes_above
    (store : MachineStore Universal.State) (oldBump newCapacity : UInt32)
    (off len : Nat) (habove : 1048500 ≤ off) :
    (decodeLoopReservedStore store oldBump newCapacity).wasm.mem.readBytes
      off len = store.wasm.mem.readBytes off len := by
  simp only [decodeLoopReservedStore, reserveFinishStore, reserveVectorStore,
    growResultOkStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  all_goals right
  all_goals first | exact le_trans (by decide) habove | omega

theorem decodeLoopReservedStore_capacity
    (store : MachineStore Universal.State) (oldBump newCapacity : UInt32) :
    (decodeLoopReservedStore store oldBump newCapacity).wasm.mem.read32
      (coreFrame + 60) = newCapacity := by
  simp only [decodeLoopReservedStore, reserveFinishStore, reserveVectorStore]
  rw [Mem.read32_write32_disjoint]
  · exact Mem.read32_write32_same _ _ _
  · left
    decide

theorem DecodeLoopInv.reserve_success_finish_bound
    {input consumed remaining decoded : List UInt8}
    {store allocStore : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (hsuccess : ByteGrowSuccess (reserveFrameStore store (coreFrame - 16))
      capacity ptr (reserveNewCapacity outLen 1 capacity) bump allocStore) :
    (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat ≤
      allocStore.wasm.mem.pages * 65536 := by
  cases hsuccess with
  | freshNoGrow hzero hfit =>
      exfalso
      have hc := h.capacity_pos
      simp [hzero] at hc
  | freshGrow hzero memory previousPages hgrow =>
      exfalso
      have hc := h.capacity_pos
      simp [hzero] at hc
  | reallocNoGrow hnonzero hfit =>
      simpa [reallocatorResultStore_pages, reserveFrameStore] using
        h.reserve_finish_le_pages_of_required_le hfull hfit
  | reallocGrow hnonzero memory previousPages hgrow =>
      have hcover := h.reserve_grown_pages_cover_required hfull memory
        previousPages (by
          simpa only [reserveFrameStore_mem, reserveFrameStore_memoryCap,
            reserveFrameStore_runtime] using hgrow)
      have hceil :
          (allocatorFinish
            (reserveNewCapacity outLen 1 capacity) 1 bump).toNat ≤
            (allocatorRequiredPages
              (reserveNewCapacity outLen 1 capacity) 1 bump).toNat * 65536 := by
        apply ceil_pages_bound
        rw [← h.reserve_requiredPages_toNat hfull]
      simpa [reallocatorResultStore_pages, allocatorGrownStore] using
        le_trans hceil (Nat.mul_le_mul_right 65536 hcover)

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.after_reserve
    {input consumed remaining decoded : List UInt8}
    {store allocStore : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (hfinish : ¬(allocatorFinish
      (reserveNewCapacity outLen 1 capacity) 1 bump).toInt32 <
        UInt32.toInt32 0)
    (hsuccess : ByteGrowSuccess (reserveFrameStore store (coreFrame - 16))
      capacity ptr (reserveNewCapacity outLen 1 capacity) bump allocStore) :
    let newCapacity := reserveNewCapacity outLen 1 capacity
    let newPtr := allocatorPtr bump 1
    let newBump := allocatorFinish newCapacity 1 bump
    let reserved := decodeLoopReservedStore allocStore bump newCapacity
    DecodeLoopInv input consumed remaining decoded reserved inputCapacity
      data inputLen newPtr newCapacity outLen newBump pending := by
  dsimp only
  let newCapacity := reserveNewCapacity outLen 1 capacity
  let newPtr := allocatorPtr bump 1
  let newBump := allocatorFinish newCapacity 1 bump
  let base := reserveFrameStore store (coreFrame - 16)
  let reserved := decodeLoopReservedStore allocStore bump newCapacity
  have hcapacityNe : capacity ≠ 0 := by
    intro hz
    have hc := h.capacity_pos
    simp [hz] at hc
  have hptrEq : newPtr = bump := by
    exact h.reserve_allocator_ptr
  have hptrNe : newPtr ≠ 0 := by simpa [hptrEq] using h.bump_ne_zero
  have hcopy : reallocatorCopyLen capacity newCapacity = capacity := by
    exact h.reserve_copy_length hfull
  have hmeta (addr : UInt32) (haddr : addr.toNat + 4 ≤ 1053960) :
      allocStore.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
    have hb : addr.toNat + 4 ≤ newPtr.toNat := by
      rw [hptrEq]
      have hp := h.input_before_output
      have hd := h.data_lower
      have he := h.output_end
      omega
    have hh := hsuccess.realloc_preserves_read32_before hcapacityNe hptrNe
      hcopy haddr hb
    simpa [base, reserveFrameStore] using hh
  have hinputPreserved : allocStore.wasm.mem.readBytes data.toNat input.length =
      input := by
    have hbefore : data.toNat + input.length ≤ newPtr.toNat := by
      rw [hptrEq]
      have hc := h.input_capacity
      have hp := h.input_before_output
      have he := h.output_end
      omega
    have hh := hsuccess.realloc_preserves_readBytes_before hcapacityNe hptrNe
      hcopy data.toNat input.length (by have hd := h.data_lower; omega) hbefore
    simpa [base, reserveFrameStore, h.input_bytes] using hh
  have houtputCopied : allocStore.wasm.mem.readBytes newPtr.toNat decoded.length =
      decoded := by
    have holdNoWrap : ptr.toNat + capacity.toNat < UInt32.size := by
      rw [h.output_end]
      have hb := h.bump_signed
      norm_num [UInt32.size] at hb ⊢
      omega
    have hnewNoWrap : newPtr.toNat + capacity.toNat < UInt32.size := by
      rw [hptrEq]
      have hb := h.bump_signed
      have hs := h.capacity_small_when_full hfull
      norm_num [UInt32.size] at hb hs ⊢
      omega
    have hall := hsuccess.realloc_preserves_bytes hcapacityNe hptrNe hcopy
      holdNoWrap hnewNoWrap (Or.inr (by
        have hd := h.data_lower
        have hp := h.input_before_output
        omega))
    have hlen : decoded.length = capacity.toNat := by
      rw [← h.output_length, hfull]
    change allocStore.wasm.mem.readBytes
      (allocatorPtr bump 1).toNat decoded.length = decoded
    rw [hlen]
    calc
      allocStore.wasm.mem.readBytes (allocatorPtr bump 1).toNat capacity.toNat =
          base.wasm.mem.readBytes ptr.toNat capacity.toNat := hall
      _ = store.wasm.mem.readBytes ptr.toNat capacity.toNat := rfl
      _ = decoded := by simpa [hlen] using h.output_bytes
  have hmemoryCapBase :
      base.wasm.memoryCap base.runtime.currentModule 0 = 65536 := by
    change store.wasm.memoryCap store.runtime.currentModule 0 = 65536
    exact h.memory_cap
  have hpagesMono := hsuccess.pages_mono
  have hpagesCap := hsuccess.pages_le_cap hmemoryCapBase (by
      simpa [base, reserveFrameStore] using h.pages_upper)
  have hruntime := hsuccess.runtime_eq
  have hhost := hsuccess.host_eq
  have hmemoryCap := hsuccess.memoryCap_eq «module» 0
  have hglobalAlloc := hsuccess.globalAt_eq 0
  have hfinishBound := h.reserve_success_finish_bound hfull hsuccess
  have hbumpRead := hsuccess.read_bump (by
    rw [h.reserve_allocator_ptr]
    have he := h.output_end
    have hp := h.input_before_output
    have hd := h.data_lower
    omega)
  have hnewNat := h.reserve_new_capacity_toNat hfull
  have hfinishNat := h.reserve_finish_toNat hfull
  refine
    { input_split := h.input_split
      input_even := h.input_even
      consumed_even := h.consumed_even
      decoded_consumed := h.decoded_consumed
      input_length := h.input_length
      remaining_length := ?_
      iterator_error := ?_
      iterator_chunk := ?_
      iterator_pointer := ?_
      iterator_index := ?_
      error_marker := ?_
      input_bytes := ?_
      input_capacity := h.input_capacity
      input_before_output := ?_
      data_lower := h.data_lower
      vector_capacity := ?_
      vector_pointer := ?_
      vector_length := ?_
      output_bytes := ?_
      output_length := h.output_length
      output_fits := ?_
      capacity_pos := ?_
      capacity_min := ?_
      output_end := ?_
      output_bound := ?_
      bump_eq := ?_
      bump_signed := UInt32.toNat_lt_signed_limit_of_not_negative _ hfinish
      runtime_module := ?_
      runtime_host := ?_
      memory_cap := ?_
      pages_lower := ?_
      pages_upper := ?_
      global_eq := ?_
      status_capacity := ?_
      status_pointer := ?_
      status_length := ?_
      input_eq := ?_
      output_eq := ?_
      oom_eq := ?_ }
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (loopIterator + 4) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (loopIterator + 4) (by decide)).trans
        h.remaining_length)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (loopIterator + 16) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (loopIterator + 16) (by decide)).trans
        h.iterator_error)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (loopIterator + 8) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (loopIterator + 8) (by decide)).trans
        h.iterator_chunk)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      loopIterator (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta loopIterator (by decide)).trans
        h.iterator_pointer)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (loopIterator + 12) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (loopIterator + 12) (by decide)).trans
        h.iterator_index)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      loopError (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta loopError (by decide)).trans h.error_marker)
  · exact (decodeLoopReservedStore_readBytes_above allocStore bump newCapacity
      data.toNat input.length (le_trans (by decide) h.data_lower)).trans
        hinputPreserved
  · rw [h.reserve_allocator_ptr]
    have hp := h.input_before_output
    have he := h.output_end
    omega
  · exact decodeLoopReservedStore_capacity allocStore bump newCapacity
  · simpa [reserved, decodeLoopReservedStore] using
      reserveFinishStore_read_data
        (growResultOkStore allocStore ((coreFrame - 16) + 4) newPtr newCapacity)
        (coreFrame + 60) newPtr newCapacity coreFrame
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (coreFrame + 68) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (coreFrame + 68) (by decide)).trans
        h.vector_length)
  · exact (decodeLoopReservedStore_readBytes_above allocStore bump newCapacity
      newPtr.toNat decoded.length (by
        rw [hptrEq]
        have he := h.output_end
        have hp := h.input_before_output
        have hd := h.data_lower
        omega)).trans houtputCopied
  · change outLen.toNat ≤
      (reserveNewCapacity outLen 1 capacity).toNat
    rw [h.reserve_new_capacity_toNat hfull, hfull]
    omega
  · change 0 < (reserveNewCapacity outLen 1 capacity).toNat
    rw [h.reserve_new_capacity_toNat hfull]
    have hc := h.capacity_pos
    omega
  · change 8 ≤ (reserveNewCapacity outLen 1 capacity).toNat
    rw [h.reserve_new_capacity_toNat hfull]
    have hc := h.capacity_min
    omega
  · change (allocatorPtr bump 1).toNat +
      (reserveNewCapacity outLen 1 capacity).toNat =
        (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat
    rw [h.reserve_allocator_ptr, h.reserve_finish_toNat hfull,
      h.reserve_new_capacity_toNat hfull]
  · change (allocatorFinish
      (reserveNewCapacity outLen 1 capacity) 1 bump).toNat ≤
        allocStore.wasm.mem.pages * 65536
    exact hfinishBound
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      1053960 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hbumpRead
  · change allocStore.runtime.currentModule = «module»
    rw [hruntime]
    exact h.runtime_module
  · change allocStore.runtime.currentHost = Universal.envFor «module»
    rw [hruntime]
    exact h.runtime_host
  · change allocStore.wasm.memoryCap allocStore.runtime.currentModule 0 = 65536
    calc
      _ = base.wasm.memoryCap base.runtime.currentModule 0 := by
        rw [hruntime]
        exact hsuccess.memoryCap_eq base.runtime.currentModule 0
      _ = 65536 := hmemoryCapBase
  · change 17 ≤ allocStore.wasm.mem.pages
    exact le_trans h.pages_lower (by simpa [base, reserveFrameStore] using hpagesMono)
  · change allocStore.wasm.mem.pages ≤ 65536
    exact hpagesCap
  · apply reserveFinishStore_global_zero
    rw [growResultOkStore_globalAt, hglobalAlloc]
    apply reserveFrameStore_global_zero
    exact h.global_eq
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      decodeStatusVector (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta decodeStatusVector (by decide)).trans
        h.status_capacity)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (decodeStatusVector + 4) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (decodeStatusVector + 4) (by decide)).trans
        h.status_pointer)
  · exact (decodeLoopReservedStore_read32_other allocStore bump newCapacity
      (decodeStatusVector + 8) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ((hmeta (decodeStatusVector + 8) (by decide)).trans
        h.status_length)
  · change allocStore.wasm.host.stdio.input = []
    rw [hhost]
    exact h.input_eq
  · change allocStore.wasm.host.stdio.output = []
    rw [hhost]
    exact h.output_eq
  · change allocStore.wasm.host.oom.raised = false
    rw [hhost]
    exact h.oom_eq

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.after_valid_pair_reserve
    {input consumed rest decoded : List UInt8}
    {store allocStore : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending hi lo : UInt8} (hiRoute loRoute : HexRoute)
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (hfinish : ¬(allocatorFinish
      (reserveNewCapacity outLen 1 capacity) 1 bump).toInt32 <
        UInt32.toInt32 0)
    (hsuccess : ByteGrowSuccess (reserveFrameStore store (coreFrame - 16))
      capacity ptr (reserveNewCapacity outLen 1 capacity) bump allocStore)
    (hhi : hiRoute.valid hi) (hlo : loRoute.valid lo) :
    let newCapacity := reserveNewCapacity outLen 1 capacity
    let newPtr := allocatorPtr bump 1
    let newBump := allocatorFinish newCapacity 1 bump
    let reserved := decodeLoopReservedStore allocStore bump newCapacity
    let appended := decodeLoopAppendStore reserved newPtr outLen pending
    let inputPtr := data + UInt32.ofNat consumed.length
    let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
    let chunkIndex := UInt32.ofNat (consumed.length / 2)
    let next := (loRoute.nibble lo).toUInt8 |||
      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
    let paired := decodeLoopPairValidStore appended inputPtr remainingWord
      chunkIndex next
    DecodeLoopInv input (consumed ++ [hi, lo]) rest (decoded ++ [pending])
      paired inputCapacity data inputLen newPtr newCapacity (1 + outLen)
      newBump next := by
  dsimp only
  let newCapacity := reserveNewCapacity outLen 1 capacity
  let newPtr := allocatorPtr bump 1
  let newBump := allocatorFinish newCapacity 1 bump
  let reserved := decodeLoopReservedStore allocStore bump newCapacity
  have hreserved : DecodeLoopInv input consumed (hi :: lo :: rest) decoded
      reserved inputCapacity data inputLen newPtr newCapacity outLen newBump
      pending := h.after_reserve hfull hfinish hsuccess
  have hspare : outLen ≠ newCapacity := by
    intro heq
    have hn := congrArg UInt32.toNat heq
    change outLen.toNat =
      (reserveNewCapacity outLen 1 capacity).toNat at hn
    rw [h.reserve_new_capacity_toNat hfull, hfull] at hn
    have hc := h.capacity_pos
    omega
  exact hreserved.after_valid_pair_no_grow hiRoute loRoute hspare hhi hlo

end Submission.HexDecodeStdio
