import HexDecodeStdio.DecodeLoopResult

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem DecodeLoopInv.next_length_of_spare
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity) :
    (1 + outLen).toNat = (decoded ++ [pending]).length := by
  have hlt : outLen.toNat < capacity.toNat := by
    apply lt_of_le_of_ne h.output_fits
    intro heq
    exact hspare (UInt32.toNat_inj.mp heq)
  have hc : capacity.toNat < 2 ^ 31 := by
    have he := h.output_end
    have hb := h.bump_signed
    omega
  have hone : (1 : UInt32).toNat = 1 := by decide
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
  · rw [hone]
    simp [h.output_length, Nat.add_comm]
  · rw [hone]
    norm_num [UInt32.size] at hc ⊢
    omega

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.empty_call_reaches
    {input consumed decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed : UInt8}
    (h : DecodeLoopInv input consumed [] decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity)
    (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    let appended := decodeLoopAppendStore store ptr outLen pending
    Reaches
      (decodeLoopCallConfig appended data inputLen ptr outLen seed pending
        returningInstance)
      (decodeAfterCoreConfig
        (decodeLoopSuccessStore (decodeLoopPairEmptyStore appended)
          ptr capacity (1 + outLen)) data) ∧
    DecodeCoreResult input data
      (decodeAfterCoreConfig
        (decodeLoopSuccessStore (decodeLoopPairEmptyStore appended)
          ptr capacity (1 + outLen)) data) := by
  dsimp only
  let appended := decodeLoopAppendStore store ptr outLen pending
  let paired := decodeLoopPairEmptyStore appended
  let finalStore := decodeLoopSuccessStore paired ptr capacity (1 + outLen)
  have hremaining : appended.wasm.mem.read32 (loopIterator + 4) = 0 := by
    rw [h.appended_read32_scratch]
    · simpa using h.remaining_length
    · have hp := h.input_before_output
      have hd := h.data_lower
      change 1048512 ≤ ptr.toNat
      omega
    · decide
  have hpair := decode_loop_pair_empty_exit appended data inputLen ptr outLen
    seed pending returningInstance h.runtime_module h.pages_lower hremaining
  have hptr : paired.wasm.mem.read32 (coreFrame + 64) = ptr := by
    simp only [paired]
    rw [show coreFrame + 64 = coreFrame + 64 by rfl]
    simp only [decodeLoopPairEmptyStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop]
    · exact h.appended_read32_scratch (by
        have hp := h.input_before_output
        have hd := h.data_lower
        have haddr : (coreFrame + 64).toNat + 4 = 1048500 := by decide
        rw [haddr]
        omega) (by decide) |>.trans h.vector_pointer
    all_goals decide
  have hcapacity : paired.wasm.mem.read32 (coreFrame + 60) = capacity := by
    simp only [paired, decodeLoopPairEmptyStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop]
    · exact h.appended_read32_scratch (by
        have hp := h.input_before_output
        have hd := h.data_lower
        have haddr : (coreFrame + 60).toNat + 4 = 1048496 := by decide
        rw [haddr]
        omega) (by decide) |>.trans h.vector_capacity
    all_goals decide
  have hpost := decode_loop_exit_to_post paired data inputLen ptr capacity
    outLen seed 0 returningInstance h.pages_lower hptr hcapacity
  have hmarker : paired.wasm.mem.read32 coreError = 1114114 := by
    simp only [paired, decodeLoopPairEmptyStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop]
    · exact h.appended_read32_scratch (by
        have hp := h.input_before_output
        have hd := h.data_lower
        change 1048468 ≤ ptr.toNat
        omega) (by decide) |>.trans h.error_marker
    all_goals decide
  have hreturn' : returningInstance = paired.runtime.entry := by
    simpa [paired, appended, decodeLoopPairEmptyStore,
      decodeLoopAppendStore] using hreturn
  have hsuccess := decode_post_loop_success_reaches paired data inputLen ptr
    capacity (1 + outLen) seed returningInstance h.pages_lower (by
      change globalAt? store 0 = some (.i32 coreFrame)
      exact h.global_eq) hmarker hreturn'
  have hfacts : DecodeCoreStoreFacts finalStore bump := by
    have hptrLower : 1054000 ≤ ptr.toNat := by
      have hp := h.input_before_output
      have hd := h.data_lower
      omega
    have preserveStatus (addr value : UInt32)
        (haddr : store.wasm.mem.read32 addr = value)
        (hbeforePtr : addr.toNat + 4 ≤ ptr.toNat)
        (hmeta : addr.toNat + 4 ≤ (coreFrame + 68).toNat ∨
          (coreFrame + 68).toNat + 4 ≤ addr.toNat)
        (hpairPayload : addr.toNat + 4 ≤ (loopPairOut + 1).toNat ∨
          (loopPairOut + 1).toNat + 1 ≤ addr.toNat)
        (hpairTag : addr.toNat + 4 ≤ loopPairOut.toNat ∨
          loopPairOut.toNat + 1 ≤ addr.toNat)
        (hresult8 : addr.toNat + 4 ≤ (decodeResultOut + 8).toNat ∨
          (decodeResultOut + 8).toNat + 4 ≤ addr.toNat)
        (hresult4 : addr.toNat + 4 ≤ (decodeResultOut + 4).toNat ∨
          (decodeResultOut + 4).toNat + 4 ≤ addr.toNat)
        (hresult0 : addr.toNat + 4 ≤ decodeResultOut.toNat ∨
          decodeResultOut.toNat + 4 ≤ addr.toNat) :
        finalStore.wasm.mem.read32 addr = value := by
      simp only [finalStore, decodeLoopSuccessStore]
      rw [Mem.read32_write32_disjoint _ _ _ _ hresult0,
        Mem.read32_write32_disjoint _ _ _ _ hresult4,
        Mem.read32_write32_disjoint _ _ _ _ hresult8]
      · simp only [paired, decodeLoopPairEmptyStore]
        rw [Mem.read32_write8_disjoint_loop _ _ _ _ hpairTag,
          Mem.read32_write8_disjoint_loop _ _ _ _ hpairPayload]
        exact (h.appended_read32_scratch hbeforePtr hmeta).trans haddr
    have preserveBump : finalStore.wasm.mem.read32 1053960 = bump := by
      apply preserveStatus 1053960 bump h.bump_eq
      · exact (show (1053960 : UInt32).toNat + 4 ≤ 1054000 by decide).trans
          hptrLower
      all_goals decide
    refine {
      runtime_module := by
        simpa [finalStore, paired, appended, decodeLoopSuccessStore,
          decodeLoopPairEmptyStore, decodeLoopAppendStore] using h.runtime_module
      runtime_host := by
        simpa [finalStore, paired, appended, decodeLoopSuccessStore,
          decodeLoopPairEmptyStore, decodeLoopAppendStore] using h.runtime_host
      memory_cap := by
        change store.wasm.memoryCap store.runtime.currentModule 0 = 65536
        exact h.memory_cap
      pages_lower := by
        change 17 ≤ store.wasm.mem.pages
        exact h.pages_lower
      pages_upper := by
        change store.wasm.mem.pages ≤ 65536
        exact h.pages_upper
      global_eq := by
        simp only [finalStore, decodeLoopSuccessStore]
        have hzero : 0 < paired.wasm.globals.globals.length := by
          apply (getElem?_eq_some_iff.mp (show
            paired.wasm.globals.globals[0]? = some (.i32 coreFrame) by
              change store.wasm.globals.globals[0]? = some (.i32 coreFrame)
              simpa only [globalAt?, canonicalGlobalIndex_zero] using h.global_eq)).1
        simpa only [globalAt?, canonicalGlobalIndex_zero] using
          (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
      status_capacity := preserveStatus decodeStatusVector 0 h.status_capacity
        (by
          have hs : decodeStatusVector.toNat + 4 ≤ 1054000 := by decide
          exact hs.trans hptrLower) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      status_pointer := preserveStatus (decodeStatusVector + 4) 1
        h.status_pointer (by
          have hs : (decodeStatusVector + 4).toNat + 4 ≤ 1054000 := by
            decide
          exact hs.trans hptrLower) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
      status_length := preserveStatus (decodeStatusVector + 8) 0
        h.status_length (by
          have hs : (decodeStatusVector + 8).toNat + 4 ≤ 1054000 := by
            decide
          exact hs.trans hptrLower) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
      input_eq := by
        simpa [finalStore, paired, appended, decodeLoopSuccessStore,
          decodeLoopPairEmptyStore, decodeLoopAppendStore] using h.input_eq
      output_eq := by
        simpa [finalStore, paired, appended, decodeLoopSuccessStore,
          decodeLoopPairEmptyStore, decodeLoopAppendStore] using h.output_eq
      oom_eq := by
        simpa [finalStore, paired, appended, decodeLoopSuccessStore,
          decodeLoopPairEmptyStore, decodeLoopAppendStore] using h.oom_eq
      bump_eq := preserveBump
      bump_zero_or_lower := Or.inr (by
        have hd := h.data_lower
        have hp := h.input_before_output
        have he := h.output_end
        omega)
      bump_signed := h.bump_signed }
  constructor
  · exact hpair.trans (hpost.trans hsuccess)
  · left
    refine ⟨finalStore, capacity, ptr, 1 + outLen, decoded ++ [pending], rfl,
      ?_, ?_, ?_, ?_, h.next_length_of_spare hspare, ?_, ?_, ?_, ?_,
      ⟨bump, hfacts, Or.inr ⟨(by
        have hp := h.input_before_output
        have hd := h.data_lower
        omega), h.output_end⟩⟩⟩
    · simpa [h.input_split] using h.decoded_consumed
    · exact (decodeLoopSuccessStore_result_fields paired ptr capacity
        (1 + outLen)).1
    · exact (decodeLoopSuccessStore_result_fields paired ptr capacity
        (1 + outLen)).2.1
    · exact (decodeLoopSuccessStore_result_fields paired ptr capacity
        (1 + outLen)).2.2
    · have hlt : outLen.toNat < capacity.toNat := by
        exact lt_of_le_of_ne h.output_fits (fun heq =>
          hspare (UInt32.toNat_inj.mp heq))
      have hn := h.next_length_of_spare hspare
      simp only [List.length_append, List.length_singleton] at hn
      rw [← h.output_length] at hn
      omega
    · have hb := h.bump_signed
      have hp : 0 < ptr.toNat := by
        have hd := h.data_lower
        have hbefore := h.input_before_output
        omega
      have he := h.output_end
      omega
    · change ptr.toNat + (1 + outLen).toNat ≤
        store.wasm.mem.pages * 65536
      have hn := h.next_length_of_spare hspare
      simp only [List.length_append, List.length_singleton] at hn
      rw [← h.output_length] at hn
      have hlt : outLen.toNat < capacity.toNat := by
        exact lt_of_le_of_ne h.output_fits (fun heq =>
          hspare (UInt32.toNat_inj.mp heq))
      have he := h.output_end
      have hb := h.output_bound
      omega
    · rw [decodeLoopSuccessStore_readBytes_above]
      · rw [decodeLoopPairEmptyStore_readBytes_above]
        · simpa only [List.length_append, List.length_singleton] using
            h.appended_output
        · have hp := h.input_before_output
          have hd := h.data_lower
          omega
      · have hp := h.input_before_output
        have hd := h.data_lower
        omega

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.empty_reachesOrOOM
    {input consumed decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed : UInt8}
    (h : DecodeLoopInv input consumed [] decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    ReachesOrOOM
      (decodeLoopHeadConfig store data inputLen ptr outLen seed pending
        returningInstance)
      (DecodeCoreResult input data) := by
  by_cases hfull : outLen = capacity
  · have hprefix := decode_loop_full_to_reserve store data inputLen ptr capacity
      outLen 0 seed pending returningInstance h.pages_lower h.vector_capacity
      hfull h.iterator_error h.error_marker (by simpa using h.remaining_length)
      h.iterator_chunk
    apply ReachesOrOOM.prependReaches hprefix
    apply (h.reserve_reachesOrOOM hfull returningInstance).bind
    intro middle hmiddle
    rcases hmiddle with ⟨allocStore, hfinish, hsuccess, rfl⟩
    let newCapacity := reserveNewCapacity outLen 1 capacity
    let newPtr := allocatorPtr bump 1
    let newBump := allocatorFinish newCapacity 1 bump
    let reserved := decodeLoopReservedStore allocStore bump newCapacity
    have hreserved : DecodeLoopInv input consumed [] decoded reserved
        inputCapacity data inputLen newPtr newCapacity outLen newBump pending :=
      h.after_reserve hfull hfinish hsuccess
    have hspare : outLen ≠ newCapacity := by
      intro heq
      have hn := congrArg UInt32.toNat heq
      change outLen.toNat =
        (reserveNewCapacity outLen 1 capacity).toNat at hn
      rw [h.reserve_new_capacity_toNat hfull, hfull] at hn
      have hc := h.capacity_pos
      omega
    have hreturn' : returningInstance = reserved.runtime.entry := by
      rw [hreturn]
      change store.runtime.entry = allocStore.runtime.entry
      rw [hsuccess.runtime_eq]
      rfl
    have hdone := hreserved.empty_call_reaches (seed := seed) hspare
      returningInstance hreturn'
    exact ReachesOrOOM.of_reaches hdone.1 hdone.2
  · have hprefix := decode_loop_append_no_grow store data inputLen ptr capacity
      outLen seed pending returningInstance h.pages_lower h.vector_capacity
      hfull (h.append_bound hfull)
    have hdone := h.empty_call_reaches (seed := seed) hfull
      returningInstance hreturn
    exact ReachesOrOOM.of_reaches (hprefix.trans hdone.1) hdone.2

end Submission.HexDecodeStdio
