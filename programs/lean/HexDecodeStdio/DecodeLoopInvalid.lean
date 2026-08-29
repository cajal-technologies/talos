import HexDecodeStdio.DecodeLoopEmpty

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem decodeLoopPairInvalidStore_read32_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (bad : UInt8) (index addr : UInt32)
    (habove : 1048528 ≤ addr.toNat) :
    (decodeLoopPairInvalidStore store inputPtr len chunkIndex bad index).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [decodeLoopPairInvalidStore, decodeLoopPairBaseStore]
  rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint]
  all_goals right
  all_goals exact le_trans (by decide) habove

theorem DecodeLoopInv.invalid_core_facts
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (inputPtr remainingWord chunkIndex : UInt32) (badByte : UInt8)
    (index bad : UInt32) :
    DecodeCoreStoreFacts
      (decodeInvalidCoreStore
        (decodeLoopPairInvalidStore
          (decodeLoopAppendStore store ptr outLen pending)
          inputPtr remainingWord chunkIndex badByte index) bad index) bump := by
  let appended := decodeLoopAppendStore store ptr outLen pending
  let paired := decodeLoopPairInvalidStore appended inputPtr remainingWord
    chunkIndex badByte index
  let finalStore := decodeInvalidCoreStore paired bad index
  have hptrLower : 1054000 ≤ ptr.toNat := by
    have hp := h.input_before_output
    have hd := h.data_lower
    omega
  have preserve (addr value : UInt32)
      (haddr : store.wasm.mem.read32 addr = value)
      (hbeforePtr : addr.toNat + 4 ≤ ptr.toNat)
      (habove : 1048528 ≤ addr.toNat)
      (hresult8 : addr.toNat + 4 ≤ (decodeResultOut + 8).toNat ∨
        (decodeResultOut + 8).toNat + 4 ≤ addr.toNat)
      (hresult4 : addr.toNat + 4 ≤ (decodeResultOut + 4).toNat ∨
        (decodeResultOut + 4).toNat + 4 ≤ addr.toNat)
      (hresult0 : addr.toNat + 4 ≤ decodeResultOut.toNat ∨
        decodeResultOut.toNat + 4 ≤ addr.toNat) :
      finalStore.wasm.mem.read32 addr = value := by
    simp only [finalStore, decodeInvalidCoreStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ hresult0,
      Mem.read32_write32_disjoint _ _ _ _ hresult4,
      Mem.read32_write32_disjoint _ _ _ _ hresult8]
    exact (decodeLoopPairInvalidStore_read32_above appended inputPtr
      remainingWord chunkIndex badByte index addr habove).trans
      (h.appended_read32_scratch hbeforePtr (by
        right
        exact le_trans (by decide) habove) |>.trans haddr)
  refine {
    runtime_module := by
      simpa [finalStore, paired, appended, decodeInvalidCoreStore,
        decodeLoopPairInvalidStore, decodeLoopPairBaseStore,
        decodeLoopAppendStore] using h.runtime_module
    runtime_host := by
      simpa [finalStore, paired, appended, decodeInvalidCoreStore,
        decodeLoopPairInvalidStore, decodeLoopPairBaseStore,
        decodeLoopAppendStore] using h.runtime_host
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
      simp only [finalStore, decodeInvalidCoreStore]
      have hzero : 0 < paired.wasm.globals.globals.length := by
        apply (getElem?_eq_some_iff.mp (show
          paired.wasm.globals.globals[0]? = some (.i32 coreFrame) by
            change store.wasm.globals.globals[0]? = some (.i32 coreFrame)
            simpa only [globalAt?, canonicalGlobalIndex_zero] using h.global_eq)).1
      simpa only [globalAt?, canonicalGlobalIndex_zero] using
        (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
    status_capacity := preserve decodeStatusVector 0 h.status_capacity
      (by
        have hs : decodeStatusVector.toNat + 4 ≤ 1054000 := by decide
        exact hs.trans hptrLower) (by decide) (by decide) (by decide) (by decide)
    status_pointer := preserve (decodeStatusVector + 4) 1 h.status_pointer
      (by
        have hs : (decodeStatusVector + 4).toNat + 4 ≤ 1054000 := by decide
        exact hs.trans hptrLower) (by decide) (by decide) (by decide) (by decide)
    status_length := preserve (decodeStatusVector + 8) 0 h.status_length
      (by
        have hs : (decodeStatusVector + 8).toNat + 4 ≤ 1054000 := by decide
        exact hs.trans hptrLower) (by decide) (by decide) (by decide) (by decide)
    input_eq := by
      simpa [finalStore, paired, appended, decodeInvalidCoreStore,
        decodeLoopPairInvalidStore, decodeLoopPairBaseStore,
        decodeLoopAppendStore] using h.input_eq
    output_eq := by
      simpa [finalStore, paired, appended, decodeInvalidCoreStore,
        decodeLoopPairInvalidStore, decodeLoopPairBaseStore,
        decodeLoopAppendStore] using h.output_eq
    oom_eq := by
      simpa [finalStore, paired, appended, decodeInvalidCoreStore,
        decodeLoopPairInvalidStore, decodeLoopPairBaseStore,
        decodeLoopAppendStore] using h.oom_eq
    bump_eq := preserve 1053960 bump h.bump_eq
      (by
        have hs : (1053960 : UInt32).toNat + 4 ≤ 1054000 := by decide
        exact hs.trans hptrLower) (by decide) (by decide) (by decide) (by decide)
    bump_zero_or_lower := Or.inr (by
      have hd := h.data_lower
      have hp := h.input_before_output
      have he := h.output_end
      omega)
    bump_signed := h.bump_signed }

theorem DecodeLoopInv.appended_pair_reads
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending hi lo : UInt8}
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending) :
    let appended := decodeLoopAppendStore store ptr outLen pending
    let inputPtr := data + UInt32.ofNat consumed.length
    appended.wasm.mem.read8 inputPtr = hi ∧
      appended.wasm.mem.read8 (inputPtr + 1) = lo := by
  dsimp only
  let inputPtr := data + UInt32.ofNat consumed.length
  have hp := h.input_pair_reads
  have hinputPtrNat : inputPtr.toNat = data.toNat + consumed.length :=
    h.iteratorPointer_toNat
  have hptrLower : 1054000 ≤ ptr.toNat := by
    have hb := h.input_before_output
    have hd := h.data_lower
    omega
  have hinputPtr : inputPtr.toNat < ptr.toNat := by
    rw [hinputPtrNat]
    have hc := h.input_capacity
    have hs : consumed.length + 2 ≤ input.length := by
      rw [h.input_split, List.length_append]
      simp
    have hb := h.input_before_output
    omega
  have hinputPairEnd : inputPtr.toNat + 2 ≤ ptr.toNat := by
    rw [hinputPtrNat]
    have hs : consumed.length + 2 ≤ input.length := by
      rw [h.input_split, List.length_append]
      simp
    have hc := h.input_capacity
    have hb := h.input_before_output
    omega
  have hinputPtr1 : (inputPtr + 1).toNat = inputPtr.toNat + 1 := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
    · simp
    · have hone : (1 : UInt32).toNat = 1 := by decide
      rw [hone]
      norm_num [UInt32.size] at ⊢
      have he := h.output_end
      have hb := h.bump_signed
      omega
  have hscratch : 1048504 ≤ inputPtr.toNat := by
    rw [hinputPtrNat]
    have hd := h.data_lower
    omega
  have hwrite0 : inputPtr.toNat ≠ (outLen + ptr).toNat := by
    rw [h.append_address]
    omega
  have hwrite1 : (inputPtr + 1).toNat ≠ (outLen + ptr).toNat := by
    rw [h.append_address, hinputPtr1]
    omega
  constructor
  · simp only [decodeLoopAppendStore]
    rw [Mem.read8_write32_disjoint_core]
    · simp only [Mem.read8, Mem.write8]
      rw [if_neg hwrite0]
      exact hp.1
    · exact Or.inr (by
        have ha : (coreFrame + 68).toNat + 4 = 1048504 := by decide
        rw [ha]
        exact hscratch)
  · simp only [decodeLoopAppendStore]
    rw [Mem.read8_write32_disjoint_core]
    · simp only [Mem.read8, Mem.write8]
      rw [if_neg hwrite1]
      exact hp.2
    · exact Or.inr (by
        have ha : (coreFrame + 68).toNat + 4 = 1048504 := by decide
        rw [ha, hinputPtr1]
        omega)

theorem decodeLoopPairInvalidStore_vector_fields
    (store : MachineStore Universal.State)
    (inputPtr remaining chunkIndex : UInt32) (bad : UInt8) (index : UInt32)
    (ptr capacity : UInt32)
    (hptr : store.wasm.mem.read32 (coreFrame + 64) = ptr)
    (hcapacity : store.wasm.mem.read32 (coreFrame + 60) = capacity) :
    (decodeLoopPairInvalidStore store inputPtr remaining chunkIndex bad index).wasm.mem.read32
        (coreFrame + 64) = ptr ∧
    (decodeLoopPairInvalidStore store inputPtr remaining chunkIndex bad index).wasm.mem.read32
        (coreFrame + 60) = capacity := by
  constructor
  all_goals simp only [decodeLoopPairInvalidStore, decodeLoopPairBaseStore]
  · rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint]
    · exact hptr
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  · rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint]
    · exact hcapacity
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem DecodeLoopInv.invalid_high_call_reaches
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed hi lo : UInt8}
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity) (hhi : hexValue hi = none)
    (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    let appended := decodeLoopAppendStore store ptr outLen pending
    let inputPtr := data + UInt32.ofNat consumed.length
    let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
    let chunkIndex := UInt32.ofNat (consumed.length / 2)
    let index := ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
      (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
    let paired := decodeLoopPairInvalidStore appended inputPtr remainingWord
      chunkIndex hi index
    let finalStore := decodeInvalidCoreStore paired (hi.toUInt32 &&& 255) index
    Reaches
      (decodeLoopCallConfig appended data inputLen ptr outLen seed pending
        returningInstance)
      (decodeAfterCoreConfig finalStore data) ∧
    DecodeCoreResult input data
      (decodeAfterCoreConfig finalStore data) := by
  dsimp only
  let appended := decodeLoopAppendStore store ptr outLen pending
  let inputPtr := data + UInt32.ofNat consumed.length
  let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
  let chunkIndex := UInt32.ofNat (consumed.length / 2)
  let index := ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
    (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
  let paired := decodeLoopPairInvalidStore appended inputPtr remainingWord
    chunkIndex hi index
  have hremainingNat : remainingWord.toNat = (hi :: lo :: rest).length :=
    h.remainingWord_toNat
  have hinputPtrNat : inputPtr.toNat = data.toNat + consumed.length :=
    h.iteratorPointer_toNat
  have hinputBound : inputPtr.toNat + 2 ≤
      appended.wasm.mem.pages * 65536 := by
    change inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536
    rw [hinputPtrNat]
    have hs : consumed.length + 2 ≤ input.length := by
      rw [h.input_split, List.length_append]
      simp
    have hc := h.input_capacity
    have hb := h.input_before_output
    have he := h.output_end
    have hp := h.output_bound
    omega
  have hremaining : appended.wasm.mem.read32 (loopIterator + 4) =
      remainingWord := by
    rw [h.appended_read32_scratch]
    · exact h.remaining_length
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 4).toNat + 4 = 1048512 := by decide
      rw [ha]
      omega
    · decide
  have herr : appended.wasm.mem.read32 (loopIterator + 16) = loopError := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_error
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 16).toNat + 4 = 1048524 := by decide
      rw [ha]
      omega
    · decide
  have hchunk : appended.wasm.mem.read32 (loopIterator + 8) = 2 := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_chunk
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 8).toNat + 4 = 1048516 := by decide
      rw [ha]
      omega
    · decide
  have hptrRead : appended.wasm.mem.read32 loopIterator = inputPtr := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_pointer
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : loopIterator.toNat + 4 = 1048508 := by decide
      rw [ha]
      omega
    · decide
  have hindexRead : appended.wasm.mem.read32 (loopIterator + 12) =
      chunkIndex := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_index
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 12).toNat + 4 = 1048520 := by decide
      rw [ha]
      omega
    · decide
  have hreads := h.appended_pair_reads
  have hpair := decode_loop_pair_invalid_high_exit appended data inputLen ptr
    outLen inputPtr remainingWord chunkIndex seed pending hi lo
    returningInstance h.runtime_module h.pages_lower h.pages_upper hinputBound
    (by rw [hinputPtrNat]; have hd := h.data_lower; omega) (by
      rw [hremainingNat]; simp) hremaining herr hchunk hptrRead hindexRead
    hreads.1 hreads.2 hhi
  have hv := decodeLoopPairInvalidStore_vector_fields appended inputPtr
    remainingWord chunkIndex hi index ptr capacity
    (h.appended_read32_scratch (by
      have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (coreFrame + 64).toNat + 4 = 1048500 := by decide
      rw [ha]; omega) (by decide) |>.trans h.vector_pointer)
    (h.appended_read32_scratch (by
      have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (coreFrame + 60).toNat + 4 = 1048496 := by decide
      rw [ha]; omega) (by decide) |>.trans h.vector_capacity)
  have hpost := decode_loop_exit_to_post paired data inputLen ptr capacity
    outLen seed hi returningInstance h.pages_lower hv.1 hv.2
  have hmarker : paired.wasm.mem.read32 coreError = hi.toUInt32 &&& 255 := by
    simp only [paired, decodeLoopPairInvalidStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_same]
    all_goals decide
  have hidx : paired.wasm.mem.read32 (coreError + 4) = index := by
    simp only [paired, decodeLoopPairInvalidStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
      Mem.read32_write32_disjoint, Mem.read32_write32_same]
    all_goals decide
  have hreturn' : returningInstance = paired.runtime.entry := by
    simpa [paired, appended, decodeLoopPairInvalidStore,
      decodeLoopPairBaseStore, decodeLoopAppendStore] using hreturn
  have hinvalid := decode_post_loop_invalid_reaches paired data inputLen ptr
    capacity (1 + outLen) (hi.toUInt32 &&& 255) index seed returningInstance
    h.runtime_module h.pages_lower (by
      change globalAt? store 0 = some (.i32 coreFrame); exact h.global_eq)
    hmarker (by
      intro heq
      have hle : (hi.toUInt32 &&& 255).toNat ≤ 255 := by
        simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
          UInt32.toNat_ofNat]
        exact Nat.and_le_right
      have hnat := congrArg UInt32.toNat heq
      have hlarge : (1114114 : UInt32).toNat = 1114114 := by
        norm_num [UInt32.toNat_ofNat]
      rw [hlarge] at hnat
      omega) hidx (by
      intro hz; have hc := h.capacity_pos; simp [hz] at hc) hreturn'
  constructor
  · exact hpair.trans (hpost.trans hinvalid)
  · right
    have hdecode : decode input = none := by
      rw [h.input_split]
      exact decode_append_invalid_high consumed rest (decoded ++ [pending]) hi lo
        h.consumed_even h.decoded_consumed hhi
    exact ⟨_, hi.toUInt32 &&& 255, rfl, hdecode,
      decodeInvalidCoreStore_result_tag _ _ _,
      decodeInvalidCoreStore_result_payload _ _ _,
      Or.inr ⟨h.input_even,
        by simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
          UInt32.toNat_ofNat]; exact Nat.and_le_right⟩,
      ⟨bump, h.invalid_core_facts inputPtr remainingWord chunkIndex hi index
        (hi.toUInt32 &&& 255)⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem DecodeLoopInv.invalid_low_call_reaches
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed hi lo : UInt8} (hiRoute : HexRoute)
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity) (hhi : hiRoute.valid hi)
    (hlo : hexValue lo = none)
    (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    let appended := decodeLoopAppendStore store ptr outLen pending
    let inputPtr := data + UInt32.ofNat consumed.length
    let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
    let chunkIndex := UInt32.ofNat (consumed.length / 2)
    let index := ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
      (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
    let paired := decodeLoopPairInvalidStore appended inputPtr remainingWord
      chunkIndex lo index
    let finalStore := decodeInvalidCoreStore paired (lo.toUInt32 &&& 255) index
    Reaches
      (decodeLoopCallConfig appended data inputLen ptr outLen seed pending
        returningInstance)
      (decodeAfterCoreConfig finalStore data) ∧
    DecodeCoreResult input data
      (decodeAfterCoreConfig finalStore data) := by
  dsimp only
  let appended := decodeLoopAppendStore store ptr outLen pending
  let inputPtr := data + UInt32.ofNat consumed.length
  let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
  let chunkIndex := UInt32.ofNat (consumed.length / 2)
  let index := ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
    (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
  let paired := decodeLoopPairInvalidStore appended inputPtr remainingWord
    chunkIndex lo index
  have hremainingNat : remainingWord.toNat = (hi :: lo :: rest).length :=
    h.remainingWord_toNat
  have hinputPtrNat : inputPtr.toNat = data.toNat + consumed.length :=
    h.iteratorPointer_toNat
  have hinputBound : inputPtr.toNat + 2 ≤
      appended.wasm.mem.pages * 65536 := by
    change inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536
    rw [hinputPtrNat]
    have hs : consumed.length + 2 ≤ input.length := by
      rw [h.input_split, List.length_append]
      simp
    have hc := h.input_capacity
    have hb := h.input_before_output
    have he := h.output_end
    have hp := h.output_bound
    omega
  have hremaining : appended.wasm.mem.read32 (loopIterator + 4) =
      remainingWord := by
    rw [h.appended_read32_scratch]
    · exact h.remaining_length
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 4).toNat + 4 = 1048512 := by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
      rw [ha]; omega
    · norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have herr : appended.wasm.mem.read32 (loopIterator + 16) = loopError := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_error
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 16).toNat + 4 = 1048524 := by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
      rw [ha]; omega
    · norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have hchunk : appended.wasm.mem.read32 (loopIterator + 8) = 2 := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_chunk
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 8).toNat + 4 = 1048516 := by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
      rw [ha]; omega
    · norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have hptrRead : appended.wasm.mem.read32 loopIterator = inputPtr := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_pointer
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : loopIterator.toNat + 4 = 1048508 := by
        norm_num [UInt32.toNat_ofNat]
      rw [ha]; omega
    · norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have hindexRead : appended.wasm.mem.read32 (loopIterator + 12) =
      chunkIndex := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_index
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 12).toNat + 4 = 1048520 := by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
      rw [ha]; omega
    · norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have hreads := h.appended_pair_reads
  have hpair := decode_loop_pair_invalid_low_exit appended data inputLen ptr
    outLen inputPtr remainingWord chunkIndex seed pending hi lo hiRoute
    returningInstance h.runtime_module h.pages_lower h.pages_upper hinputBound
    (by rw [hinputPtrNat]; have hd := h.data_lower; omega) (by
      rw [hremainingNat]; simp) hremaining herr hchunk hptrRead hindexRead
    hreads.1 hreads.2 hhi hlo
  have hv := decodeLoopPairInvalidStore_vector_fields appended inputPtr
    remainingWord chunkIndex lo index ptr capacity
    (h.appended_read32_scratch (by
      have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (coreFrame + 64).toNat + 4 = 1048500 := by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
      rw [ha]; omega) (by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size])
      |>.trans h.vector_pointer)
    (h.appended_read32_scratch (by
      have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (coreFrame + 60).toNat + 4 = 1048496 := by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
      rw [ha]; omega) (by
        norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size])
      |>.trans h.vector_capacity)
  have hpost := decode_loop_exit_to_post paired data inputLen ptr capacity
    outLen seed lo returningInstance h.pages_lower hv.1 hv.2
  have hmarker : paired.wasm.mem.read32 coreError = lo.toUInt32 &&& 255 := by
    simp only [paired, decodeLoopPairInvalidStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_same]
    all_goals
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have hidx : paired.wasm.mem.read32 (coreError + 4) = index := by
    simp only [paired, decodeLoopPairInvalidStore]
    rw [Mem.read32_write8_disjoint_loop, Mem.read32_write8_disjoint_loop,
      Mem.read32_write32_disjoint, Mem.read32_write32_same]
    all_goals
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.size]
  have hreturn' : returningInstance = paired.runtime.entry := by
    simpa [paired, appended, decodeLoopPairInvalidStore,
      decodeLoopPairBaseStore, decodeLoopAppendStore] using hreturn
  have hinvalid := decode_post_loop_invalid_reaches paired data inputLen ptr
    capacity (1 + outLen) (lo.toUInt32 &&& 255) index seed returningInstance
    h.runtime_module h.pages_lower (by
      change globalAt? store 0 = some (.i32 coreFrame); exact h.global_eq)
    hmarker (by
      intro heq
      have hle : (lo.toUInt32 &&& 255).toNat ≤ 255 := by
        simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
          UInt32.toNat_ofNat]
        exact Nat.and_le_right
      have hnat := congrArg UInt32.toNat heq
      have hlarge : (1114114 : UInt32).toNat = 1114114 := by
        norm_num [UInt32.toNat_ofNat]
      rw [hlarge] at hnat
      omega) hidx (by
      intro hz; have hc := h.capacity_pos; simp [hz] at hc) hreturn'
  constructor
  · exact hpair.trans (hpost.trans hinvalid)
  · right
    have hdecode : decode input = none := by
      rw [h.input_split]
      exact decode_append_invalid_low consumed rest (decoded ++ [pending]) hi lo
        (hiRoute.nibble hi).toNat h.consumed_even h.decoded_consumed
        (hexValue_of_route_valid hiRoute hi hhi) hlo
    exact ⟨_, lo.toUInt32 &&& 255, rfl, hdecode,
      decodeInvalidCoreStore_result_tag _ _ _,
      decodeInvalidCoreStore_result_payload _ _ _,
      Or.inr ⟨h.input_even,
        by simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
          UInt32.toNat_ofNat]; exact Nat.and_le_right⟩,
      ⟨bump, h.invalid_core_facts inputPtr remainingWord chunkIndex lo index
        (lo.toUInt32 &&& 255)⟩⟩

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.invalid_high_reachesOrOOM
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed hi lo : UInt8}
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hhi : hexValue hi = none) (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    ReachesOrOOM
      (decodeLoopHeadConfig store data inputLen ptr outLen seed pending
        returningInstance)
      (DecodeCoreResult input data) := by
  by_cases hfull : outLen = capacity
  · have hprefix := decode_loop_full_to_reserve store data inputLen ptr capacity
      outLen (UInt32.ofNat (hi :: lo :: rest).length) seed pending
      returningInstance h.pages_lower h.vector_capacity hfull h.iterator_error
      h.error_marker h.remaining_length h.iterator_chunk
    apply ReachesOrOOM.prependReaches hprefix
    apply (h.reserve_reachesOrOOM hfull returningInstance).bind
    intro middle hmiddle
    rcases hmiddle with ⟨allocStore, hfinish, hsuccess, rfl⟩
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
    have hreturn' : returningInstance = reserved.runtime.entry := by
      rw [hreturn]
      change store.runtime.entry = allocStore.runtime.entry
      rw [hsuccess.runtime_eq]
      rfl
    have hdone := hreserved.invalid_high_call_reaches (seed := seed) hspare
      hhi returningInstance hreturn'
    exact ReachesOrOOM.of_reaches hdone.1 hdone.2
  · have hprefix := decode_loop_append_no_grow store data inputLen ptr capacity
      outLen seed pending returningInstance h.pages_lower h.vector_capacity
      hfull (h.append_bound hfull)
    have hdone := h.invalid_high_call_reaches (seed := seed) hfull hhi
      returningInstance hreturn
    exact ReachesOrOOM.of_reaches (hprefix.trans hdone.1) hdone.2

set_option maxRecDepth 100000 in
theorem DecodeLoopInv.invalid_low_reachesOrOOM
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed hi lo : UInt8} (hiRoute : HexRoute)
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hhi : hiRoute.valid hi) (hlo : hexValue lo = none)
    (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    ReachesOrOOM
      (decodeLoopHeadConfig store data inputLen ptr outLen seed pending
        returningInstance)
      (DecodeCoreResult input data) := by
  by_cases hfull : outLen = capacity
  · have hprefix := decode_loop_full_to_reserve store data inputLen ptr capacity
      outLen (UInt32.ofNat (hi :: lo :: rest).length) seed pending
      returningInstance h.pages_lower h.vector_capacity hfull h.iterator_error
      h.error_marker h.remaining_length h.iterator_chunk
    apply ReachesOrOOM.prependReaches hprefix
    apply (h.reserve_reachesOrOOM hfull returningInstance).bind
    intro middle hmiddle
    rcases hmiddle with ⟨allocStore, hfinish, hsuccess, rfl⟩
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
    have hreturn' : returningInstance = reserved.runtime.entry := by
      rw [hreturn]
      change store.runtime.entry = allocStore.runtime.entry
      rw [hsuccess.runtime_eq]
      rfl
    have hdone := hreserved.invalid_low_call_reaches (seed := seed) hiRoute
      hspare hhi hlo returningInstance hreturn'
    exact ReachesOrOOM.of_reaches hdone.1 hdone.2
  · have hprefix := decode_loop_append_no_grow store data inputLen ptr capacity
      outLen seed pending returningInstance h.pages_lower h.vector_capacity
      hfull (h.append_bound hfull)
    have hdone := h.invalid_low_call_reaches (seed := seed) hiRoute hfull hhi
      hlo returningInstance hreturn
    exact ReachesOrOOM.of_reaches (hprefix.trans hdone.1) hdone.2

end Project.HexDecodeStdio
