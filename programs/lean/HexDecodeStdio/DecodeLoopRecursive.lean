import HexDecodeStdio.DecodeLoopInvalid

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem DecodeLoopInv.valid_call_step
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed hi lo : UInt8} (hiRoute loRoute : HexRoute)
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity) (hhi : hiRoute.valid hi)
    (hlo : loRoute.valid lo) (returningInstance : ModuleInstanceId) :
    let appended := decodeLoopAppendStore store ptr outLen pending
    let inputPtr := data + UInt32.ofNat consumed.length
    let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
    let chunkIndex := UInt32.ofNat (consumed.length / 2)
    let next := (loRoute.nibble lo).toUInt8 |||
      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
    let paired := decodeLoopPairValidStore appended inputPtr remainingWord
      chunkIndex next
    Reaches
      (decodeLoopCallConfig appended data inputLen ptr outLen seed pending
        returningInstance)
      (decodeLoopHeadConfig paired data inputLen ptr (1 + outLen) seed next
        returningInstance) ∧
    DecodeLoopInv input (consumed ++ [hi, lo]) rest (decoded ++ [pending])
      paired inputCapacity data inputLen ptr capacity (1 + outLen) bump next := by
  dsimp only
  let appended := decodeLoopAppendStore store ptr outLen pending
  let inputPtr := data + UInt32.ofNat consumed.length
  let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
  let chunkIndex := UInt32.ofNat (consumed.length / 2)
  let next := (loRoute.nibble lo).toUInt8 |||
    ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
  let paired := decodeLoopPairValidStore appended inputPtr remainingWord
    chunkIndex next
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
      rw [ha]; omega
    · decide
  have herr : appended.wasm.mem.read32 (loopIterator + 16) = loopError := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_error
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 16).toNat + 4 = 1048524 := by decide
      rw [ha]; omega
    · decide
  have hchunk : appended.wasm.mem.read32 (loopIterator + 8) = 2 := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_chunk
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 8).toNat + 4 = 1048516 := by decide
      rw [ha]; omega
    · decide
  have hptrRead : appended.wasm.mem.read32 loopIterator = inputPtr := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_pointer
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : loopIterator.toNat + 4 = 1048508 := by decide
      rw [ha]; omega
    · decide
  have hindexRead : appended.wasm.mem.read32 (loopIterator + 12) =
      chunkIndex := by
    rw [h.appended_read32_scratch]
    · exact h.iterator_index
    · have hp := h.input_before_output
      have hd := h.data_lower
      have ha : (loopIterator + 12).toNat + 4 = 1048520 := by decide
      rw [ha]; omega
    · decide
  have hreads := h.appended_pair_reads
  constructor
  · exact decode_loop_pair_valid_next appended data inputLen ptr outLen inputPtr
      remainingWord chunkIndex seed pending hi lo hiRoute loRoute
      returningInstance h.runtime_module h.pages_lower h.pages_upper hinputBound
      (by rw [hinputPtrNat]; have hd := h.data_lower; omega) (by
        rw [hremainingNat]; simp) hremaining herr hchunk hptrRead hindexRead
      hreads.1 hreads.2 hhi hlo
  · exact h.after_valid_pair_no_grow hiRoute loRoute hspare hhi hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem DecodeLoopInv.outcome
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending seed : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (returningInstance : ModuleInstanceId)
    (hreturn : returningInstance = store.runtime.entry) :
    ReachesOrOOM
      (decodeLoopHeadConfig store data inputLen ptr outLen seed pending
        returningInstance)
      (DecodeCoreResult input data) := by
  induction remaining using List.twoStepInduction generalizing consumed decoded
      store ptr capacity outLen bump pending with
  | nil =>
      exact h.empty_reachesOrOOM (seed := seed) returningInstance hreturn
  | singleton byte =>
      have heven := h.remaining_even
      simp at heven
  | cons_cons hi lo rest ih =>
      cases hhiValue : hexValue hi with
      | none =>
          exact h.invalid_high_reachesOrOOM hhiValue returningInstance hreturn
      | some hiNibble =>
          obtain ⟨hiRoute, hhi, _⟩ := hexValue_some_route hi hiNibble hhiValue
          cases hloValue : hexValue lo with
          | none =>
              exact h.invalid_low_reachesOrOOM hiRoute hhi hloValue
                returningInstance hreturn
          | some loNibble =>
              obtain ⟨loRoute, hlo, _⟩ :=
                hexValue_some_route lo loNibble hloValue
              by_cases hfull : outLen = capacity
              · have hprefix := decode_loop_full_to_reserve store data inputLen
                  ptr capacity outLen (UInt32.ofNat (hi :: lo :: rest).length)
                  seed pending returningInstance h.pages_lower h.vector_capacity
                  hfull h.iterator_error h.error_marker h.remaining_length
                  h.iterator_chunk
                apply ReachesOrOOM.prependReaches hprefix
                apply (h.reserve_reachesOrOOM hfull returningInstance).bind
                intro middle hmiddle
                rcases hmiddle with ⟨allocStore, hfinish, hsuccess, rfl⟩
                let newCapacity := reserveNewCapacity outLen 1 capacity
                let newPtr := allocatorPtr bump 1
                let newBump := allocatorFinish newCapacity 1 bump
                let reserved := decodeLoopReservedStore allocStore bump newCapacity
                have hreserved : DecodeLoopInv input consumed
                    (hi :: lo :: rest) decoded reserved inputCapacity data
                    inputLen newPtr newCapacity outLen newBump pending :=
                  h.after_reserve hfull hfinish hsuccess
                have hspare : outLen ≠ newCapacity := by
                  intro heq
                  have hn := congrArg UInt32.toNat heq
                  change outLen.toNat =
                    (reserveNewCapacity outLen 1 capacity).toNat at hn
                  rw [h.reserve_new_capacity_toNat hfull, hfull] at hn
                  have hc := h.capacity_pos
                  omega
                have hstep := hreserved.valid_call_step (seed := seed)
                  hiRoute loRoute hspare hhi hlo returningInstance
                apply ReachesOrOOM.prependReaches hstep.1
                have hreturn' : returningInstance =
                    (decodeLoopPairValidStore
                      (decodeLoopAppendStore reserved newPtr outLen pending)
                      (data + UInt32.ofNat consumed.length)
                      (UInt32.ofNat (hi :: lo :: rest).length)
                      (UInt32.ofNat (consumed.length / 2))
                      ((loRoute.nibble lo).toUInt8 |||
                        ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8)))).runtime.entry := by
                  rw [hreturn]
                  change store.runtime.entry = allocStore.runtime.entry
                  rw [hsuccess.runtime_eq]
                  rfl
                exact ih hstep.2 hreturn'
              · have hprefix := decode_loop_append_no_grow store data inputLen
                  ptr capacity outLen seed pending returningInstance h.pages_lower
                  h.vector_capacity hfull (h.append_bound hfull)
                have hstep := h.valid_call_step (seed := seed) hiRoute loRoute
                  hfull hhi hlo returningInstance
                apply ReachesOrOOM.prependReaches (hprefix.trans hstep.1)
                have hreturn' : returningInstance =
                    (decodeLoopPairValidStore
                      (decodeLoopAppendStore store ptr outLen pending)
                      (data + UInt32.ofNat consumed.length)
                      (UInt32.ofNat (hi :: lo :: rest).length)
                      (UInt32.ofNat (consumed.length / 2))
                      ((loRoute.nibble lo).toUInt8 |||
                        ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8)))).runtime.entry := by
                  simpa [decodeLoopPairValidStore, decodeLoopPairBaseStore,
                    decodeLoopAppendStore] using hreturn
                exact ih hstep.2 hreturn'

end Project.HexDecodeStdio
