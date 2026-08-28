import HexDecodeStdio.DecodeLoopInvariant

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem Mem.readBytes_write8_append (m : Mem) (off len : Nat)
    (bytes : List UInt8) (addr : UInt32) (value : UInt8)
    (haddr : addr.toNat = off + len)
    (hbytes : m.readBytes off len = bytes)
    (hlen : bytes.length = len) :
    (m.write8 addr value).readBytes off (len + 1) = bytes ++ [value] := by
  apply List.ext_getElem
  · simp [Mem.readBytes, hlen]
  · intro i hleft hright
    have hi : i < len + 1 := by simpa [Mem.readBytes] using hleft
    by_cases hprefix : i < len
    · have hprefix' : i < bytes.length := by simpa [hlen] using hprefix
      rw [List.getElem_append_left hprefix']
      have holdAt := congrArg (fun xs => xs[i]?) hbytes
      simp only [Mem.readBytes, List.getElem?_map, List.getElem?_range,
        hprefix, ↓reduceDIte, Option.map_some] at holdAt
      rw [List.getElem?_eq_getElem hprefix'] at holdAt
      simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
        Mem.write8]
      rw [if_neg (by omega)]
      exact Option.some.inj holdAt
    · have hieq : i = len := by omega
      subst i
      simpa [Mem.readBytes, Mem.write8, haddr, ← hlen]

theorem DecodeLoopInv.append_address
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    (outLen + ptr).toNat = ptr.toNat + decoded.length := by
  have hsum : outLen.toNat + ptr.toNat < 2 ^ 32 := by
    have he := h.output_end
    have hb := h.bump_signed
    have hf := h.output_fits
    norm_num [UInt32.size] at hb ⊢
    omega
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt hsum, h.output_length]
  omega

theorem DecodeLoopInv.appended_output
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    (decodeLoopAppendStore store ptr outLen pending).wasm.mem.readBytes
        ptr.toNat (decoded.length + 1) = decoded ++ [pending] := by
  simp only [decodeLoopAppendStore]
  rw [Mem.readBytes_write32_disjoint]
  · apply Mem.readBytes_write8_append
      store.wasm.mem ptr.toNat decoded.length decoded
      (outLen + ptr) pending
    · simpa [UInt32.add_comm] using h.append_address
    · exact h.output_bytes
    · rfl
  · right
    have hp := h.input_before_output
    have hd := h.data_lower
    change 1048504 ≤ ptr.toNat
    omega

theorem DecodeLoopInv.appended_input
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    (decodeLoopAppendStore store ptr outLen pending).wasm.mem.readBytes
        data.toNat input.length = input := by
  simp only [decodeLoopAppendStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint]
  · exact h.input_bytes
  · left
    have hc := h.input_capacity
    have hp := h.input_before_output
    have ha := h.append_address
    omega
  · right
    have hd := h.data_lower
    change 1048504 ≤ data.toNat
    omega

theorem decodeLoopPairValidStore_readBytes_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8)
    (off count : Nat) (habove : 1048520 ≤ off) :
    (decodeLoopPairValidStore store inputPtr len chunkIndex byte).wasm.mem.readBytes
        off count = store.wasm.mem.readBytes off count := by
  simp only [decodeLoopPairValidStore, decodeLoopPairBaseStore]
  rw [Mem.readBytes_write8_disjoint, Mem.readBytes_write8_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  · right
    have he : (loopIterator + 4).toNat + 4 = 1048512 := by decide
    omega
  · right
    have he : loopIterator.toNat + 4 = 1048508 := by decide
    omega
  · right
    have he : (loopIterator + 12).toNat + 4 = 1048520 := by decide
    omega
  · right
    have he : (loopPairOut + 1).toNat + 1 = 1048442 := by decide
    omega
  · right
    have he : loopPairOut.toNat + 1 = 1048441 := by decide
    omega

theorem decodeLoopPairEmptyStore_readBytes_above
    (store : MachineStore Universal.State) (off count : Nat)
    (habove : 1048442 ≤ off) :
    (decodeLoopPairEmptyStore store).wasm.mem.readBytes off count =
      store.wasm.mem.readBytes off count := by
  simp only [decodeLoopPairEmptyStore]
  rw [Mem.readBytes_write8_disjoint, Mem.readBytes_write8_disjoint]
  · right
    have he : (loopPairOut + 1).toNat + 1 = 1048442 := by decide
    omega
  · right
    have he : loopPairOut.toNat + 1 = 1048441 := by decide
    omega

theorem Mem.read32_write8_disjoint_loop (m : Mem)
    (writeAddr readAddr : UInt32) (value : UInt8)
    (h : readAddr.toNat + 4 ≤ writeAddr.toNat ∨
      writeAddr.toNat + 1 ≤ readAddr.toNat) :
    (m.write8 writeAddr value).read32 readAddr = m.read32 readAddr := by
  simp only [Mem.read32, Mem.write8]
  rw [if_neg, if_neg, if_neg, if_neg]
  all_goals rcases h with hbefore | hafter <;> omega

theorem DecodeLoopInv.appended_read32_scratch
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump addr : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (haddr : addr.toNat + 4 ≤ ptr.toNat)
    (hmeta : addr.toNat + 4 ≤ (coreFrame + 68).toNat ∨
      (coreFrame + 68).toNat + 4 ≤ addr.toNat) :
    (decodeLoopAppendStore store ptr outLen pending).wasm.mem.read32 addr =
      store.wasm.mem.read32 addr := by
  simp only [decodeLoopAppendStore]
  rw [Mem.read32_write32_disjoint _ _ _ _ hmeta]
  apply Mem.read32_write8_disjoint_loop
  left
  have ha := h.append_address
  omega

theorem DecodeLoopInv.appended_vector_length
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    (decodeLoopAppendStore store ptr outLen pending).wasm.mem.read32
        (coreFrame + 68) = 1 + outLen := by
  simp only [decodeLoopAppendStore]
  exact Mem.read32_write32_same _ _ _

theorem decodeLoopPairValidStore_read32_unchanged
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) (addr : UInt32)
    (hlen : addr.toNat + 4 ≤ (loopIterator + 4).toNat ∨
      (loopIterator + 4).toNat + 4 ≤ addr.toNat)
    (hptr : addr.toNat + 4 ≤ loopIterator.toNat ∨
      loopIterator.toNat + 4 ≤ addr.toNat)
    (hindex : addr.toNat + 4 ≤ (loopIterator + 12).toNat ∨
      (loopIterator + 12).toNat + 4 ≤ addr.toNat)
    (hpayload : addr.toNat + 4 ≤ (loopPairOut + 1).toNat ∨
      (loopPairOut + 1).toNat + 1 ≤ addr.toNat)
    (htag : addr.toNat + 4 ≤ loopPairOut.toNat ∨
      loopPairOut.toNat + 1 ≤ addr.toNat) :
    (decodeLoopPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [decodeLoopPairValidStore, decodeLoopPairBaseStore]
  rw [Mem.read32_write8_disjoint_loop _ _ _ _ htag,
    Mem.read32_write8_disjoint_loop _ _ _ _ hpayload,
    Mem.read32_write32_disjoint _ _ _ _ hindex,
    Mem.read32_write32_disjoint _ _ _ _ hptr,
    Mem.read32_write32_disjoint _ _ _ _ hlen]

theorem decodeLoopPairValidStore_remaining
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    (decodeLoopPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        (loopIterator + 4) = len - 2 := by
  simp [decodeLoopPairValidStore, decodeLoopPairBaseStore, Mem.read32,
    Mem.write32, Mem.write8]
  bv_decide

theorem decodeLoopPairValidStore_pointer
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    (decodeLoopPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        loopIterator = 2 + inputPtr := by
  simp [decodeLoopPairValidStore, decodeLoopPairBaseStore, Mem.read32,
    Mem.write32, Mem.write8]
  bv_decide

theorem decodeLoopPairValidStore_index
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    (decodeLoopPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        (loopIterator + 12) = 1 + chunkIndex := by
  simp [decodeLoopPairValidStore, decodeLoopPairBaseStore, Mem.read32,
    Mem.write32, Mem.write8]
  bv_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem DecodeLoopInv.after_valid_pair_no_grow
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending hi lo : UInt8} (hiRoute loRoute : HexRoute)
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity)
    (hhi : hiRoute.valid hi) (hlo : loRoute.valid lo) :
    let appended := decodeLoopAppendStore store ptr outLen pending
    let inputPtr := data + UInt32.ofNat consumed.length
    let remainingWord := UInt32.ofNat (hi :: lo :: rest).length
    let chunkIndex := UInt32.ofNat (consumed.length / 2)
    let next := (loRoute.nibble lo).toUInt8 |||
      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
    let paired := decodeLoopPairValidStore appended inputPtr remainingWord
      chunkIndex next
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
  have hhiValue := hexValue_of_route_valid hiRoute hi hhi
  have hloValue := hexValue_of_route_valid loRoute lo hlo
  have hhiLt := hexValue_some_lt hi _ hhiValue
  have hloLt := hexValue_some_lt lo _ hloValue
  have hnext : next = UInt8.ofNat
      (16 * (hiRoute.nibble hi).toNat + (loRoute.nibble lo).toNat) := by
    simpa [next] using route_pair_byte hi lo
      (hiRoute.nibble hi).toNat (loRoute.nibble lo).toNat hiRoute loRoute
      rfl rfl hhiLt hloLt
  have hcombine :
      16 * (hiRoute.nibble hi).toUInt8 + (loRoute.nibble lo).toUInt8 =
        next := by
    rw [hnext]
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_ofNat]
    have hhiNat : (hiRoute.nibble hi).toUInt8.toNat =
        (hiRoute.nibble hi).toNat := by
      rw [UInt32.toUInt8_toNat, Nat.mod_eq_of_lt (by omega)]
    have hloNat : (loRoute.nibble lo).toUInt8.toNat =
        (loRoute.nibble lo).toNat := by
      rw [UInt32.toUInt8_toNat, Nat.mod_eq_of_lt (by omega)]
    rw [hhiNat, hloNat]
    norm_num
  have hpairDecode : decode [hi, lo] = some [next] := by
    simpa [decode, hhiValue, hloValue] using
      congrArg (fun byte : UInt8 => some [byte]) hnext.symm
  have hremainingNat : remainingWord.toNat =
      (hi :: lo :: rest).length := by
    simpa only [remainingWord] using h.remainingWord_toNat
  have hremainingSub : remainingWord - 2 = UInt32.ofNat rest.length := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le]
    · rw [hremainingNat]
      rw [UInt32.toNat_ofNat_of_lt']
      · simp
      · have hs := h.input_small
        rw [h.input_split, List.length_append] at hs
        norm_num [UInt32.size] at hs ⊢
        omega
    · apply UInt32.le_iff_toNat_le.mpr
      rw [hremainingNat]
      have htwo : (2 : UInt32).toNat = 2 := by decide
      rw [htwo]
      simp
  have hindexNext : 1 + chunkIndex =
      UInt32.ofNat ((consumed ++ [hi, lo]).length / 2) := by
    have heq : (consumed ++ [hi, lo]).length / 2 =
        consumed.length / 2 + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add]
      omega
    rw [heq, UInt32.ofNat_add]
    simp [chunkIndex, UInt32.add_comm]
  have hnextLength : (1 + outLen).toNat = (decoded ++ [pending]).length := by
    have hlt : outLen.toNat < capacity.toNat := by
      apply lt_of_le_of_ne h.output_fits
      intro heq
      exact hspare (UInt32.toNat_inj.mp heq)
    have hc : capacity.toNat < 2 ^ 31 := by
      have he := h.output_end
      have hb := h.bump_signed
      omega
    have hsum : (1 : UInt32).toNat + outLen.toNat < 2 ^ 32 := by
      have hone : (1 : UInt32).toNat = 1 := by decide
      rw [hone]
      norm_num at hc ⊢
      omega
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt hsum]
    simp [h.output_length, Nat.add_comm]
  have hptrLower : 1054000 ≤ ptr.toNat := by
    exact le_trans h.data_lower (le_trans (Nat.le_add_right _ _)
      h.input_before_output)
  have hscratch (addr : UInt32) (hb : addr.toNat + 4 ≤ 1054000) :
      addr.toNat + 4 ≤ ptr.toNat := le_trans hb hptrLower
  refine
    { input_split := ?_
      input_even := h.input_even
      consumed_even := ?_
      decoded_consumed := ?_
      input_length := h.input_length
      remaining_length := ?_
      iterator_error := ?_
      iterator_chunk := ?_
      iterator_pointer := ?_
      iterator_index := ?_
      error_marker := ?_
      input_bytes := ?_
      input_capacity := h.input_capacity
      input_before_output := h.input_before_output
      data_lower := h.data_lower
      vector_capacity := ?_
      vector_pointer := ?_
      vector_length := ?_
      output_bytes := ?_
      output_length := hnextLength
      output_fits := ?_
      capacity_pos := h.capacity_pos
      capacity_min := h.capacity_min
      output_end := h.output_end
      output_bound := ?_
      bump_eq := ?_
      bump_signed := h.bump_signed
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
  · simpa [List.append_assoc] using h.input_split
  · simpa [List.length_append, Nat.add_mod] using h.consumed_even
  · rw [decode_append_even consumed [hi, lo] h.consumed_even,
      h.decoded_consumed, hpairDecode]
    simp only [Option.bind_some, Option.map_some]
    simp [List.append_assoc]
    rfl
  · rw [decodeLoopPairValidStore_remaining]
    exact hremainingSub
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.iterator_error
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.iterator_chunk
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_pointer]
    simp [inputPtr, List.length_append, UInt32.ofNat_add]
    ac_rfl
  · rw [decodeLoopPairValidStore_index]
    exact hindexNext
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.error_marker
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_readBytes_above]
    · exact h.appended_input
    · exact le_trans (by decide) h.data_lower
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.vector_capacity
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.vector_pointer
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · exact h.appended_vector_length
    all_goals decide
  · rw [decodeLoopPairValidStore_readBytes_above]
    · simpa using h.appended_output
    · have hp := h.input_before_output
      have hd := h.data_lower
      omega
  · rw [hnextLength]
    have hlt : outLen.toNat < capacity.toNat := by
      apply lt_of_le_of_ne h.output_fits
      intro heq
      exact hspare (UInt32.toNat_inj.mp heq)
    have hs : decoded.length + 1 ≤ capacity.toNat := by
      rw [← h.output_length]
      omega
    simpa using hs
  · change bump.toNat ≤ store.wasm.mem.pages * 65536
    exact h.output_bound
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.bump_eq
      · apply hscratch
        decide
      · decide
    all_goals decide
  · change store.runtime.currentModule = «module»
    exact h.runtime_module
  · change store.runtime.currentHost = Universal.envFor «module»
    exact h.runtime_host
  · change store.wasm.memoryCap store.runtime.currentModule 0 = 65536
    exact h.memory_cap
  · change 17 ≤ store.wasm.mem.pages
    exact h.pages_lower
  · change store.wasm.mem.pages ≤ 65536
    exact h.pages_upper
  · change globalAt? store 0 = some (.i32 coreFrame)
    exact h.global_eq
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.status_capacity
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.status_pointer
      · apply hscratch
        decide
      · decide
    all_goals decide
  · rw [decodeLoopPairValidStore_read32_unchanged]
    · rw [h.appended_read32_scratch]
      · exact h.status_length
      · apply hscratch
        decide
      · decide
    all_goals decide
  · change store.wasm.host.stdio.input = []
    exact h.input_eq
  · change store.wasm.host.stdio.output = []
    exact h.output_eq
  · change store.wasm.host.oom.raised = false
    exact h.oom_eq

end Project.HexDecodeStdio
