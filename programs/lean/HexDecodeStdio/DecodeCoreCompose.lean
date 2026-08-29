import HexDecodeStdio.DecodeLoopRecursive

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem decodeEvenPreparedStore_readBytes_above
    (store : MachineStore Universal.State) (data len : UInt32)
    (off count : Nat) (habove : 1048492 ≤ off) :
    (decodeEvenPreparedStore store data len).wasm.mem.readBytes off count =
      store.wasm.mem.readBytes off count := by
  have h32 : coreError.toNat + 4 = 1048468 := by decide
  have h40 : (coreFrame + 40).toNat + 4 = 1048476 := by decide
  have h44 : (coreFrame + 44).toNat + 4 = 1048480 := by decide
  have h48 : (coreFrame + 48).toNat + 8 = 1048488 := by decide
  have h56 : (coreFrame + 56).toNat + 4 = 1048492 := by decide
  simp only [decodeEvenPreparedStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write64_disjoint,
    Mem.readBytes_write32_disjoint]
  all_goals right
  all_goals simp only [h32, h40, h44, h48, h56]
  all_goals omega

theorem decodePairValidStore_readBytes_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8)
    (off count : Nat) (habove : 1048488 ≤ off) :
    (decodePairValidStore store inputPtr len chunkIndex byte).wasm.mem.readBytes
      off count = store.wasm.mem.readBytes off count := by
  have hlen : (coreIterator + 4).toNat + 4 = 1048480 := by decide
  have hptr : coreIterator.toNat + 4 = 1048476 := by decide
  have hindex : (coreIterator + 12).toNat + 4 = 1048488 := by decide
  have hpayload : (corePairOut + 1).toNat + 1 = 1048458 := by decide
  have htag : corePairOut.toNat + 1 = 1048457 := by decide
  simp only [decodePairValidStore, decodePairBaseStore]
  rw [Mem.readBytes_write8_disjoint, Mem.readBytes_write8_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  all_goals right
  all_goals simp only [hlen, hptr, hindex, hpayload, htag]
  all_goals omega

theorem decodeInitialVectorStore_readBytes_between
    (store : MachineStore Universal.State) (ptr : UInt32) (byte : UInt8)
    (off count : Nat) (habove : 1048528 ≤ off)
    (hbefore : off + count ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr byte).wasm.mem.readBytes off count =
      store.wasm.mem.readBytes off count := by
  have h68 : (coreFrame + 68).toNat + 4 = 1048504 := by decide
  have h64 : (coreFrame + 64).toNat + 4 = 1048500 := by decide
  have h60 : (coreFrame + 60).toNat + 4 = 1048496 := by decide
  have h88 : (coreFrame + 88).toNat + 4 = 1048524 := by decide
  have h80 : (coreFrame + 80).toNat + 8 = 1048520 := by decide
  have h72 : (coreFrame + 72).toNat + 8 = 1048512 := by decide
  simp only [decodeInitialVectorStore]
  rw [Mem.readBytes_write64_disjoint, Mem.readBytes_write64_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write8_disjoint]
  all_goals try { simp only [h68, h64, h60, h88, h80, h72] }
  all_goals omega

theorem decodeInitialVectorStore_output
    (store : MachineStore Universal.State) (ptr : UInt32) (byte : UInt8)
    (hlower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr byte).wasm.mem.readBytes ptr.toNat 1 =
      [byte] := by
  have h68 : (coreFrame + 68).toNat + 4 = 1048504 := by decide
  have h64 : (coreFrame + 64).toNat + 4 = 1048500 := by decide
  have h60 : (coreFrame + 60).toNat + 4 = 1048496 := by decide
  have h88 : (coreFrame + 88).toNat + 4 = 1048524 := by decide
  have h80 : (coreFrame + 80).toNat + 8 = 1048520 := by decide
  have h72 : (coreFrame + 72).toNat + 8 = 1048512 := by decide
  simp only [decodeInitialVectorStore]
  rw [Mem.readBytes_write64_disjoint, Mem.readBytes_write64_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint]
  all_goals try { simp only [h68, h64, h60, h88, h80, h72] }
  all_goals try { right; omega }
  exact Mem.readBytes_write8_append store.wasm.mem ptr.toNat 0 [] ptr byte
    (by simp) (by simp [Mem.readBytes]) rfl

theorem decodeSecondPairValidStore_readBytes_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8)
    (off count : Nat) (habove : 1048520 ≤ off) :
    (decodeSecondPairValidStore store inputPtr len chunkIndex byte).wasm.mem.readBytes
      off count = store.wasm.mem.readBytes off count := by
  have hlen : (secondIterator + 4).toNat + 4 = 1048512 := by decide
  have hptr : secondIterator.toNat + 4 = 1048508 := by decide
  have hindex : (secondIterator + 12).toNat + 4 = 1048520 := by decide
  have hpayload : (secondPairOut + 1).toNat + 1 = 1048450 := by decide
  have htag : secondPairOut.toNat + 1 = 1048449 := by decide
  simp only [decodeSecondPairValidStore, decodeSecondPairBaseStore]
  rw [Mem.readBytes_write8_disjoint, Mem.readBytes_write8_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  all_goals right
  all_goals simp only [hlen, hptr, hindex, hpayload, htag]
  all_goals omega

theorem decodeEvenPreparedStore_read32_above
    (store : MachineStore Universal.State) (data len addr : UInt32)
    (habove : 1048492 ≤ addr.toNat) :
    (decodeEvenPreparedStore store data len).wasm.mem.read32 addr =
      store.wasm.mem.read32 addr := by
  simp only [decodeEvenPreparedStore]
  rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_disjoint]
  all_goals right
  all_goals exact le_trans (by decide) habove

theorem decodePairValidStore_read32_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) (addr : UInt32)
    (habove : 1048488 ≤ addr.toNat) :
    (decodePairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [decodePairValidStore, decodePairBaseStore]
  rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint]
  all_goals right
  all_goals exact le_trans (by decide) habove

theorem decodeInitialVectorStore_read32_between
    (store : MachineStore Universal.State) (ptr : UInt32) (byte : UInt8)
    (addr : UInt32) (habove : 1048528 ≤ addr.toNat)
    (hbefore : addr.toNat + 4 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr byte).wasm.mem.read32 addr =
      store.wasm.mem.read32 addr := by
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write8_disjoint]
  · exact Or.inl hbefore
  all_goals right
  all_goals exact le_trans (by decide) habove

theorem decodeInitialVectorStore_capacity_field
    (store : MachineStore Universal.State) (ptr : UInt32) (byte : UInt8) :
    (decodeInitialVectorStore store ptr byte).wasm.mem.read32
        (coreFrame + 60) = 8 := by
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_same]
  all_goals decide

theorem decodeInitialVectorStore_pointer_field
    (store : MachineStore Universal.State) (ptr : UInt32) (byte : UInt8) :
    (decodeInitialVectorStore store ptr byte).wasm.mem.read32
        (coreFrame + 64) = ptr := by
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_same]
  all_goals decide

theorem decodeInitialVectorStore_length_field
    (store : MachineStore Universal.State) (ptr : UInt32) (byte : UInt8) :
    (decodeInitialVectorStore store ptr byte).wasm.mem.read32
        (coreFrame + 68) = 1 := by
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_same]
  all_goals decide

theorem decodeSecondPairValidStore_read32_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) (addr : UInt32)
    (habove : 1048520 ≤ addr.toNat) :
    (decodeSecondPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [decodeSecondPairValidStore, decodeSecondPairBaseStore]
  rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint]
  all_goals right
  all_goals exact le_trans (by decide) habove

theorem decodeSecondPairInvalidStore_read32_above
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (bad : UInt8) (index addr : UInt32)
    (habove : 1048528 ≤ addr.toNat) :
    (decodeSecondPairInvalidStore store inputPtr len chunkIndex bad index).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [decodeSecondPairInvalidStore]
  rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint]
  all_goals right
  all_goals exact le_trans (by decide) habove

theorem decodeSecondPairValidStore_read32_unchanged
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) (addr : UInt32)
    (hlen : addr.toNat + 4 ≤ (secondIterator + 4).toNat ∨
      (secondIterator + 4).toNat + 4 ≤ addr.toNat)
    (hptr : addr.toNat + 4 ≤ secondIterator.toNat ∨
      secondIterator.toNat + 4 ≤ addr.toNat)
    (hindex : addr.toNat + 4 ≤ (secondIterator + 12).toNat ∨
      (secondIterator + 12).toNat + 4 ≤ addr.toNat)
    (hpayload : addr.toNat + 4 ≤ (secondPairOut + 1).toNat ∨
      (secondPairOut + 1).toNat + 1 ≤ addr.toNat)
    (htag : addr.toNat + 4 ≤ secondPairOut.toNat ∨
      secondPairOut.toNat + 1 ≤ addr.toNat) :
    (decodeSecondPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [decodeSecondPairValidStore, decodeSecondPairBaseStore]
  rw [Mem.read32_write8_disjoint _ _ _ _ htag,
    Mem.read32_write8_disjoint _ _ _ _ hpayload,
    Mem.read32_write32_disjoint _ _ _ _ hindex,
    Mem.read32_write32_disjoint _ _ _ _ hptr,
    Mem.read32_write32_disjoint _ _ _ _ hlen]

theorem decodeSecondPairValidStore_remaining_field
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    (decodeSecondPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        (secondIterator + 4) = len - 2 := by
  simp only [decodeSecondPairValidStore, decodeSecondPairBaseStore]
  rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_same]
  all_goals decide

theorem decodeSecondPairValidStore_pointer_field
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    (decodeSecondPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        secondIterator = 2 + inputPtr := by
  simp only [decodeSecondPairValidStore, decodeSecondPairBaseStore]
  rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_same]
  all_goals decide

theorem decodeSecondPairValidStore_index_field
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    (decodeSecondPairValidStore store inputPtr len chunkIndex byte).wasm.mem.read32
        (secondIterator + 12) = 1 + chunkIndex := by
  simp only [decodeSecondPairValidStore, decodeSecondPairBaseStore]
  rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
    Mem.read32_write32_same]
  all_goals decide

theorem decode_none_of_odd_length (input : List UInt8)
    (hodd : input.length % 2 ≠ 0) : decode input = none := by
  by_contra hn
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists.mp hn
  have hlen := decode_some_length input output houtput.symm
  omega

theorem decodeOddStore_result_tag (store : MachineStore Universal.State) :
    (decodeOddStore store).wasm.mem.read32 decodeResultOut = 2147483648 := by
  simp [decodeOddStore, Mem.read32, Mem.write64]
  bv_decide

theorem decodeOddStore_result_payload (store : MachineStore Universal.State) :
    (decodeOddStore store).wasm.mem.read32 (decodeResultOut + 4) = 1114112 := by
  simp [decodeOddStore, Mem.read32, Mem.write64]
  bv_decide

theorem decodeOddStore_core_facts
    (store : MachineStore Universal.State) (bump : UInt32)
    (h : DecodeCoreStoreFacts store bump) :
    DecodeCoreStoreFacts (decodeOddStore store) bump := by
  have preserve (addr value : UInt32)
      (haddr : store.wasm.mem.read32 addr = value)
      (hdisjoint : addr.toNat + 4 ≤ decodeResultOut.toNat ∨
        decodeResultOut.toNat + 8 ≤ addr.toNat) :
      (decodeOddStore store).wasm.mem.read32 addr = value := by
    simp only [decodeOddStore]
    rw [Mem.read32_write64_disjoint _ _ _ _ hdisjoint]
    exact haddr
  refine {
    runtime_module := h.runtime_module
    runtime_host := h.runtime_host
    memory_cap := h.memory_cap
    pages_lower := h.pages_lower
    pages_upper := h.pages_upper
    global_eq := by
      have hzero : 0 < store.wasm.globals.globals.length := by
        apply (getElem?_eq_some_iff.mp (show
          store.wasm.globals.globals[0]? = some (.i32 decodeStack) by
            simpa only [globalAt?, canonicalGlobalIndex_zero] using h.global_eq)).1
      simpa only [decodeOddStore, globalAt?, canonicalGlobalIndex_zero] using
        (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
    status_capacity := preserve decodeStatusVector 0 h.status_capacity (by decide)
    status_pointer := preserve (decodeStatusVector + 4) 1 h.status_pointer
      (by decide)
    status_length := preserve (decodeStatusVector + 8) 0 h.status_length
      (by decide)
    input_eq := h.input_eq
    output_eq := h.output_eq
    oom_eq := h.oom_eq
    bump_eq := preserve 1053960 bump h.bump_eq (by decide)
    bump_zero_or_lower := h.bump_zero_or_lower
    bump_signed := h.bump_signed }

theorem decodeEmptyCoreStore_core_facts
    (store : MachineStore Universal.State) (data bump : UInt32)
    (h : DecodeCoreStoreFacts store bump) :
    DecodeCoreStoreFacts (decodeEmptyCoreStore store data) bump := by
  refine {
    runtime_module := h.runtime_module
    runtime_host := h.runtime_host
    memory_cap := h.memory_cap
    pages_lower := h.pages_lower
    pages_upper := h.pages_upper
    global_eq := by
      have hzero : 0 < store.wasm.globals.globals.length := by
        apply (getElem?_eq_some_iff.mp (show
          store.wasm.globals.globals[0]? = some (.i32 decodeStack) by
            simpa only [globalAt?, canonicalGlobalIndex_zero] using h.global_eq)).1
      have hzero' : 0 <
          (decodePairEmptyStore (decodeEvenPreparedStore store data 0)).wasm.globals.globals.length := by
        simpa only [decodePairEmptyStore, decodeEvenPreparedStore,
          List.length_set] using hzero
      simpa only [decodeEmptyCoreStore, globalAt?, canonicalGlobalIndex_zero]
        using (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero')
    status_capacity := by
      simpa [decodeEmptyCoreStore, decodePairEmptyStore,
        decodeEvenPreparedStore, Mem.read32, Mem.write32, Mem.write64,
        Mem.write8] using h.status_capacity
    status_pointer := by
      simpa [decodeEmptyCoreStore, decodePairEmptyStore,
        decodeEvenPreparedStore, Mem.read32, Mem.write32, Mem.write64,
        Mem.write8] using h.status_pointer
    status_length := by
      simpa [decodeEmptyCoreStore, decodePairEmptyStore,
        decodeEvenPreparedStore, Mem.read32, Mem.write32, Mem.write64,
        Mem.write8] using h.status_length
    input_eq := h.input_eq
    output_eq := h.output_eq
    oom_eq := h.oom_eq
    bump_eq := by
      simpa [decodeEmptyCoreStore, decodePairEmptyStore,
        decodeEvenPreparedStore, Mem.read32, Mem.write32, Mem.write64,
        Mem.write8] using h.bump_eq
    bump_zero_or_lower := h.bump_zero_or_lower
    bump_signed := h.bump_signed }

set_option maxHeartbeats 5000000 in
theorem decodeFirstInvalidCoreStore_core_facts
    (store : MachineStore Universal.State)
    (data len chunkIndex bad index bump : UInt32) (badByte : UInt8)
    (h : DecodeCoreStoreFacts store bump) :
    DecodeCoreStoreFacts
      (decodeInvalidCoreStore
        (decodePairInvalidStore (decodeEvenPreparedStore store data len)
          data len chunkIndex badByte index) bad index) bump := by
  let paired := decodePairInvalidStore (decodeEvenPreparedStore store data len)
    data len chunkIndex badByte index
  let finalStore := decodeInvalidCoreStore paired bad index
  refine {
    runtime_module := by
      change store.runtime.currentModule = «module»
      exact h.runtime_module
    runtime_host := by
      change store.runtime.currentHost = Universal.envFor «module»
      exact h.runtime_host
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
      have hzero : 0 < paired.wasm.globals.globals.length := by
        have hs := (getElem?_eq_some_iff.mp (show
          store.wasm.globals.globals[0]? = some (.i32 decodeStack) by
            simpa only [globalAt?, canonicalGlobalIndex_zero] using h.global_eq)).1
        simpa only [paired, decodePairInvalidStore,
          decodeEvenPreparedStore, List.length_set] using hs
      simpa only [finalStore, decodeInvalidCoreStore, globalAt?,
        canonicalGlobalIndex_zero] using
          (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
    status_capacity := by
      simpa [finalStore, paired, decodeInvalidCoreStore,
        decodePairInvalidStore, decodeEvenPreparedStore,
        Mem.read32, Mem.write32, Mem.write64, Mem.write8] using h.status_capacity
    status_pointer := by
      simpa [finalStore, paired, decodeInvalidCoreStore,
        decodePairInvalidStore, decodeEvenPreparedStore,
        Mem.read32, Mem.write32, Mem.write64, Mem.write8] using h.status_pointer
    status_length := by
      simpa [finalStore, paired, decodeInvalidCoreStore,
        decodePairInvalidStore, decodeEvenPreparedStore,
        Mem.read32, Mem.write32, Mem.write64, Mem.write8] using h.status_length
    input_eq := h.input_eq
    output_eq := h.output_eq
    oom_eq := h.oom_eq
    bump_eq := by
      simpa [finalStore, paired, decodeInvalidCoreStore,
        decodePairInvalidStore, decodeEvenPreparedStore,
        Mem.read32, Mem.write32, Mem.write64, Mem.write8] using h.bump_eq
    bump_zero_or_lower := h.bump_zero_or_lower
    bump_signed := h.bump_signed }

theorem decodeEmptyCoreStore_result
    (store : MachineStore Universal.State) (data bump : UInt32)
    (hfacts : DecodeCoreStoreFacts store bump) :
    DecodeCoreResult [] data
      (decodeAfterCoreConfig (decodeEmptyCoreStore store data) data) := by
  left
  refine ⟨decodeEmptyCoreStore store data, 0, 1, 0, [], rfl, by simp [decode],
    (by simp [decodeEmptyCoreStore, Mem.read32, Mem.write64, Mem.write32] <;>
      bv_decide),
    (by simp [decodeEmptyCoreStore, Mem.read32, Mem.write64, Mem.write32] <;>
      bv_decide),
    (by simp [decodeEmptyCoreStore, Mem.read32, Mem.write64, Mem.write32] <;>
      bv_decide), by simp, by simp, by norm_num,
    (by
      have hp := hfacts.pages_lower
      change 1 ≤ store.wasm.mem.pages * 65536
      omega),
    by simp [Mem.readBytes], ⟨bump,
        decodeEmptyCoreStore_core_facts store data bump hfacts, Or.inl rfl⟩⟩

theorem Mem.read8_of_readBytes
    (m : Mem) (off count i : Nat) (bytes : List UInt8)
    (hbytes : m.readBytes off count = bytes) (hi : i < count)
    (hilen : i < bytes.length) (addr : UInt32)
    (haddr : addr.toNat = off + i) : m.read8 addr = bytes[i] := by
  have hget := congrArg (fun xs => xs[i]?) hbytes
  simp only [Mem.readBytes, List.getElem?_map, List.getElem?_range, hi,
    Option.map_some] at hget
  rw [List.getElem?_eq_getElem hilen] at hget
  change m.bytes addr.toNat = bytes[i]
  rw [haddr]
  exact Option.some.inj hget

theorem ofNat_length_and_one_eq_zero (input : List UInt8)
    (heven : input.length % 2 = 0) :
    UInt32.ofNat input.length &&& (1 : UInt32) = 0 := by
  apply UInt32.toNat_inj.mp
  simpa [UInt32.toNat_and] using heven

set_option maxRecDepth 100000 in
theorem decode_post_success_result
    (input bytes : List UInt8) (store : MachineStore Universal.State)
    (data len ptr capacity outLen bump : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (hmarker : store.wasm.mem.read32 coreError = 1114114)
    (hreturning : returningInstance = store.runtime.entry)
    (hdecode : decode input = some bytes)
    (houtLen : outLen.toNat = bytes.length)
    (hfits : outLen.toNat ≤ capacity.toNat)
    (houtBound : ptr.toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536)
    (hptrLower : 1048564 ≤ ptr.toNat)
    (hbytes : store.wasm.mem.readBytes ptr.toNat bytes.length = bytes)
    (hptrAllocLower : 1054000 ≤ ptr.toNat)
    (houtputEnd : ptr.toNat + capacity.toNat = bump.toNat)
    (hfacts : DecodeCoreStoreFacts
      (decodeLoopSuccessStore store ptr capacity outLen) bump) :
    let finalStore := decodeLoopSuccessStore store ptr capacity outLen
    Reaches (decodePostLoopConfig store data len ptr capacity outLen seed
        returningInstance) (decodeAfterCoreConfig finalStore data) ∧
      DecodeCoreResult input data (decodeAfterCoreConfig finalStore data) := by
  dsimp only
  let finalStore := decodeLoopSuccessStore store ptr capacity outLen
  have hreach := decode_post_loop_success_reaches store data len ptr capacity
    outLen seed returningInstance hpages hglobal hmarker hreturning
  constructor
  · exact hreach
  · left
    refine ⟨finalStore, capacity, ptr, outLen, bytes, rfl, hdecode,
      (decodeLoopSuccessStore_result_fields store ptr capacity outLen).1,
      (decodeLoopSuccessStore_result_fields store ptr capacity outLen).2.1,
      (decodeLoopSuccessStore_result_fields store ptr capacity outLen).2.2,
      houtLen, hfits, (by
        have hb := hfacts.bump_signed
        have hp : 0 < ptr.toNat := by omega
        omega), (by simpa [finalStore, decodeLoopSuccessStore] using
        houtBound),
      (decodeLoopSuccessStore_readBytes_above store ptr capacity outLen
        ptr.toNat bytes.length hptrLower).trans hbytes,
      ⟨bump, hfacts, Or.inr ⟨hptrAllocLower, houtputEnd⟩⟩⟩

set_option maxRecDepth 100000 in
theorem decode_post_invalid_result
    (input : List UInt8) (store : MachineStore Universal.State)
    (data len ptr capacity outLen bad index bump : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (hmarker : store.wasm.mem.read32 coreError = bad)
    (hmarkerNe : bad ≠ 1114114)
    (hindex : store.wasm.mem.read32 (coreError + 4) = index)
    (hcapacity : capacity ≠ 0)
    (hreturning : returningInstance = store.runtime.entry)
    (hdecode : decode input = none)
    (hkind : (input.length % 2 = 1 ∧ bad = 1114112) ∨
      (input.length % 2 = 0 ∧ bad.toNat ≤ 255))
    (hfacts : DecodeCoreStoreFacts (decodeInvalidCoreStore store bad index)
      bump) :
    let finalStore := decodeInvalidCoreStore store bad index
    Reaches (decodePostLoopConfig store data len ptr capacity outLen seed
        returningInstance) (decodeAfterCoreConfig finalStore data) ∧
      DecodeCoreResult input data (decodeAfterCoreConfig finalStore data) := by
  dsimp only
  let finalStore := decodeInvalidCoreStore store bad index
  have hreach := decode_post_loop_invalid_reaches store data len ptr capacity
    outLen bad index seed returningInstance hmod hpages hglobal hmarker
    hmarkerNe hindex hcapacity hreturning
  constructor
  · exact hreach
  · right
    refine ⟨finalStore, bad, rfl, hdecode,
      decodeInvalidCoreStore_result_tag store bad index,
      decodeInvalidCoreStore_result_payload store bad index, hkind,
      ⟨bump, hfacts⟩⟩

theorem decodeInitialVectorStore_remaining
    (store : MachineStore Universal.State) (ptr : UInt32) (seed : UInt8)
    (hptrLower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr seed).wasm.mem.read32
        (secondIterator + 4) =
      store.wasm.mem.read32 (coreIterator + 4) := by
  rw [show secondIterator = coreFrame + 72 by decide,
    show coreIterator = coreFrame + 40 by decide]
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_high _ _ _ (by decide),
    Mem.read64_high _ _ (by decide)]
  rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write8_disjoint]
  all_goals try rfl
  all_goals try decide
  left
  have haddr : (coreFrame + 40 + 4).toNat + 4 = 1048480 := by decide
  omega

theorem decodeInitialVectorStore_chunk
    (store : MachineStore Universal.State) (ptr : UInt32) (seed : UInt8)
    (hptrLower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr seed).wasm.mem.read32
        (secondIterator + 8) =
      store.wasm.mem.read32 (coreIterator + 8) := by
  rw [show secondIterator + 8 = coreFrame + 80 by decide,
    show coreIterator + 8 = coreFrame + 48 by decide]
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint,
    Mem.read32_write64_low, Mem.read64_low]
  rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write8_disjoint]
  all_goals try rfl
  all_goals try decide
  left
  have haddr : (coreFrame + 48).toNat + 4 = 1048484 := by decide
  omega

theorem decodeInitialVectorStore_pointer
    (store : MachineStore Universal.State) (ptr : UInt32) (seed : UInt8)
    (hptrLower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr seed).wasm.mem.read32 secondIterator =
      store.wasm.mem.read32 coreIterator := by
  rw [show secondIterator = coreFrame + 72 by decide,
    show coreIterator = coreFrame + 40 by decide]
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_low, Mem.read64_low]
  rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write8_disjoint]
  all_goals try rfl
  all_goals try decide
  left
  have haddr : (coreFrame + 40).toNat + 4 = 1048476 := by decide
  omega

theorem decodeInitialVectorStore_index
    (store : MachineStore Universal.State) (ptr : UInt32) (seed : UInt8)
    (hptrLower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr seed).wasm.mem.read32
        (secondIterator + 12) =
      store.wasm.mem.read32 (coreIterator + 12) := by
  rw [show secondIterator + 12 = (coreFrame + 80) + 4 by decide,
    show coreIterator + 12 = (coreFrame + 48) + 4 by decide]
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint,
    Mem.read32_write64_high _ _ _ (by decide), Mem.read64_high _ _ (by decide)]
  rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write8_disjoint]
  all_goals try rfl
  all_goals try decide
  left
  have haddr : (coreFrame + 48 + 4).toNat + 4 = 1048488 := by decide
  omega

theorem decodeInitialVectorStore_error_pointer
    (store : MachineStore Universal.State) (ptr : UInt32) (seed : UInt8)
    (hptrLower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr seed).wasm.mem.read32
        (secondIterator + 16) = store.wasm.mem.read32 (coreIterator + 16) := by
  rw [show secondIterator + 16 = coreFrame + 88 by decide,
    show coreIterator + 16 = coreFrame + 56 by decide]
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_same, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write8_disjoint]
  all_goals try rfl
  all_goals try decide
  left
  have haddr : (coreFrame + 56).toNat + 4 = 1048492 := by decide
  omega

theorem decodeInitialVectorStore_error_marker
    (store : MachineStore Universal.State) (ptr : UInt32) (seed : UInt8)
    (hptrLower : 1048528 ≤ ptr.toNat) :
    (decodeInitialVectorStore store ptr seed).wasm.mem.read32 secondError =
      store.wasm.mem.read32 coreError := by
  simp only [decodeInitialVectorStore]
  rw [Mem.read32_write64_disjoint, Mem.read32_write64_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write8_disjoint]
  all_goals try rfl
  all_goals try decide
  left
  have haddr : secondError.toNat + 4 = 1048468 := by decide
  omega

set_option maxRecDepth 100000 in
theorem initial_second_metadata
    (store allocStore : MachineStore Universal.State)
    (data len bump : UInt32) (seed : UInt8)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hptrLower : 1048528 ≤ (allocatorPtr bump 1).toNat)
    (hsuccess :
      ByteGrowSuccess
        (decodePairValidStore (decodeEvenPreparedStore store data len)
          data len 0 seed) 0 1 8 bump allocStore) :
    let initial := decodeInitialVectorStore allocStore
      (allocatorPtr bump 1) seed
    initial.wasm.mem.read32 (secondIterator + 4) = len - 2 ∧
    initial.wasm.mem.read32 (secondIterator + 16) = secondError ∧
    initial.wasm.mem.read32 (secondIterator + 8) = 2 ∧
    initial.wasm.mem.read32 secondIterator = 2 + data ∧
    initial.wasm.mem.read32 (secondIterator + 12) = 1 ∧
    initial.wasm.mem.read32 secondError = 1114114 ∧
    globalAt? initial 0 = some (.i32 coreFrame) := by
  dsimp only
  let prepared := decodeEvenPreparedStore store data len
  let first := decodePairValidStore prepared data len 0 seed
  let ptr := allocatorPtr bump 1
  let initial := decodeInitialVectorStore allocStore ptr seed
  have preserve (addr : UInt32) (haddr : addr.toNat + 4 ≤ 1053960) :
      allocStore.wasm.mem.read32 addr = first.wasm.mem.read32 addr := by
    exact hsuccess.fresh_preserves_read32 haddr
  have hlen : allocStore.wasm.mem.read32 (coreIterator + 4) = len - 2 := by
    rw [preserve _ (by
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])]
    simp only [first, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_same]
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  have herr : allocStore.wasm.mem.read32 (coreIterator + 16) = coreError := by
    rw [preserve _ (by
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])]
    rw [show coreIterator + 16 = coreFrame + 56 by
      apply UInt32.toNat_inj.mp
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]]
    simp only [first, prepared, decodePairValidStore, decodePairBaseStore,
      decodeEvenPreparedStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_same]
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  have hchunk : allocStore.wasm.mem.read32 (coreIterator + 8) = 2 := by
    rw [preserve _ (by
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])]
    rw [show coreIterator + 8 = coreFrame + 48 by
      apply UInt32.toNat_inj.mp
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]]
    simp only [first, prepared, decodePairValidStore, decodePairBaseStore,
      decodeEvenPreparedStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write64_low]
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  have hptr : allocStore.wasm.mem.read32 coreIterator = 2 + data := by
    rw [preserve _ (by
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])]
    simp only [first, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_same]
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  have hindex : allocStore.wasm.mem.read32 (coreIterator + 12) = 1 := by
    rw [preserve _ (by
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])]
    simp only [first, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_same]
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  have hmarker : allocStore.wasm.mem.read32 coreError = 1114114 := by
    rw [preserve _ (by
      norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])]
    simp only [first, prepared, decodePairValidStore, decodePairBaseStore,
      decodeEvenPreparedStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write64_disjoint, Mem.read32_write32_same]
    all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
  have hglobalAlloc : globalAt? allocStore 0 = some (.i32 coreFrame) := by
    rw [hsuccess.globalAt_eq]
    change globalAt? first 0 = some (.i32 coreFrame)
    change globalAt? prepared 0 = some (.i32 coreFrame)
    exact decodeEvenPreparedStore_global_zero store data len hglobal
  exact ⟨
    (by simpa only [initial, ptr] using
      (decodeInitialVectorStore_remaining allocStore (allocatorPtr bump 1)
        seed hptrLower).trans hlen),
    (by simpa only [initial, ptr] using
      (decodeInitialVectorStore_error_pointer allocStore (allocatorPtr bump 1)
        seed hptrLower).trans herr),
    (by simpa only [initial, ptr] using
      (decodeInitialVectorStore_chunk allocStore (allocatorPtr bump 1) seed
        hptrLower).trans hchunk),
    (by simpa only [initial, ptr] using
      (decodeInitialVectorStore_pointer allocStore (allocatorPtr bump 1) seed
        hptrLower).trans hptr),
    (by simpa only [initial, ptr] using
      (decodeInitialVectorStore_index allocStore (allocatorPtr bump 1) seed
        hptrLower).trans hindex),
    (by simpa only [initial, ptr] using
      (decodeInitialVectorStore_error_marker allocStore (allocatorPtr bump 1)
        seed hptrLower).trans hmarker),
    (by change globalAt? allocStore 0 = some (.i32 coreFrame)
        exact hglobalAlloc)⟩

theorem decodeSecondPairEmptyStore_readBytes_above
    (store : MachineStore Universal.State) (off count : Nat)
    (habove : 1048450 ≤ off) :
    (decodeSecondPairEmptyStore store).wasm.mem.readBytes off count =
      store.wasm.mem.readBytes off count := by
  have hbase : secondPairOut.toNat = 1048448 := by decide
  have hnext : (secondPairOut + 1).toNat = 1048449 := by decide
  simp only [decodeSecondPairEmptyStore]
  rw [Mem.readBytes_write8_disjoint, Mem.readBytes_write8_disjoint]
  all_goals try rfl
  all_goals right
  all_goals omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_second_empty_outcome
    (input : List UInt8) (store allocStore : MachineStore Universal.State)
    (inputCapacity data bump : UInt32) (hi lo : UInt8)
    (hiRoute loRoute : HexRoute)
    (hsplit : input = [hi, lo])
    (hhi : hiRoute.valid hi) (hlo : loRoute.valid lo)
    (hinputBytes : store.wasm.mem.readBytes data.toNat input.length = input)
    (hinputCapacity : input.length ≤ inputCapacity.toNat)
    (hdataBump : data.toNat + inputCapacity.toNat = bump.toNat)
    (hdataLower : 1054000 ≤ data.toNat)
    (hbumpSigned : bump.toNat < 2 ^ 31)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hmod : store.runtime.currentModule = «module»)
    (hpagesLower : 17 ≤ store.wasm.mem.pages)
    (hpagesUpper : store.wasm.mem.pages ≤ 65536)
    (hbaseFacts : DecodeCoreStoreFacts store bump)
    (hfinishSmall : bump.toNat + 8 < 2 ^ 31)
    (hsuccess :
      let len := UInt32.ofNat input.length
      let seed := (loRoute.nibble lo).toUInt8 |||
        ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
      let first := decodePairValidStore
        (decodeEvenPreparedStore store data len) data len 0 seed
      ByteGrowSuccess first 0 1 8 bump allocStore) :
    let len := UInt32.ofNat input.length
    let seed := (loRoute.nibble lo).toUInt8 |||
      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
    let ptr := allocatorPtr bump 1
    ReachesOrOOM (decodeAfterInitialAllocConfig allocStore data len seed ptr
        store.runtime.entry) (DecodeCoreResult input data) := by
  dsimp only
  let len := UInt32.ofNat input.length
  let seed := (loRoute.nibble lo).toUInt8 |||
    ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
  let first := decodePairValidStore
    (decodeEvenPreparedStore store data len) data len 0 seed
  let ptr := allocatorPtr bump 1
  let newBump := allocatorFinish 8 1 bump
  let initial := decodeInitialVectorStore allocStore ptr seed
  let paired := decodeSecondPairEmptyStore initial
  have hbumpNe : bump ≠ 0 := by
    intro hz
    have hzNat := congrArg UInt32.toNat hz
    simp at hzNat
    rw [hzNat] at hdataBump
    omega
  have hptrEq : ptr = bump := allocatorPtr_one_eq bump hbumpNe
  have hmeta := initial_second_metadata store allocStore data len bump seed
    hglobal (by rw [allocatorPtr_one_eq bump hbumpNe]; omega) hsuccess
  have hptrNe : ptr ≠ 0 := by simpa [hptrEq] using hbumpNe
  have hbound : ptr.toNat + 1 ≤ allocStore.wasm.mem.pages * 65536 := by
    have hf := hsuccess.fresh_eight_finish_bound hbumpNe (by
      norm_num [UInt32.size] at hfinishSmall ⊢
      omega) (by
      change store.wasm.mem.pages < UInt32.size
      norm_num [UInt32.size]
      omega)
    rw [hptrEq]
    omega
  have htoSecond := decode_after_initial_alloc_to_second_pair allocStore data
    len ptr seed store.runtime.entry (by
      exact le_trans hpagesLower hsuccess.pages_mono) hptrNe hbound
  apply ReachesOrOOM.prependReaches htoSecond
  have hempty : len - 2 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le]
    · simp [len, hsplit]
    · apply UInt32.le_iff_toNat_le.mpr
      simp [len, hsplit]
  have hpair := decode_second_pair_empty_to_post allocStore data len ptr seed
    store.runtime.entry (by
      change allocStore.runtime.currentModule = «module»
      rw [hsuccess.runtime_eq]
      exact hmod)
    (by exact le_trans hpagesLower hsuccess.pages_mono)
    (by simpa [hempty] using hmeta.1)
  have hseedValue : seed = UInt8.ofNat
      (16 * (hiRoute.nibble hi).toNat + (loRoute.nibble lo).toNat) := by
    simpa [seed] using route_pair_byte hi lo
      (hiRoute.nibble hi).toNat (loRoute.nibble lo).toNat hiRoute loRoute
      rfl rfl (hexValue_some_lt hi _ (hexValue_of_route_valid hiRoute hi hhi))
      (hexValue_some_lt lo _ (hexValue_of_route_valid loRoute lo hlo))
  have hdecode : decode input = some [seed] := by
    simp [hsplit, decode, hexValue_of_route_valid hiRoute hi hhi,
      hexValue_of_route_valid loRoute lo hlo, hseedValue]
  have hglobalInitial : globalAt? initial 0 = some (.i32 coreFrame) := hmeta.2.2.2.2.2.2
  have hmarker : paired.wasm.mem.read32 coreError = 1114114 := by
    change (decodeSecondPairEmptyStore initial).wasm.mem.read32 coreError = _
    simp only [decodeSecondPairEmptyStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint]
    · exact hmeta.2.2.2.2.2.1
    all_goals decide
  have hreturn : store.runtime.entry = paired.runtime.entry := by
    change store.runtime.entry = allocStore.runtime.entry
    rw [hsuccess.runtime_eq]
    simp [first, decodePairValidStore, decodePairBaseStore,
      decodeEvenPreparedStore]
  have hbytes : paired.wasm.mem.readBytes ptr.toNat 1 = [seed] := by
    rw [decodeSecondPairEmptyStore_readBytes_above]
    · exact decodeInitialVectorStore_output allocStore ptr seed (by
        rw [hptrEq]
        omega)
    · rw [hptrEq]
      omega
  have hpairedStatus (addr value : UInt32)
      (habove : 1048528 ≤ addr.toNat)
      (hupper : addr.toNat + 4 ≤ 1048560)
      (hstore : store.wasm.mem.read32 addr = value) :
      paired.wasm.mem.read32 addr = value := by
    have hfirst : first.wasm.mem.read32 addr = value :=
      (decodePairValidStore_read32_above (decodeEvenPreparedStore store data len)
        data len 0 seed addr (le_trans (by decide) habove)).trans
        ((decodeEvenPreparedStore_read32_above store data len addr
          (le_trans (by decide) habove)).trans hstore)
    have halloc : allocStore.wasm.mem.read32 addr = value :=
      (hsuccess.fresh_preserves_read32 (le_trans hupper (by decide))).trans
        hfirst
    have hinitial : initial.wasm.mem.read32 addr = value := by
      apply (decodeInitialVectorStore_read32_between allocStore ptr seed addr
        habove (by
          rw [hptrEq]
          exact le_trans hupper (le_trans (by decide)
            (le_trans hdataLower (by omega))))).trans halloc
    simp only [paired, decodeSecondPairEmptyStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint]
    · exact hinitial
    all_goals right
    all_goals exact le_trans (by decide) habove
  have hnewBumpNat : newBump.toNat = bump.toNat + 8 := by
    change (allocatorFinish 8 1 bump).toNat = bump.toNat + 8
    rw [allocatorFinish_one_eq_comm 8 bump hbumpNe, UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    norm_num [UInt32.size] at hfinishSmall ⊢
    omega
  have hpairedBump : paired.wasm.mem.read32 1053960 = newBump := by
    have hallocBump : allocStore.wasm.mem.read32 1053960 = newBump := by
      simpa [newBump] using hsuccess.read_bump (by
        rw [allocatorPtr_one_eq bump hbumpNe, ← hdataBump]
        have hc := hinputCapacity
        simp [hsplit] at hc
        norm_num
        omega)
    have hinitialBump : initial.wasm.mem.read32 1053960 = newBump := by
      apply (decodeInitialVectorStore_read32_between allocStore ptr seed
        1053960 (by decide) (by
          rw [hptrEq]
          have hs : (1053960 : UInt32).toNat + 4 ≤ 1054000 := by decide
          exact hs.trans (hdataLower.trans (by omega)))).trans hallocBump
    simp only [paired, decodeSecondPairEmptyStore]
    rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint]
    · exact hinitialBump
    all_goals decide
  have hpairedMod : paired.runtime.currentModule = «module» := by
    change allocStore.runtime.currentModule = «module»
    rw [hsuccess.runtime_eq]
    exact hbaseFacts.runtime_module
  have hpairedHost : paired.runtime.currentHost = Universal.envFor «module» := by
    change allocStore.runtime.currentHost = Universal.envFor «module»
    rw [hsuccess.runtime_eq]
    exact hbaseFacts.runtime_host
  have hpairedCap : paired.wasm.memoryCap paired.runtime.currentModule 0 =
      65536 := by
    change allocStore.wasm.memoryCap allocStore.runtime.currentModule 0 = 65536
    rw [hsuccess.runtime_eq]
    exact (hsuccess.memoryCap_eq store.runtime.currentModule 0).trans
      hbaseFacts.memory_cap
  have hpairedPagesLower : 17 ≤ paired.wasm.mem.pages := by
    change 17 ≤ allocStore.wasm.mem.pages
    exact le_trans hbaseFacts.pages_lower hsuccess.pages_mono
  have hpairedPagesUpper : paired.wasm.mem.pages ≤ 65536 := by
    change allocStore.wasm.mem.pages ≤ 65536
    exact hsuccess.pages_le_cap hbaseFacts.memory_cap hbaseFacts.pages_upper
  have hpairedInput : paired.wasm.host.stdio.input = [] := by
    change allocStore.wasm.host.stdio.input = []
    rw [hsuccess.host_eq]
    exact hbaseFacts.input_eq
  have hpairedOutput : paired.wasm.host.stdio.output = [] := by
    change allocStore.wasm.host.stdio.output = []
    rw [hsuccess.host_eq]
    exact hbaseFacts.output_eq
  have hpairedOom : paired.wasm.host.oom.raised = false := by
    change allocStore.wasm.host.oom.raised = false
    rw [hsuccess.host_eq]
    exact hbaseFacts.oom_eq
  have hfinalFacts := decodeLoopSuccessStore_core_facts paired ptr 8 1 newBump
    hpairedMod hpairedHost hpairedCap hpairedPagesLower hpairedPagesUpper
    (by change globalAt? initial 0 = some (.i32 coreFrame); exact hglobalInitial)
    (hpairedStatus decodeStatusVector 0 (by decide) (by decide)
      hbaseFacts.status_capacity)
    (hpairedStatus (decodeStatusVector + 4) 1 (by decide) (by decide)
      hbaseFacts.status_pointer)
    (hpairedStatus (decodeStatusVector + 8) 0 (by decide) (by decide)
      hbaseFacts.status_length)
    hpairedInput hpairedOutput hpairedOom hpairedBump (Or.inr (by
      rw [hnewBumpNat]
      exact le_trans hdataLower (by omega)))
    (by rw [hnewBumpNat]; exact hfinishSmall)
  have hfinish := decode_post_success_result input [seed] paired data len ptr
    8 1 newBump seed
    store.runtime.entry (by exact le_trans hpagesLower hsuccess.pages_mono)
    (by
      change globalAt? initial 0 = some (.i32 coreFrame)
      exact hglobalInitial)
    hmarker hreturn hdecode (by simp) (by simp) (by
      change ptr.toNat + 1 ≤ allocStore.wasm.mem.pages * 65536
      exact hbound)
    (by rw [hptrEq]; omega) hbytes (by
      rw [hptrEq]
      omega)
    (by rw [hptrEq, hnewBumpNat]; simp) hfinalFacts
  exact ReachesOrOOM.of_reaches (hpair.trans hfinish.1) hfinish.2


set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_loop_initial_invariant
    (input : List UInt8) (store allocStore : MachineStore Universal.State)
    (inputCapacity data bump : UInt32)
    (hi₀ lo₀ hi₁ lo₁ : UInt8) (rest : List UInt8)
    (hiRoute₀ loRoute₀ hiRoute₁ loRoute₁ : HexRoute)
    (hsplit : input = hi₀ :: lo₀ :: hi₁ :: lo₁ :: rest)
    (heven : input.length % 2 = 0)
    (hhi₀ : hiRoute₀.valid hi₀) (hlo₀ : loRoute₀.valid lo₀)
    (hhi₁ : hiRoute₁.valid hi₁) (hlo₁ : loRoute₁.valid lo₁)
    (hinputBytes : store.wasm.mem.readBytes data.toNat input.length = input)
    (hinputCapacity : input.length ≤ inputCapacity.toNat)
    (hdataBump : data.toNat + inputCapacity.toNat = bump.toNat)
    (hdataLower : 1054000 ≤ data.toNat)
    (hbumpSigned : bump.toNat < 2 ^ 31)
    (hbumpRead : store.wasm.mem.read32 1053960 = bump)
    (hmod : store.runtime.currentModule = «module»)
    (hhost : store.runtime.currentHost = Universal.envFor «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536)
    (hpagesLower : 17 ≤ store.wasm.mem.pages)
    (hpagesUpper : store.wasm.mem.pages ≤ 65536)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hstatusCapacity : store.wasm.mem.read32 decodeStatusVector = 0)
    (hstatusPointer : store.wasm.mem.read32 (decodeStatusVector + 4) = 1)
    (hstatusLength : store.wasm.mem.read32 (decodeStatusVector + 8) = 0)
    (hinputEmpty : store.wasm.host.stdio.input = [])
    (houtputEmpty : store.wasm.host.stdio.output = [])
    (hoom : store.wasm.host.oom.raised = false)
    (hfinishSmall : bump.toNat + 8 < 2 ^ 31)
    (hsuccess :
      let len := UInt32.ofNat input.length
      let seed := (loRoute₀.nibble lo₀).toUInt8 |||
        ((hiRoute₀.nibble hi₀).toUInt8 <<< (4 : UInt8))
      let prepared := decodeEvenPreparedStore store data len
      let first := decodePairValidStore prepared data len 0 seed
      ByteGrowSuccess first 0 1 8 bump allocStore) :
    let len := UInt32.ofNat input.length
    let seed := (loRoute₀.nibble lo₀).toUInt8 |||
      ((hiRoute₀.nibble hi₀).toUInt8 <<< (4 : UInt8))
    let next := (loRoute₁.nibble lo₁).toUInt8 |||
      ((hiRoute₁.nibble hi₁).toUInt8 <<< (4 : UInt8))
    let ptr := allocatorPtr bump 1
    let newBump := allocatorFinish 8 1 bump
    let initial := decodeInitialVectorStore allocStore ptr seed
    let paired := decodeSecondPairValidStore initial (data + 2) (len - 2) 1 next
    DecodeLoopInv input [hi₀, lo₀, hi₁, lo₁] rest [seed] paired
      inputCapacity data len ptr 8 1 newBump next := by
  dsimp only
  let len := UInt32.ofNat input.length
  let seed := (loRoute₀.nibble lo₀).toUInt8 |||
    ((hiRoute₀.nibble hi₀).toUInt8 <<< (4 : UInt8))
  let next := (loRoute₁.nibble lo₁).toUInt8 |||
    ((hiRoute₁.nibble hi₁).toUInt8 <<< (4 : UInt8))
  let prepared := decodeEvenPreparedStore store data len
  let first := decodePairValidStore prepared data len 0 seed
  let ptr := allocatorPtr bump 1
  let newBump := allocatorFinish 8 1 bump
  let initial := decodeInitialVectorStore allocStore ptr seed
  let paired := decodeSecondPairValidStore initial (data + 2) (len - 2) 1 next
  have hbumpNe : bump ≠ 0 := by
    intro hz
    have hzNat := congrArg UInt32.toNat hz
    simp at hzNat
    rw [hzNat] at hdataBump
    omega
  have hptrEq : ptr = bump := allocatorPtr_one_eq bump hbumpNe
  have hinputSmall : input.length < 2 ^ 31 := by omega
  have hlenNat : len.toNat = input.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size] at hinputSmall ⊢
    omega
  have hfirstInput : first.wasm.mem.readBytes data.toNat input.length = input := by
    rw [decodePairValidStore_readBytes_above]
    · rw [decodeEvenPreparedStore_readBytes_above]
      · exact hinputBytes
      · omega
    · omega
  have hallocInput : allocStore.wasm.mem.readBytes data.toNat input.length =
      input := by
    rw [hsuccess.fresh_preserves_readBytes_disjoint]
    · exact hfirstInput
    · right; omega
  have hinputEnd : data.toNat + input.length ≤ ptr.toNat := by
    rw [hptrEq]
    omega
  have hinitialInput : initial.wasm.mem.readBytes data.toNat input.length =
      input := by
    rw [decodeInitialVectorStore_readBytes_between]
    · exact hallocInput
    · omega
    · exact hinputEnd
  have hpairedInput : paired.wasm.mem.readBytes data.toNat input.length =
      input := by
    rw [decodeSecondPairValidStore_readBytes_above]
    · exact hinitialInput
    · omega
  have hnewBumpNat : newBump.toNat = bump.toNat + 8 := by
    change (allocatorFinish 8 1 bump).toNat = bump.toNat + 8
    rw [allocatorFinish_one_eq_comm 8 bump hbumpNe, UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    norm_num [UInt32.size] at hfinishSmall ⊢
    omega
  have hfinishBound : newBump.toNat ≤ allocStore.wasm.mem.pages * 65536 := by
    rw [hnewBumpNat]
    exact hsuccess.fresh_eight_finish_bound hbumpNe (by
      norm_num [UInt32.size] at hfinishSmall ⊢
      omega) (by
      change first.wasm.mem.pages < UInt32.size
      change store.wasm.mem.pages < UInt32.size
      norm_num [UInt32.size]
      omega)
  have hpagesMono := hsuccess.pages_mono
  have hhostEq := hsuccess.host_eq
  have hruntimeEq := hsuccess.runtime_eq
  have hglobalAlloc := hsuccess.globalAt_eq 0
  have hmemoryCap := hsuccess.memoryCap_eq store.runtime.currentModule 0
  have hpagesMax := hsuccess.pages_le_cap hcap hpagesUpper
  have hhiValue₀ := hexValue_of_route_valid hiRoute₀ hi₀ hhi₀
  have hloValue₀ := hexValue_of_route_valid loRoute₀ lo₀ hlo₀
  have hhiValue₁ := hexValue_of_route_valid hiRoute₁ hi₁ hhi₁
  have hloValue₁ := hexValue_of_route_valid loRoute₁ lo₁ hlo₁
  have hseed : seed = UInt8.ofNat
      (16 * (hiRoute₀.nibble hi₀).toNat +
        (loRoute₀.nibble lo₀).toNat) := by
    simpa [seed] using route_pair_byte hi₀ lo₀
      (hiRoute₀.nibble hi₀).toNat (loRoute₀.nibble lo₀).toNat
      hiRoute₀ loRoute₀ rfl rfl
      (hexValue_some_lt hi₀ _ hhiValue₀)
      (hexValue_some_lt lo₀ _ hloValue₀)
  have hnext : next = UInt8.ofNat
      (16 * (hiRoute₁.nibble hi₁).toNat +
        (loRoute₁.nibble lo₁).toNat) := by
    simpa [next] using route_pair_byte hi₁ lo₁
      (hiRoute₁.nibble hi₁).toNat (loRoute₁.nibble lo₁).toNat
      hiRoute₁ loRoute₁ rfl rfl
      (hexValue_some_lt hi₁ _ hhiValue₁)
      (hexValue_some_lt lo₁ _ hloValue₁)
  have hcombine₀ :
      16 * (hiRoute₀.nibble hi₀).toUInt8 + (loRoute₀.nibble lo₀).toUInt8 =
        seed := by
    rw [hseed]
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_ofNat]
    have hhiNat : (hiRoute₀.nibble hi₀).toUInt8.toNat =
        (hiRoute₀.nibble hi₀).toNat := by
      rw [UInt32.toUInt8_toNat, Nat.mod_eq_of_lt (by
        have := hexValue_some_lt hi₀ _ hhiValue₀
        omega)]
    have hloNat : (loRoute₀.nibble lo₀).toUInt8.toNat =
        (loRoute₀.nibble lo₀).toNat := by
      rw [UInt32.toUInt8_toNat, Nat.mod_eq_of_lt (by
        have := hexValue_some_lt lo₀ _ hloValue₀
        omega)]
    rw [hhiNat, hloNat]
    norm_num
  have hcombine₁ :
      16 * (hiRoute₁.nibble hi₁).toUInt8 + (loRoute₁.nibble lo₁).toUInt8 =
        next := by
    rw [hnext]
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_ofNat]
    have hhiNat : (hiRoute₁.nibble hi₁).toUInt8.toNat =
        (hiRoute₁.nibble hi₁).toNat := by
      rw [UInt32.toUInt8_toNat, Nat.mod_eq_of_lt (by
        have := hexValue_some_lt hi₁ _ hhiValue₁
        omega)]
    have hloNat : (loRoute₁.nibble lo₁).toUInt8.toNat =
        (loRoute₁.nibble lo₁).toNat := by
      rw [UInt32.toUInt8_toNat, Nat.mod_eq_of_lt (by
        have := hexValue_some_lt lo₁ _ hloValue₁
        omega)]
    rw [hhiNat, hloNat]
    norm_num
  have hmetadata := initial_second_metadata store allocStore data len bump seed
    hglobal (by
      rw [allocatorPtr_one_eq bump hbumpNe]
      exact le_trans (show 1048528 ≤ 1054000 by decide)
        (le_trans hdataLower (by omega))) hsuccess
  rcases hmetadata with ⟨hmetaRemaining, hmetaError, hmetaChunk, hmetaPtr,
    hmetaIndex, hmetaMarker, hmetaGlobal⟩
  have hpairedStatus (addr value : UInt32)
      (habove : 1048528 ≤ addr.toNat)
      (hupper : addr.toNat + 4 ≤ 1048560)
      (hstore : store.wasm.mem.read32 addr = value) :
      paired.wasm.mem.read32 addr = value := by
    have hfirst : first.wasm.mem.read32 addr = value :=
      (decodePairValidStore_read32_above prepared data len 0 seed addr
        (le_trans (by decide) habove)).trans
        ((decodeEvenPreparedStore_read32_above store data len addr
          (le_trans (by decide) habove)).trans hstore)
    have halloc : allocStore.wasm.mem.read32 addr = value :=
      (hsuccess.fresh_preserves_read32 (le_trans hupper (by decide))).trans
        hfirst
    have hinitial : initial.wasm.mem.read32 addr = value := by
      apply (decodeInitialVectorStore_read32_between allocStore ptr seed addr
        habove (by
          rw [hptrEq]
          exact le_trans hupper (le_trans (by decide)
            (le_trans hdataLower (by omega))))).trans halloc
    exact (decodeSecondPairValidStore_read32_above initial (data + 2)
      (len - 2) 1 next addr (le_trans (by decide) habove)).trans hinitial
  refine {
    input_split := by simpa [hsplit]
    input_even := heven
    consumed_even := by simp
    decoded_consumed := by
      simpa [decode, hhiValue₀, hloValue₀, hhiValue₁, hloValue₁] using
        And.intro hcombine₀ hcombine₁
    input_length := hlenNat
    remaining_length := by
      have hremainingWord : (len - 2) - 2 = UInt32.ofNat rest.length := by
        have htwoLen : (2 : UInt32) ≤ len := by
          apply UInt32.le_iff_toNat_le.mpr
          rw [hlenNat]
          simp [hsplit]
        have hsubNat : (len - 2).toNat = input.length - 2 := by
          calc
            _ = len.toNat - (2 : UInt32).toNat :=
              UInt32.toNat_sub_of_le len 2 htwoLen
            _ = input.length - 2 := by simp [hlenNat]
        have htwoSub : (2 : UInt32) ≤ len - 2 := by
          apply UInt32.le_iff_toNat_le.mpr
          rw [hsubNat]
          simp [hsplit]
        apply UInt32.toNat_inj.mp
        calc
          ((len - 2) - 2).toNat = (len - 2).toNat - (2 : UInt32).toNat :=
            UInt32.toNat_sub_of_le (len - 2) 2 htwoSub
          _ = (input.length - 2) - 2 := by simp [hsubNat]
          _ = rest.length := by simp [hsplit]
          _ = (UInt32.ofNat rest.length).toNat := by
            symm
            apply UInt32.toNat_ofNat_of_lt'
            norm_num [UInt32.size] at hinputSmall ⊢
            simp [hsplit] at hinputSmall ⊢
            omega
      simpa only [show loopIterator = secondIterator by decide] using
        (decodeSecondPairValidStore_remaining_field initial (data + 2)
          (len - 2) 1 next).trans hremainingWord
    iterator_error := by
      exact (decodeSecondPairValidStore_read32_unchanged initial (data + 2)
        (len - 2) 1 next (loopIterator + 16) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans (by simpa using hmetaError)
    iterator_chunk := by
      exact (decodeSecondPairValidStore_read32_unchanged initial (data + 2)
        (len - 2) 1 next (loopIterator + 8) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans (by simpa using hmetaChunk)
    iterator_pointer := by
      change paired.wasm.mem.read32 secondIterator = data + 4
      calc
        _ = 2 + (data + 2) :=
          decodeSecondPairValidStore_pointer_field initial (data + 2)
            (len - 2) 1 next
        _ = data + 4 := by bv_decide
    iterator_index := by
      rw [show loopIterator = secondIterator by decide]
      calc
        _ = 1 + 1 :=
          decodeSecondPairValidStore_index_field initial (data + 2)
            (len - 2) 1 next
        _ = 2 := by decide
        _ = UInt32.ofNat ([hi₀, lo₀, hi₁, lo₁].length / 2) := by simp
    error_marker := by
      exact (decodeSecondPairValidStore_read32_unchanged initial (data + 2)
        (len - 2) 1 next coreError (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans (by simpa using hmetaMarker)
    input_bytes := hpairedInput
    input_capacity := hinputCapacity
    input_before_output := by
      rw [allocatorPtr_one_eq bump hbumpNe, hdataBump]
    data_lower := hdataLower
    vector_capacity := by
      exact (decodeSecondPairValidStore_read32_unchanged initial (data + 2)
        (len - 2) 1 next (coreFrame + 60) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
          (decodeInitialVectorStore_capacity_field allocStore ptr seed)
    vector_pointer := by
      exact (decodeSecondPairValidStore_read32_unchanged initial (data + 2)
        (len - 2) 1 next (coreFrame + 64) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
          (decodeInitialVectorStore_pointer_field allocStore ptr seed)
    vector_length := by
      exact (decodeSecondPairValidStore_read32_unchanged initial (data + 2)
        (len - 2) 1 next (coreFrame + 68) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
          (decodeInitialVectorStore_length_field allocStore ptr seed)
    output_bytes := by
      rw [decodeSecondPairValidStore_readBytes_above]
      · exact decodeInitialVectorStore_output allocStore ptr seed (by
          rw [hptrEq]
          exact le_trans (by decide) (le_trans hdataLower (by omega)))
      · rw [allocatorPtr_one_eq bump hbumpNe]
        exact le_trans (by decide) (le_trans hdataLower (by omega))
    output_length := by simp
    output_fits := by decide
    capacity_pos := by decide
    capacity_min := by decide
    output_end := by
      rw [allocatorPtr_one_eq bump hbumpNe, hnewBumpNat]
      congr 1
    output_bound := by
      change newBump.toNat ≤ allocStore.wasm.mem.pages * 65536
      exact hfinishBound
    bump_eq := by
      have hallocBump : allocStore.wasm.mem.read32 1053960 = newBump := by
        simpa [newBump] using hsuccess.read_bump (by
          rw [allocatorPtr_one_eq bump hbumpNe, ← hdataBump]
          have hc := hinputCapacity
          simp [hsplit] at hc
          norm_num
          omega)
      have hinitialBump : initial.wasm.mem.read32 1053960 = newBump := by
        apply (decodeInitialVectorStore_read32_between allocStore ptr seed
          1053960 (by decide) (by
            rw [hptrEq]
            exact (show (1053960 : UInt32).toNat + 4 ≤ 1054000 by decide).trans
              (hdataLower.trans (by omega)))).trans hallocBump
      exact (decodeSecondPairValidStore_read32_above initial (data + 2)
        (len - 2) 1 next 1053960 (by decide)).trans hinitialBump
    bump_signed := by
      rw [hnewBumpNat]
      exact hfinishSmall
    runtime_module := by
      change allocStore.runtime.currentModule = «module»
      rw [hruntimeEq]
      exact hmod
    runtime_host := by
      change allocStore.runtime.currentHost = Universal.envFor «module»
      rw [hruntimeEq]
      exact hhost
    memory_cap := by
      change allocStore.wasm.memoryCap allocStore.runtime.currentModule 0 = 65536
      rw [hruntimeEq]
      exact hmemoryCap.trans hcap
    pages_lower := by
      change 17 ≤ allocStore.wasm.mem.pages
      exact le_trans hpagesLower hpagesMono
    pages_upper := by
      change allocStore.wasm.mem.pages ≤ 65536
      exact hpagesMax
    global_eq := by
      change globalAt? initial 0 = some (.i32 coreFrame)
      exact hmetaGlobal
    status_capacity := hpairedStatus decodeStatusVector 0 (by decide)
      (by decide) hstatusCapacity
    status_pointer := hpairedStatus (decodeStatusVector + 4) 1 (by decide)
      (by decide) hstatusPointer
    status_length := hpairedStatus (decodeStatusVector + 8) 0 (by decide)
      (by decide) hstatusLength
    input_eq := by
      change allocStore.wasm.host.stdio.input = []
      rw [hhostEq]
      exact hinputEmpty
    output_eq := by
      change allocStore.wasm.host.stdio.output = []
      rw [hhostEq]
      exact houtputEmpty
    oom_eq := by
      change allocStore.wasm.host.oom.raised = false
      rw [hhostEq]
      exact hoom }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem decode_after_initial_alloc_outcome
    (input : List UInt8) (store allocStore : MachineStore Universal.State)
    (inputCapacity data bump : UInt32) (hi₀ lo₀ : UInt8)
    (rest : List UInt8) (hiRoute₀ loRoute₀ : HexRoute)
    (hsplit : input = hi₀ :: lo₀ :: rest)
    (heven : input.length % 2 = 0)
    (hhi₀ : hiRoute₀.valid hi₀) (hlo₀ : loRoute₀.valid lo₀)
    (hinputBytes : store.wasm.mem.readBytes data.toNat input.length = input)
    (hinputCapacity : input.length ≤ inputCapacity.toNat)
    (hdataBump : data.toNat + inputCapacity.toNat = bump.toNat)
    (hdataLower : 1054000 ≤ data.toNat)
    (hbumpSigned : bump.toNat < 2 ^ 31)
    (hbumpRead : store.wasm.mem.read32 1053960 = bump)
    (hmod : store.runtime.currentModule = «module»)
    (hhost : store.runtime.currentHost = Universal.envFor «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536)
    (hpagesLower : 17 ≤ store.wasm.mem.pages)
    (hpagesUpper : store.wasm.mem.pages ≤ 65536)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hstatusCapacity : store.wasm.mem.read32 decodeStatusVector = 0)
    (hstatusPointer : store.wasm.mem.read32 (decodeStatusVector + 4) = 1)
    (hstatusLength : store.wasm.mem.read32 (decodeStatusVector + 8) = 0)
    (hinputEmpty : store.wasm.host.stdio.input = [])
    (houtputEmpty : store.wasm.host.stdio.output = [])
    (hoom : store.wasm.host.oom.raised = false)
    (hfinishSmall : bump.toNat + 8 < 2 ^ 31)
    (hsuccess :
      let len := UInt32.ofNat input.length
      let seed := (loRoute₀.nibble lo₀).toUInt8 |||
        ((hiRoute₀.nibble hi₀).toUInt8 <<< (4 : UInt8))
      let first := decodePairValidStore
        (decodeEvenPreparedStore store data len) data len 0 seed
      ByteGrowSuccess first 0 1 8 bump allocStore) :
    let len := UInt32.ofNat input.length
    let seed := (loRoute₀.nibble lo₀).toUInt8 |||
      ((hiRoute₀.nibble hi₀).toUInt8 <<< (4 : UInt8))
    let ptr := allocatorPtr bump 1
    ReachesOrOOM (decodeAfterInitialAllocConfig allocStore data len seed ptr
        store.runtime.entry) (DecodeCoreResult input data) := by
  dsimp only
  let len := UInt32.ofNat input.length
  let seed := (loRoute₀.nibble lo₀).toUInt8 |||
    ((hiRoute₀.nibble hi₀).toUInt8 <<< (4 : UInt8))
  let first := decodePairValidStore
    (decodeEvenPreparedStore store data len) data len 0 seed
  let ptr := allocatorPtr bump 1
  let newBump := allocatorFinish 8 1 bump
  let initial := decodeInitialVectorStore allocStore ptr seed
  have hbaseFacts : DecodeCoreStoreFacts store bump := {
    runtime_module := hmod
    runtime_host := hhost
    memory_cap := hcap
    pages_lower := hpagesLower
    pages_upper := hpagesUpper
    global_eq := hglobal
    status_capacity := hstatusCapacity
    status_pointer := hstatusPointer
    status_length := hstatusLength
    input_eq := hinputEmpty
    output_eq := houtputEmpty
    oom_eq := hoom
    bump_eq := hbumpRead
    bump_zero_or_lower := Or.inr (by omega)
    bump_signed := hbumpSigned }
  have hbumpNe : bump ≠ 0 := by
    intro hz
    have hzNat := congrArg UInt32.toNat hz
    simp at hzNat
    rw [hzNat] at hdataBump
    omega
  have hptrEq : ptr = bump := allocatorPtr_one_eq bump hbumpNe
  have hbound : ptr.toNat + 1 ≤ allocStore.wasm.mem.pages * 65536 := by
    have hf := hsuccess.fresh_eight_finish_bound hbumpNe (by
      norm_num [UInt32.size] at hfinishSmall ⊢
      omega) (by
      change store.wasm.mem.pages < UInt32.size
      norm_num [UInt32.size]
      omega)
    rw [hptrEq]
    omega
  have hpagesLower' : 17 ≤ allocStore.wasm.mem.pages :=
    le_trans hpagesLower hsuccess.pages_mono
  have htoSecond := decode_after_initial_alloc_to_second_pair allocStore data
    len ptr seed store.runtime.entry hpagesLower' (by
      simpa [hptrEq] using hbumpNe) hbound
  cases rest with
  | nil =>
      exact decode_second_empty_outcome input store allocStore inputCapacity
        data bump hi₀ lo₀ hiRoute₀ loRoute₀ (by simpa using hsplit) hhi₀ hlo₀
        hinputBytes hinputCapacity hdataBump hdataLower hbumpSigned hglobal
        hmod hpagesLower hpagesUpper hbaseFacts hfinishSmall hsuccess
  | cons hi₁ rest' =>
      cases rest' with
      | nil => simp [hsplit] at heven
      | cons lo₁ tail =>
          have hmeta := initial_second_metadata store allocStore data len bump
            seed hglobal (by rw [allocatorPtr_one_eq bump hbumpNe]; omega)
            hsuccess
          have hmetaRemaining : initial.wasm.mem.read32
              (secondIterator + 4) = len - 2 := by
            simpa only [initial, ptr] using hmeta.1
          have hmetaError : initial.wasm.mem.read32
              (secondIterator + 16) = secondError := by
            simpa only [initial, ptr] using hmeta.2.1
          have hmetaChunk : initial.wasm.mem.read32
              (secondIterator + 8) = 2 := by
            simpa only [initial, ptr] using hmeta.2.2.1
          have hmetaPtr : initial.wasm.mem.read32 secondIterator = data + 2 := by
            simpa only [initial, ptr, UInt32.add_comm] using
              hmeta.2.2.2.1
          have hmetaIndex : initial.wasm.mem.read32
              (secondIterator + 12) = 1 := by
            simpa only [initial, ptr] using hmeta.2.2.2.2.1
          have hmetaMarker : initial.wasm.mem.read32 secondError = 1114114 := by
            simpa only [initial, ptr] using hmeta.2.2.2.2.2.1
          have hmetaGlobal : globalAt? initial 0 = some (.i32 coreFrame) := by
            simpa only [initial, ptr] using hmeta.2.2.2.2.2.2
          have hinitialPreserve (addr value : UInt32)
              (habove : 1048528 ≤ addr.toNat)
              (hupper : addr.toNat + 4 ≤ 1048560)
              (hstore : store.wasm.mem.read32 addr = value) :
              initial.wasm.mem.read32 addr = value := by
            have hfirst : first.wasm.mem.read32 addr = value :=
              (decodePairValidStore_read32_above
                (decodeEvenPreparedStore store data len) data len 0 seed addr
                (le_trans (by norm_num) habove)).trans
                ((decodeEvenPreparedStore_read32_above store data len addr
                  (le_trans (by norm_num) habove)).trans hstore)
            have halloc : allocStore.wasm.mem.read32 addr = value :=
              (hsuccess.fresh_preserves_read32
                (le_trans hupper (by norm_num))).trans hfirst
            exact (decodeInitialVectorStore_read32_between allocStore ptr seed
              addr habove (by
                rw [hptrEq]
                exact le_trans hupper (le_trans (by norm_num)
                  (le_trans hdataLower (by omega))))).trans halloc
          have hnewBumpNat : newBump.toNat = bump.toNat + 8 := by
            change (allocatorFinish 8 1 bump).toNat = bump.toNat + 8
            rw [allocatorFinish_one_eq_comm 8 bump hbumpNe, UInt32.toNat_add]
            simp only [UInt32.toNat_ofNat]
            rw [Nat.mod_eq_of_lt]
            norm_num [UInt32.size] at hfinishSmall ⊢
            omega
          have hinitialBump : initial.wasm.mem.read32 1053960 = newBump := by
            have hallocBump : allocStore.wasm.mem.read32 1053960 = newBump := by
              simpa [newBump] using hsuccess.read_bump (by
                rw [allocatorPtr_one_eq bump hbumpNe, ← hdataBump]
                have hc := hinputCapacity
                simp [hsplit] at hc
                norm_num
                omega)
            apply (decodeInitialVectorStore_read32_between allocStore ptr seed
              1053960 (by
                change 1048528 ≤ 1053960
                omega) (by
                rw [hptrEq]
                have hs : (1053960 : UInt32).toNat + 4 ≤ 1054000 := by
                  norm_num [UInt32.toNat_ofNat]
                exact hs.trans (hdataLower.trans (by omega)))).trans hallocBump
          have hinvalidMarker (badByte : UInt8) (index : UInt32) :
              (decodeSecondPairInvalidStore initial (data + 2) (len - 2)
                1 badByte index).wasm.mem.read32 coreError =
                badByte.toUInt32 &&& 255 := by
            simp only [decodeSecondPairInvalidStore]
            rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
              Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
              Mem.read32_write32_same]
            all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
          have hinvalidIndex (badByte : UInt8) (index : UInt32) :
              (decodeSecondPairInvalidStore initial (data + 2) (len - 2)
                1 badByte index).wasm.mem.read32 (coreError + 4) = index := by
            simp only [decodeSecondPairInvalidStore]
            rw [Mem.read32_write8_disjoint, Mem.read32_write8_disjoint,
              Mem.read32_write32_disjoint, Mem.read32_write32_same]
            all_goals norm_num [UInt32.toNat_add, UInt32.toNat_ofNat]
          have hbyteMarkerNe (badByte : UInt8) :
              badByte.toUInt32 &&& 255 ≠ (1114114 : UInt32) := by
            intro heq
            have hle : (badByte.toUInt32 &&& 255).toNat ≤ 255 := by
              simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
                UInt32.toNat_ofNat]
              exact Nat.and_le_right
            rw [heq] at hle
            norm_num [UInt32.toNat_ofNat] at hle
          have heightNe : (8 : UInt32) ≠ 0 := by
            intro heq
            have heqNat := congrArg UInt32.toNat heq
            norm_num [UInt32.toNat_ofNat] at heqNat
          have invalidFinalFacts (badByte : UInt8) (index bad : UInt32) :
              DecodeCoreStoreFacts
                (decodeInvalidCoreStore
                  (decodeSecondPairInvalidStore initial (data + 2) (len - 2)
                    1 badByte index) bad index) newBump := by
            let paired := decodeSecondPairInvalidStore initial (data + 2)
              (len - 2) 1 badByte index
            have hpairPreserve (addr value : UInt32)
                (habove : 1048528 ≤ addr.toNat)
                (hread : initial.wasm.mem.read32 addr = value) :
                paired.wasm.mem.read32 addr = value :=
              (decodeSecondPairInvalidStore_read32_above initial (data + 2)
                (len - 2) 1 badByte index addr habove).trans hread
            apply decodeInvalidCoreStore_core_facts paired bad index newBump
            · change allocStore.runtime.currentModule = «module»
              rw [hsuccess.runtime_eq]
              exact hmod
            · change allocStore.runtime.currentHost = Universal.envFor «module»
              rw [hsuccess.runtime_eq]
              exact hhost
            · change allocStore.wasm.memoryCap allocStore.runtime.currentModule 0 =
                65536
              rw [hsuccess.runtime_eq]
              exact (hsuccess.memoryCap_eq store.runtime.currentModule 0).trans hcap
            · change 17 ≤ allocStore.wasm.mem.pages
              exact hpagesLower'
            · change allocStore.wasm.mem.pages ≤ 65536
              exact hsuccess.pages_le_cap hcap hpagesUpper
            · change globalAt? initial 0 = some (.i32 coreFrame)
              exact hmetaGlobal
            · exact hpairPreserve decodeStatusVector 0 (by
                  norm_num [UInt32.toNat_ofNat])
                (hinitialPreserve decodeStatusVector 0 (by
                    norm_num [UInt32.toNat_ofNat]) (by
                    norm_num [UInt32.toNat_ofNat])
                  hstatusCapacity)
            · exact hpairPreserve (decodeStatusVector + 4) 1 (by
                  norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])
                (hinitialPreserve (decodeStatusVector + 4) 1 (by
                    norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])
                  (by norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])
                  hstatusPointer)
            · exact hpairPreserve (decodeStatusVector + 8) 0 (by
                  norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])
                (hinitialPreserve (decodeStatusVector + 8) 0 (by
                    norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])
                  (by norm_num [UInt32.toNat_add, UInt32.toNat_ofNat])
                  hstatusLength)
            · change allocStore.wasm.host.stdio.input = []
              rw [hsuccess.host_eq]
              exact hinputEmpty
            · change allocStore.wasm.host.stdio.output = []
              rw [hsuccess.host_eq]
              exact houtputEmpty
            · change allocStore.wasm.host.oom.raised = false
              rw [hsuccess.host_eq]
              exact hoom
            · exact hpairPreserve 1053960 newBump (by
                norm_num [UInt32.toNat_ofNat]) hinitialBump
            · right
              rw [hnewBumpNat]
              exact le_trans hdataLower (by omega)
            · rw [hnewBumpNat]
              exact hfinishSmall
          have hinputSmall : input.length < 2 ^ 31 := by omega
          have hlenNat : len.toNat = input.length := by
            apply UInt32.toNat_ofNat_of_lt'
            norm_num [UInt32.size] at hinputSmall ⊢
            omega
          have hdata2Nat : (data + 2).toNat = data.toNat + 2 := by
            rw [UInt32.toNat_add]
            simp only [UInt32.toNat_ofNat]
            have hadd : data.toNat + 2 < UInt32.size := by
              norm_num [UInt32.size] at hbumpSigned ⊢
              omega
            rw [Nat.mod_eq_of_lt hadd]
          have hfirstInput : first.wasm.mem.readBytes data.toNat input.length =
              input := by
            rw [decodePairValidStore_readBytes_above]
            · rw [decodeEvenPreparedStore_readBytes_above]
              · exact hinputBytes
              · omega
            · omega
          have hallocInput : allocStore.wasm.mem.readBytes data.toNat
              input.length = input := by
            rw [hsuccess.fresh_preserves_readBytes_disjoint]
            · exact hfirstInput
            · right; omega
          have hinitialInput : initial.wasm.mem.readBytes data.toNat
              input.length = input := by
            rw [decodeInitialVectorStore_readBytes_between]
            · exact hallocInput
            · omega
            · rw [hptrEq]
              omega
          have hhiRead : initial.wasm.mem.read8 (data + 2) = hi₁ := by
            have h := Mem.read8_of_readBytes initial.wasm.mem data.toNat
              input.length 2 input hinitialInput (by simp [hsplit])
              (by simp [hsplit]) (data + 2) hdata2Nat
            simpa [hsplit] using h
          have hdata3Nat : ((data + 2) + 1).toNat = data.toNat + 3 := by
            rw [UInt32.toNat_add]
            simp only [UInt32.toNat_ofNat]
            have hadd : (data + 2).toNat + 1 < UInt32.size := by
              rw [hdata2Nat]
              norm_num [UInt32.size] at hbumpSigned ⊢
              omega
            rw [Nat.mod_eq_of_lt hadd, hdata2Nat]
          have hloRead : initial.wasm.mem.read8 ((data + 2) + 1) = lo₁ := by
            have h := Mem.read8_of_readBytes initial.wasm.mem data.toNat
              input.length 3 input hinitialInput (by simp [hsplit])
              (by simp [hsplit]) ((data + 2) + 1) hdata3Nat
            simpa [hsplit] using h
          have hinputBound : (data + 2).toNat + 2 ≤
              allocStore.wasm.mem.pages * 65536 := by
            rw [hdata2Nat]
            have hc := hinputCapacity
            simp [hsplit] at hc
            rw [hptrEq] at hbound
            omega
          cases hhiValue : hexValue hi₁ with
          | none =>
              let index := (((1 : UInt32) <<< (1 : UInt32)) &&& 255 |||
                ((1 : UInt32) <<< (1 : UInt32)) &&& 4294967040)
              let paired := decodeSecondPairInvalidStore initial (data + 2)
                (len - 2) 1 hi₁ index
              have hpair := decode_second_pair_invalid_high_to_post allocStore
                data len ptr (data + 2) (len - 2) 1 seed hi₁ lo₁
                store.runtime.entry (by rw [hsuccess.runtime_eq]; exact hmod)
                hpagesLower' (hsuccess.pages_le_cap hcap hpagesUpper)
                hinputBound (by rw [hdata2Nat]; omega)
                (by rw [UInt32.toNat_sub_of_le];
                    · rw [hlenNat]; simp [hsplit]
                    · apply UInt32.le_iff_toNat_le.mpr; rw [hlenNat]; simp [hsplit])
                hmetaRemaining hmetaError hmetaChunk hmetaPtr hmetaIndex
                hhiRead hloRead hhiValue
              have hdecode : decode input = none := by
                simp [hsplit, decode, hexValue_of_route_valid hiRoute₀ hi₀ hhi₀,
                  hexValue_of_route_valid loRoute₀ lo₀ hlo₀, hhiValue]
              have hfinish := decode_post_invalid_result input paired data len
                ptr 8 1 (hi₁.toUInt32 &&& 255) index newBump seed
                store.runtime.entry
                (by
                  change allocStore.runtime.currentModule = «module»
                  rw [hsuccess.runtime_eq]
                  exact hmod) hpagesLower'
                (by
                  change globalAt? initial 0 = some (.i32 coreFrame)
                  exact hmetaGlobal)
                (by simpa only [paired] using hinvalidMarker hi₁ index)
                (hbyteMarkerNe hi₁)
                (by simpa only [paired] using hinvalidIndex hi₁ index)
                heightNe (by
                  change store.runtime.entry = allocStore.runtime.entry
                  rw [hsuccess.runtime_eq]
                  simp [first, decodePairValidStore, decodePairBaseStore,
                    decodeEvenPreparedStore]) hdecode
                (Or.inr ⟨heven, by
                  simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
                    UInt32.toNat_ofNat]
                  exact Nat.and_le_right⟩)
                (invalidFinalFacts hi₁ index (hi₁.toUInt32 &&& 255))
              exact ReachesOrOOM.of_reaches
                (htoSecond.trans (hpair.trans hfinish.1)) hfinish.2
          | some hiNibble =>
              obtain ⟨hiRoute₁, hhi₁, _⟩ :=
                hexValue_some_route hi₁ hiNibble hhiValue
              cases hloValue : hexValue lo₁ with
              | none =>
                  let index := ((((1 : UInt32) <<< (1 : UInt32)) ||| 1) &&&
                    255) ||| ((1 : UInt32) <<< (1 : UInt32)) &&& 4294967040
                  let paired := decodeSecondPairInvalidStore initial (data + 2)
                    (len - 2) 1 lo₁ index
                  have hpair := decode_second_pair_invalid_low_to_post allocStore
                    data len ptr (data + 2) (len - 2) 1 seed hi₁ lo₁ hiRoute₁
                    store.runtime.entry (by rw [hsuccess.runtime_eq]; exact hmod)
                    hpagesLower' (hsuccess.pages_le_cap hcap hpagesUpper)
                    hinputBound (by rw [hdata2Nat]; omega)
                    (by rw [UInt32.toNat_sub_of_le];
                        · rw [hlenNat]; simp [hsplit]
                        · apply UInt32.le_iff_toNat_le.mpr; rw [hlenNat]; simp [hsplit])
                    hmetaRemaining hmetaError hmetaChunk hmetaPtr hmetaIndex
                    hhiRead hloRead hhi₁ hloValue
                  have hdecode : decode input = none := by
                    simp [hsplit, decode,
                      hexValue_of_route_valid hiRoute₀ hi₀ hhi₀,
                      hexValue_of_route_valid loRoute₀ lo₀ hlo₀, hhiValue,
                      hloValue]
                  have hfinish := decode_post_invalid_result input paired data
                    len ptr 8 1 (lo₁.toUInt32 &&& 255) index newBump seed
                    store.runtime.entry (by
                      change allocStore.runtime.currentModule = «module»
                      rw [hsuccess.runtime_eq]
                      exact hmod)
                    hpagesLower' (by
                      change globalAt? initial 0 = some (.i32 coreFrame)
                      exact hmetaGlobal)
                    (by simpa only [paired] using hinvalidMarker lo₁ index)
                    (hbyteMarkerNe lo₁)
                    (by simpa only [paired] using hinvalidIndex lo₁ index)
                    heightNe (by
                      change store.runtime.entry = allocStore.runtime.entry
                      rw [hsuccess.runtime_eq]
                      simp [first, decodePairValidStore, decodePairBaseStore,
                        decodeEvenPreparedStore]) hdecode
                    (Or.inr ⟨heven, by
                      simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
                        UInt32.toNat_ofNat]
                      exact Nat.and_le_right⟩)
                    (invalidFinalFacts lo₁ index (lo₁.toUInt32 &&& 255))
                  exact ReachesOrOOM.of_reaches
                    (htoSecond.trans (hpair.trans hfinish.1)) hfinish.2
              | some loNibble =>
                  obtain ⟨loRoute₁, hlo₁, _⟩ :=
                    hexValue_some_route lo₁ loNibble hloValue
                  let next := (loRoute₁.nibble lo₁).toUInt8 |||
                    ((hiRoute₁.nibble hi₁).toUInt8 <<< (4 : UInt8))
                  let paired := decodeSecondPairValidStore initial (data + 2)
                    (len - 2) 1 next
                  have hpair := decode_second_pair_valid_to_loop allocStore data
                    len ptr (data + 2) (len - 2) 1 seed hi₁ lo₁ hiRoute₁
                    loRoute₁ store.runtime.entry
                    (by rw [hsuccess.runtime_eq]; exact hmod) hpagesLower'
                    (hsuccess.pages_le_cap hcap hpagesUpper) hinputBound
                    (by rw [hdata2Nat]; omega)
                    (by rw [UInt32.toNat_sub_of_le];
                        · rw [hlenNat]; simp [hsplit]
                        · apply UInt32.le_iff_toNat_le.mpr; rw [hlenNat]; simp [hsplit])
                    hmetaRemaining hmetaError hmetaChunk hmetaPtr hmetaIndex
                    hhiRead hloRead hhi₁ hlo₁
                  have hinv := decode_loop_initial_invariant input store
                    allocStore inputCapacity data bump hi₀ lo₀ hi₁ lo₁ tail
                    hiRoute₀ loRoute₀ hiRoute₁ loRoute₁ hsplit heven hhi₀ hlo₀
                    hhi₁ hlo₁ hinputBytes hinputCapacity hdataBump hdataLower
                    hbumpSigned hbumpRead hmod hhost hcap hpagesLower
                    hpagesUpper hglobal hstatusCapacity hstatusPointer
                    hstatusLength hinputEmpty houtputEmpty hoom hfinishSmall hsuccess
                  have hreturn : store.runtime.entry = paired.runtime.entry := by
                    change store.runtime.entry = allocStore.runtime.entry
                    rw [hsuccess.runtime_eq]
                    simp [first, decodePairValidStore, decodePairBaseStore,
                      decodeEvenPreparedStore]
                  exact ReachesOrOOM.prependReaches (htoSecond.trans hpair)
                    (hinv.outcome store.runtime.entry hreturn)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem decode_after_read_success_outcome
    (input : List UInt8) (config : Config Universal.State)
    (hsuccess : ReadToEndSuccess input config) :
    ReachesOrOOM config (fun final =>
      ∃ data, DecodeCoreResult input data final) := by
  rcases hsuccess with ⟨store, inputCapacity, data, bump, rfl,
    hinputEmpty, houtputEmpty, hoom, hmod, hhost, hcap, hpagesLower,
    hpagesUpper, hglobal, hstatusCapacity, hstatusPointer, hstatusLength,
    hcapacityRead, hdataRead, hlenRead, hbumpRead, hinputBytes, hinputCapacity,
    hdataBumpOrEmpty, hdataLowerOrEmpty, hbumpBase, hbumpSigned, hinputEnd⟩
  have hbaseFacts : DecodeCoreStoreFacts store bump := {
    runtime_module := hmod
    runtime_host := hhost
    memory_cap := hcap
    pages_lower := hpagesLower
    pages_upper := hpagesUpper
    global_eq := hglobal
    status_capacity := hstatusCapacity
    status_pointer := hstatusPointer
    status_length := hstatusLength
    input_eq := hinputEmpty
    output_eq := houtputEmpty
    oom_eq := hoom
    bump_eq := hbumpRead
    bump_zero_or_lower := hbumpBase
    bump_signed := hbumpSigned }
  let len := UInt32.ofNat input.length
  have hprefix := decode_after_read_to_core_call store data len
    (by simpa [decodeInputVector] using hdataRead)
    (by simpa [len, decodeInputVector] using hlenRead)
    (by
      change 1048576 ≤ store.wasm.mem.pages * 65536
      omega)
  apply ReachesOrOOM.prependReaches hprefix
  by_cases heven : input.length % 2 = 0
  · have hevenWord : len &&& (1 : UInt32) = 0 := by
      exact ofNat_length_and_one_eq_zero input heven
    cases input with
    | nil =>
        have hreach := decode_core_empty_reaches store data hmod hglobal
          hpagesLower
        exact ReachesOrOOM.of_reaches hreach
          ⟨data, decodeEmptyCoreStore_result store data bump hbaseFacts⟩
    | cons hi tail₀ =>
        cases tail₀ with
        | nil => simp at heven
        | cons lo rest =>
            have hsplit : hi :: lo :: rest = hi :: lo :: rest := rfl
            have hdataLower : 1054000 ≤ data.toNat := by
              exact hdataLowerOrEmpty.resolve_left (by simp)
            have hdataBump : data.toNat + inputCapacity.toNat = bump.toNat := by
              exact hdataBumpOrEmpty.resolve_left (by simp)
            have hlenNat : len.toNat = (hi :: lo :: rest).length := by
              apply UInt32.toNat_ofNat_of_lt'
              have hcapacityBump : inputCapacity.toNat ≤ bump.toNat := by
                omega
              have hinputSmall : (hi :: lo :: rest).length < 2 ^ 31 :=
                lt_of_le_of_lt hinputCapacity
                  (lt_of_le_of_lt hcapacityBump hbumpSigned)
              norm_num [UInt32.size] at hinputSmall ⊢
              omega
            have hinputBound : data.toNat + 2 ≤
                store.wasm.mem.pages * 65536 := by
              have hc := hinputCapacity
              simp at hc
              omega
            have hhiRead : store.wasm.mem.read8 data = hi := by
              exact Mem.read8_of_readBytes store.wasm.mem data.toNat
                (hi :: lo :: rest).length 0 (hi :: lo :: rest) hinputBytes
                (by simp) (by simp) data (by simp)
            have hdata1Nat : (data + 1).toNat = data.toNat + 1 := by
              rw [UInt32.toNat_add]
              simp only [UInt32.toNat_ofNat]
              have hadd : data.toNat + 1 < UInt32.size := by
                norm_num [UInt32.size] at hbumpSigned ⊢
                omega
              rw [Nat.mod_eq_of_lt hadd]
            have hloRead : store.wasm.mem.read8 (data + 1) = lo := by
              exact Mem.read8_of_readBytes store.wasm.mem data.toNat
                (hi :: lo :: rest).length 1 (hi :: lo :: rest) hinputBytes
                (by simp) (by simp) (data + 1) hdata1Nat
            cases hhiValue : hexValue hi with
            | none =>
                let paired := decodePairInvalidStore
                  (decodeEvenPreparedStore store data len) data len 0 hi 0
                let finalStore := decodeInvalidCoreStore paired
                  (hi.toUInt32 &&& 255) 0
                have hreach := decode_core_invalid_high_first_reaches store
                  data len hi lo hmod hglobal hpagesLower hpagesUpper
                  hevenWord (by rw [hlenNat]; simp) hdataLower hinputBound
                  hhiRead hloRead hhiValue
                apply ReachesOrOOM.of_reaches hreach
                exact ⟨data, Or.inr ⟨finalStore, hi.toUInt32 &&& 255, rfl,
                  by simp [decode, hhiValue],
                  decodeInvalidCoreStore_result_tag paired
                    (hi.toUInt32 &&& 255) 0,
                  decodeInvalidCoreStore_result_payload paired
                    (hi.toUInt32 &&& 255) 0,
                  Or.inr ⟨heven, by
                    simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
                      UInt32.toNat_ofNat]
                    exact Nat.and_le_right⟩,
                  ⟨bump, decodeFirstInvalidCoreStore_core_facts store data len
                    0 (hi.toUInt32 &&& 255) 0 bump hi hbaseFacts⟩⟩⟩
            | some hiNibble =>
                obtain ⟨hiRoute, hhi, _⟩ :=
                  hexValue_some_route hi hiNibble hhiValue
                cases hloValue : hexValue lo with
                | none =>
                    let paired := decodePairInvalidStore
                      (decodeEvenPreparedStore store data len) data len 0 lo 1
                    let finalStore := decodeInvalidCoreStore paired
                      (lo.toUInt32 &&& 255) 1
                    have hreach := decode_core_invalid_low_first_reaches store
                      data len hi lo hiRoute hmod hglobal hpagesLower
                      hpagesUpper hevenWord (by rw [hlenNat]; simp)
                      hdataLower hinputBound hhiRead hloRead hhi hloValue
                    apply ReachesOrOOM.of_reaches hreach
                    exact ⟨data, Or.inr ⟨finalStore, lo.toUInt32 &&& 255, rfl,
                      by simp [decode, hhiValue, hloValue],
                      decodeInvalidCoreStore_result_tag paired
                        (lo.toUInt32 &&& 255) 1,
                      decodeInvalidCoreStore_result_payload paired
                        (lo.toUInt32 &&& 255) 1,
                      Or.inr ⟨heven, by
                        simp only [UInt32.toNat_and, UInt8.toUInt32_toNat,
                          UInt32.toNat_ofNat]
                        exact Nat.and_le_right⟩,
                      ⟨bump, decodeFirstInvalidCoreStore_core_facts store data
                        len 0 (lo.toUInt32 &&& 255) 1 bump lo hbaseFacts⟩⟩⟩
                | some loNibble =>
                    obtain ⟨loRoute, hlo, _⟩ :=
                      hexValue_some_route lo loNibble hloValue
                    let seed := (loRoute.nibble lo).toUInt8 |||
                      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
                    let first := decodePairValidStore
                      (decodeEvenPreparedStore store data len) data len 0 seed
                    have hfirst := decode_core_valid_first_to_alloc_reaches
                      store data len hi lo hiRoute loRoute hmod hglobal
                      hpagesLower hpagesUpper hevenWord
                      (by rw [hlenNat]; simp) hdataLower hinputBound hhiRead
                      hloRead hhi hlo
                    have hfirstBump : first.wasm.mem.read32 1053960 = bump := by
                      simp only [first, decodePairValidStore,
                        decodePairBaseStore, decodeEvenPreparedStore]
                      rw [Mem.read32_write8_disjoint,
                        Mem.read32_write8_disjoint,
                        Mem.read32_write32_disjoint,
                        Mem.read32_write32_disjoint,
                        Mem.read32_write32_disjoint,
                        Mem.read32_write32_disjoint,
                        Mem.read32_write32_disjoint,
                        Mem.read32_write32_disjoint,
                        Mem.read32_write64_disjoint,
                        Mem.read32_write32_disjoint]
                      · exact hbumpRead
                      all_goals decide
                    have hbumpNe : bump ≠ 0 := by
                      intro hz
                      have hzNat := congrArg UInt32.toNat hz
                      simp at hzNat
                      rw [hzNat] at hdataBump
                      omega
                    have halloc := decode_initial_alloc_outcome first data len
                      bump seed
                      (by simpa [first, decodePairValidStore,
                        decodePairBaseStore, decodeEvenPreparedStore] using hmod)
                      (by simpa [first, decodePairValidStore,
                        decodePairBaseStore, decodeEvenPreparedStore] using hhost)
                      hfirstBump
                      (by
                        change 1053964 ≤ first.wasm.mem.pages * 65536
                        change 1053964 ≤ store.wasm.mem.pages * 65536
                        omega)
                      (by
                        change store.wasm.mem.pages < 4294967295
                        omega)
                      hbumpNe hbumpSigned
                    apply ReachesOrOOM.prependReaches hfirst
                    rcases halloc with ⟨allocStore, hfinishSmall, hgrow,
                        hallocReach⟩ | htrap
                    · apply ReachesOrOOM.prependReaches hallocReach
                      have hentry : first.runtime.entry = store.runtime.entry := by
                        simp [first, decodePairValidStore, decodePairBaseStore,
                          decodeEvenPreparedStore]
                      rw [hentry]
                      apply (decode_after_initial_alloc_outcome
                        (hi :: lo :: rest) store allocStore inputCapacity data
                        bump hi lo rest hiRoute loRoute rfl heven hhi hlo
                        hinputBytes hinputCapacity hdataBump hdataLower
                        hbumpSigned hbumpRead hmod hhost hcap hpagesLower
                        hpagesUpper hglobal hstatusCapacity hstatusPointer
                        hstatusLength hinputEmpty houtputEmpty hoom hfinishSmall hgrow
                        ).bind
                      intro final hresult
                      exact ReachesOrOOM.refl final _ ⟨data, hresult⟩
                    · exact Or.inr htrap
  · have hoddWord : len &&& (1 : UInt32) ≠ 0 := by
      intro hz
      have hzNat := congrArg UInt32.toNat hz
      simp [len, UInt32.toNat_and] at hzNat
      omega
    have hreach := decode_core_odd_reaches store data len hmod hglobal
      hpagesLower hoddWord
    apply ReachesOrOOM.of_reaches hreach
    refine ⟨data, Or.inr ⟨decodeOddStore store, 1114112, rfl,
      decode_none_of_odd_length input heven, decodeOddStore_result_tag store,
      decodeOddStore_result_payload store, Or.inl ⟨by omega, rfl⟩,
      ⟨bump, decodeOddStore_core_facts store bump hbaseFacts⟩⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem decode_core_outcome (input : List UInt8) :
    ReachesOrOOM (decodeConfig input) (fun final =>
      ∃ data, DecodeCoreResult input data final) := by
  apply (decode_read_to_end_outcome input).bind
  intro config hsuccess
  exact decode_after_read_success_outcome input config hsuccess

end Project.HexDecodeStdio
