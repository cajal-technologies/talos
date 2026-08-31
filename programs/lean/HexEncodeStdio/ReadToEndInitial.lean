import HexEncodeStdio.ReadToEndLoop

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem first_capacity_toNat (bytes : List UInt8) (hnil : bytes ≠ [])
    (hle : bytes.length ≤ 32) :
    (reserveNewCapacity 0 (UInt32.ofNat bytes.length) 0).toNat =
      max bytes.length 8 := by
  have hsmall : bytes.length < UInt32.size := by
    norm_num [UInt32.size]
    omega
  have hcountNat : (UInt32.ofNat bytes.length).toNat = bytes.length :=
    UInt32.toNat_ofNat_of_lt' hsmall
  have hpos : 0 < (UInt32.ofNat bytes.length).toNat := by
    rw [hcountNat]
    exact List.length_pos_iff.mpr hnil
  simp only [reserveNewCapacity, reserveCandidate, reserveRequired,
    reserveDoubled, UInt32.zero_add, UInt32.zero_shiftLeft]
  rw [if_pos (UInt32.pos_iff_ne_zero.mpr (by
    intro hz
    rw [hz] at hpos
    simp at hpos))]
  by_cases hgt : (UInt32.ofNat bytes.length) > 8
  · rw [if_pos hgt, max_eq_left]
    · exact hcountNat
    · have hn := UInt32.le_iff_toNat_le.mp (UInt32.le_of_lt hgt)
      simpa [hcountNat] using hn
  · rw [if_neg hgt, max_eq_right]
    · decide
    · have hnnot : ¬(8 : UInt32).toNat <
          (UInt32.ofNat bytes.length).toNat := by
        intro hn
        exact hgt (UInt32.lt_iff_toNat_lt.mpr hn)
      have hn := Nat.le_of_not_gt hnnot
      simpa [hcountNat] using hn

theorem Mem.readBytes_copy_destination (m : Mem) (dst src len : Nat) :
    (m.copy dst src len).readBytes dst len = m.readBytes src len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp [Mem.readBytes, Mem.copy, hi]

theorem Mem.readBytes_writeBytes_same (m : Mem) (off : Nat)
    (bytes : List UInt8) :
    (m.writeBytes off bytes).readBytes off bytes.length = bytes := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < bytes.length := by simpa [Mem.readBytes] using hleft
    simp [Mem.readBytes, Mem.writeBytes, hi]

theorem Mem.read32_write8_disjoint (m : Mem) (address writeAddress : UInt32)
    (value : UInt8)
    (h : address.toNat + 4 ≤ writeAddress.toNat ∨
      writeAddress.toNat + 1 ≤ address.toNat) :
    (m.write8 writeAddress value).read32 address = m.read32 address := by
  simp only [Mem.read32, Mem.write8]
  rw [if_neg, if_neg, if_neg, if_neg]
  all_goals rcases h with hbefore | hafter <;> omega

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 1048576 in
theorem first_nonempty_read_invariant
    (input bytes : List UInt8)
    (allocStore : MachineStore Universal.State)
    (hbytes : bytes = input.take 32) (hnil : bytes ≠ [])
    (hsuccess :
      let entryStore := encodeFrameStore input
      let framed := readToEndFrameStore entryStore readToEndStack
      let after := readAdapterResultStore
        (readChunkFrameStore framed firstChunkFrame)
        firstChunkResult firstChunkBuffer bytes
      let count := UInt32.ofNat bytes.length
      ByteGrowSuccess (reserveFrameStore after (firstChunkFrame - 16))
        0 1 (reserveNewCapacity 0 count 0) 0 allocStore) :
    let entryStore := encodeFrameStore input
    let framed := readToEndFrameStore entryStore readToEndStack
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    let capacity := reserveNewCapacity 0 count 0
    let data := allocatorPtr 0 1
    let bump := allocatorFinish capacity 1 0
    let reserved := reserveFinishStore
      (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
        data capacity)
      readToEndVector data capacity firstChunkFrame
    let finalStore := readChunkFinishedStore
      (readChunkCopiedStore reserved data firstChunkBuffer count)
      readToEndResult readToEndVector count 0 readToEndStack
    ReadToEndInv input bytes (input.drop bytes.length) finalStore capacity data
      count bump := by
  dsimp only
  let entryStore := encodeFrameStore input
  let framed := readToEndFrameStore entryStore readToEndStack
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let count := UInt32.ofNat bytes.length
  let capacity := reserveNewCapacity 0 count 0
  let data := allocatorPtr 0 1
  let bump := allocatorFinish capacity 1 0
  let base := reserveFrameStore after (firstChunkFrame - 16)
  let postGrow := growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
    data capacity
  let reserved := reserveFinishStore postGrow readToEndVector data capacity
    firstChunkFrame
  let copied := readChunkCopiedStore reserved data firstChunkBuffer count
  let finalStore := readChunkFinishedStore copied readToEndResult
    readToEndVector count 0 readToEndStack
  change ByteGrowSuccess base 0 1 capacity 0 allocStore at hsuccess
  change ReadToEndInv input bytes (input.drop bytes.length) finalStore capacity
    data count bump
  have hlen : bytes.length ≤ 32 := by
    rw [hbytes, List.length_take]
    omega
  have hcountNat : count.toNat = bytes.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size]
    omega
  have hcapacityNat : capacity.toNat = max bytes.length 8 := by
    exact first_capacity_toNat bytes hnil hlen
  have hcapacityLe : capacity.toNat ≤ 32 := by
    rw [hcapacityNat]
    omega
  have hdataNat : data.toNat = 1054000 := by decide
  have hbumpNat : bump.toNat = 1054000 + capacity.toNat := by
    have hptr : allocatorPtr 0 1 = 1054000 := by decide
    simp only [bump, allocatorFinish, hptr, UInt32.toNat_add,
      UInt32.reduceToNat]
    rw [Nat.mod_eq_of_lt]
    · omega
    · exact lt_of_le_of_lt (Nat.add_le_add_right hcapacityLe 1054000)
        (show 32 + 1054000 < 2 ^ 32 by norm_num)
  have hpagesMono : 17 ≤ allocStore.wasm.mem.pages := by
    have hm := hsuccess.pages_mono
    have hentryPages : entryStore.wasm.mem.pages = 17 := by
      simp [entryStore, encodeFrameStore, encodeInitialStore]
      decide
    have hframedPages : framed.wasm.mem.pages = 17 := by
      simpa only [framed, readToEndFrameStore_pages] using hentryPages
    have hafterPages : after.wasm.mem.pages = 17 := by
      simpa only [after, readAdapterResultStore_pages,
        readChunkFrameStore_pages] using hframedPages
    have hbasePages : base.wasm.mem.pages = 17 := by
      simpa only [base, reserveFrameStore_mem] using hafterPages
    rw [← hbasePages]
    exact hm
  have hhost := hsuccess.host_eq
  have hruntime := hsuccess.runtime_eq
  refine
    { split := ?_
      input_eq := ?_
      output_eq := ?_
      oom_eq := ?_
      runtime_entry := ?_
      runtime_module := ?_
      runtime_host := ?_
      memory_cap := ?_
      pages_lower := ?_
      pages_upper := ?_
      global_eq := ?_
      capacity_eq := ?_
      data_eq := ?_
      length_eq := ?_
      bump_eq := ?_
      table_eq := ?_
      bytes_eq := ?_
      length_nat := hcountNat
      length_le_capacity := ?_
      capacity_pos := ?_
      capacity_min := ?_
      data_lower := ?_
      data_capacity_bump := ?_
      capacity_headroom := ?_
      bump_signed := ?_
      data_bound := ?_ }
  · rw [hbytes]
    rw [List.length_take]
    by_cases hlarge : 32 ≤ input.length
    · rw [min_eq_left hlarge]
      exact List.take_append_drop 32 input
    · rw [min_eq_right (by omega), List.take_of_length_le (by omega),
        List.drop_eq_nil_of_le (by omega), List.append_nil]
  · rw [show finalStore.wasm.host = allocStore.wasm.host by rfl, hhost]
    change after.wasm.host.stdio.input = input.drop bytes.length
    rw [readAdapterResultStore_input]
    rfl
  · rw [show finalStore.wasm.host = allocStore.wasm.host by rfl, hhost]
    change after.wasm.host.stdio.output = []
    simp [after, readAdapterResultStore, universalReadStore,
      afterUniversalRead, framed, entryStore, encodeFrameStore,
      encodeInitialStore, Universal.State.ofInput, StdIO.State.ofInput]
    rfl
  · rw [show finalStore.wasm.host = allocStore.wasm.host by rfl, hhost]
    change after.wasm.host.oom.raised = false
    simp [after, readAdapterResultStore, universalReadStore,
      afterUniversalRead, framed, entryStore, encodeFrameStore,
      encodeInitialStore, Universal.State.ofInput, StdIO.State.ofInput]
    rfl
  · rw [show finalStore.runtime = allocStore.runtime by rfl, hruntime]
    rfl
  · rw [show finalStore.runtime = allocStore.runtime by rfl, hruntime]
    rfl
  · rw [show finalStore.runtime = allocStore.runtime by rfl, hruntime]
    rfl
  · change allocStore.wasm.memoryCap allocStore.runtime.currentModule 0 = 65536
    rw [hruntime, hsuccess.memoryCap_eq]
    rfl
  · change 17 ≤ allocStore.wasm.mem.pages
    exact hpagesMono
  · change allocStore.wasm.mem.pages ≤ 65536
    have hcap : base.wasm.memoryCap base.runtime.currentModule 0 = 65536 := by rfl
    have hp : base.wasm.mem.pages ≤ 65536 := by
      have hentryPages : entryStore.wasm.mem.pages = 17 := by
        simp [entryStore, encodeFrameStore, encodeInitialStore]
        decide
      have hframedPages : framed.wasm.mem.pages = 17 := by
        simpa only [framed, readToEndFrameStore_pages] using hentryPages
      have hafterPages : after.wasm.mem.pages = 17 := by
        simpa only [after, readAdapterResultStore_pages,
          readChunkFrameStore_pages] using hframedPages
      have hbasePages : base.wasm.mem.pages = 17 := by
        simpa only [base, reserveFrameStore_mem] using hafterPages
      rw [hbasePages]
      decide
    exact hsuccess.pages_le_cap hcap hp
  · simp only [finalStore, readChunkFinishedStore, globalAt?,
      canonicalGlobalIndex_zero]
    have hzero : 0 < copied.wasm.globals.globals.length := by
      have hentryGlobal : globalAt? entryStore 0 = some (.i32 1048544) := by
        simp [entryStore, encodeFrameStore, encodeInitialStore, globalAt?,
          canonicalGlobalIndex_zero]
        decide
      have hframedGlobal :
          globalAt? framed 0 = some (.i32 readToEndStack) := by
        simp only [framed, readToEndFrameStore, globalAt?,
          canonicalGlobalIndex_zero] at hentryGlobal ⊢
        have hz := (getElem?_eq_some_iff.mp hentryGlobal).1
        exact List.getElem?_set_eq_of_lt (.i32 readToEndStack) hz
      have hchunkGlobal := readChunkFrameStore_global_zero framed
        firstChunkFrame readToEndStack hframedGlobal
      have hafterGlobal : globalAt? after 0 = some (.i32 firstChunkFrame) := by
        simp only [after, readAdapterResultStore_globalAt]
        exact hchunkGlobal
      have hbaseGlobal := reserveFrameStore_global_zero after
        (firstChunkFrame - 16) firstChunkFrame hafterGlobal
      have hallocGlobal :
          globalAt? allocStore 0 = some (.i32 (firstChunkFrame - 16)) :=
        (hsuccess.globalAt_eq 0).trans hbaseGlobal
      have hzeroAlloc : 0 < allocStore.wasm.globals.globals.length :=
        (getElem?_eq_some_iff.mp hallocGlobal).1
      simpa [copied, readChunkCopiedStore, reserved, reserveFinishStore,
        reserveVectorStore, postGrow, growResultOkStore] using hzeroAlloc
    exact List.getElem?_set_eq_of_lt (.i32 readToEndStack) hzero
  · simp only [finalStore, readChunkFinishedStore, copied,
      readChunkCopiedStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint,
      Mem.read32_copy_before _ _ _ _ _ (by rw [hdataNat]; decide)]
    · simp only [reserved, reserveFinishStore, reserveVectorStore]
      rw [Mem.read32_write32_disjoint]
      · exact Mem.read32_write32_same _ _ _
      · decide
    all_goals decide
  · simp only [finalStore, readChunkFinishedStore, copied,
      readChunkCopiedStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write8_disjoint,
      Mem.read32_write32_disjoint,
      Mem.read32_copy_before _ _ _ _ _ (by rw [hdataNat]; decide)]
    · exact reserveFinishStore_read_data _ _ _ _ _
    all_goals decide
  · simp only [finalStore, readChunkFinishedStore]
    rw [show readToEndStack + 12 = readToEndVector + 8 by decide]
    simpa using (Mem.read32_write32_same
      (((copied.wasm.mem.write32 (readToEndResult + 4) count).write8
        readToEndResult 4)) (readToEndVector + 8) count)
  · have hb := hsuccess.read_bump (by decide)
    simp [finalStore, readChunkFinishedStore, copied, readChunkCopiedStore,
      reserved, reserveFinishStore, reserveVectorStore, postGrow,
      growResultOkStore, base] at ⊢ hb
    exact hb
  · have hentryTable : entryStore.wasm.mem.readBytes 1048576 16 =
        Project.HexEncodeStdio.Hex.asciiTable := by
      simp [entryStore, encodeFrameStore, encodeInitialStore, Mem.readBytes]
      decide
    have hframedTable : framed.wasm.mem.readBytes 1048576 16 =
        Project.HexEncodeStdio.Hex.asciiTable := by
      simp only [framed, readToEndFrameStore]
      rw [Mem.readBytes_write64_disjoint,
        Mem.readBytes_write32_disjoint]
      · exact hentryTable
      all_goals right <;> decide
    have hchunkTable :
        (readChunkFrameStore framed firstChunkFrame).wasm.mem.readBytes
          1048576 16 = Project.HexEncodeStdio.Hex.asciiTable := by
      simp only [readChunkFrameStore]
      rw [Mem.readBytes_write64_disjoint, Mem.readBytes_write64_disjoint,
        Mem.readBytes_write64_disjoint, Mem.readBytes_write64_disjoint]
      · exact hframedTable
      all_goals right <;> decide
    have hafterTable : after.wasm.mem.readBytes 1048576 16 =
        Project.HexEncodeStdio.Hex.asciiTable := by
      simp only [after, readAdapterResultStore, universalReadStore]
      rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint,
        Mem.readBytes_writeBytes_disjoint]
      · exact hchunkTable
      · right
        simp [firstChunkBuffer]
        omega
      · right; decide
      · right; decide
    have hallocTable : allocStore.wasm.mem.readBytes 1048576 16 =
        Project.HexEncodeStdio.Hex.asciiTable := by
      exact (hsuccess.fresh_preserves_bytes 1048576 16
        (Or.inl (by decide))).trans (by simpa [base] using hafterTable)
    simp only [finalStore, readChunkFinishedStore, copied,
      readChunkCopiedStore, reserved, reserveFinishStore, reserveVectorStore,
      postGrow, growResultOkStore]
    rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint,
      Mem.readBytes_write32_disjoint, Mem.readBytes_copy_before,
      Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
      Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
      Mem.readBytes_write32_disjoint]
    · exact hallocTable
    all_goals first | left; decide | right; decide | rw [hdataNat]; decide
  · have hafterBytes :
        after.wasm.mem.readBytes firstChunkBuffer.toNat bytes.length = bytes := by
      simp only [after, readAdapterResultStore, universalReadStore]
      rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint]
      · exact Mem.readBytes_writeBytes_same _ _ _
      · left
        simp [firstChunkBuffer, firstChunkResult]
        try rw [hcountNat]
        omega
      · left
        simp [firstChunkBuffer, firstChunkResult]
        try rw [hcountNat]
        omega
    have hallocBytes :
        allocStore.wasm.mem.readBytes firstChunkBuffer.toNat bytes.length =
          bytes := by
      exact (hsuccess.fresh_preserves_bytes firstChunkBuffer.toNat bytes.length
        (Or.inl (by simp [firstChunkBuffer]; omega))).trans
          (by simpa [base] using hafterBytes)
    simp only [finalStore, readChunkFinishedStore, copied,
      readChunkCopiedStore]
    rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint,
      Mem.readBytes_write32_disjoint, hcountNat,
      Mem.readBytes_copy_destination]
    · simp only [reserved, reserveFinishStore, reserveVectorStore,
        postGrow, growResultOkStore]
      rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
        Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
        Mem.readBytes_write32_disjoint]
      · exact hallocBytes
      · right; simp [firstChunkBuffer]
      · right; simp [firstChunkBuffer]
      · right; simp [firstChunkBuffer]
      · left; simp [firstChunkBuffer]; omega
      · left; simp [firstChunkBuffer]; omega
    · right; rw [hdataNat]; decide
    · right; rw [hdataNat]; decide
    · right; rw [hdataNat]; decide
  · rw [hcountNat, hcapacityNat]
    exact Nat.le_max_left _ _
  · rw [hcapacityNat]
    omega
  · rw [hcapacityNat]
    omega
  · exact hdataNat.ge
  · rw [hdataNat, hbumpNat]
  · rw [hbumpNat, hcapacityNat]
    omega
  · rw [hbumpNat]
    omega
  · rw [hdataNat]
    change 1054000 + capacity.toNat ≤ finalStore.wasm.mem.pages * 65536
    change 1054000 + capacity.toNat ≤ allocStore.wasm.mem.pages * 65536
    have hp := hpagesMono
    omega

end Project.HexEncodeStdio
