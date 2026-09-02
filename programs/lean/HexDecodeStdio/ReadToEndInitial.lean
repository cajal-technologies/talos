import HexDecodeStdio.ReadToEndLoop

namespace Project.HexDecodeStdio

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

theorem Mem.readBytes_writeBytes_self (m : Mem) (off : Nat)
    (bytes : List UInt8) :
    (m.writeBytes off bytes).readBytes off bytes.length = bytes := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < bytes.length := by simpa [Mem.readBytes] using hleft
    simp [Mem.readBytes, Mem.writeBytes, hi]

theorem Mem.read32_write8_disjoint (m : Mem) (writeAddr readAddr : UInt32)
    (value : UInt8)
    (h : readAddr.toNat + 4 ≤ writeAddr.toNat ∨
      writeAddr.toNat + 1 ≤ readAddr.toNat) :
    (m.write8 writeAddr value).read32 readAddr = m.read32 readAddr := by
  simp only [Mem.read32, Mem.write8]
  rw [if_neg, if_neg, if_neg, if_neg]
  all_goals rcases h with hbefore | hafter <;> omega

theorem readChunkFinishedStore_read32_other
    (store : MachineStore Universal.State)
    (out vector count oldLength sp addr : UInt32)
    (houtCount : addr.toNat + 4 ≤ (out + 4).toNat ∨
      (out + 4).toNat + 4 ≤ addr.toNat)
    (houtTag : addr.toNat + 4 ≤ out.toNat ∨ out.toNat + 1 ≤ addr.toNat)
    (hlength : addr.toNat + 4 ≤ (vector + 8).toNat ∨
      (vector + 8).toNat + 4 ≤ addr.toNat) :
    (readChunkFinishedStore store out vector count oldLength sp).wasm.mem.read32
        addr = store.wasm.mem.read32 addr := by
  simp only [readChunkFinishedStore]
  rw [Mem.read32_write32_disjoint _ _ _ _ hlength,
    Mem.read32_write8_disjoint _ _ _ _ houtTag,
    Mem.read32_write32_disjoint _ _ _ _ houtCount]

theorem ByteGrowSuccess.fresh_preserves_readBytes
    {store final : MachineStore Universal.State}
    {oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr newCapacity oldBump final)
    (off len : Nat) (hbefore : off + len ≤ 1053960) :
    final.wasm.mem.readBytes off len = store.wasm.mem.readBytes off len := by
  cases h with
  | freshNoGrow hzero hfit =>
      exact Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hbefore)
  | freshGrow hzero memory previousPages hgrow =>
      simp only [allocatorBumpStore, allocatorGrownStore]
      rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hbefore)]
      simp only [Mem.readBytes, Mem.grow_success_bytes_eq _ _ _ _ _ hgrow]
  | reallocNoGrow hnonzero hfit => contradiction
  | reallocGrow hnonzero memory previousPages hgrow => contradiction

set_option maxHeartbeats 800000 in
set_option maxRecDepth 1048576 in
theorem first_nonempty_read_invariant
    (input bytes : List UInt8)
    (allocStore : MachineStore Universal.State)
    (hbytes : bytes = input.take 32) (hnil : bytes ≠ [])
    (hsuccess :
      let entryStore := decodeFrameStore (decodeConfig input).store
      let framed := readToEndFrameStore entryStore readToEndStack
      let after := readAdapterResultStore
        (readChunkFrameStore framed firstChunkFrame)
        firstChunkResult firstChunkBuffer bytes
      let count := UInt32.ofNat bytes.length
      ByteGrowSuccess (reserveFrameStore after (firstChunkFrame - 16))
        0 1 (reserveNewCapacity 0 count 0) 0 allocStore) :
    let entryStore := decodeFrameStore (decodeConfig input).store
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
  let entryStore := decodeFrameStore (decodeConfig input).store
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
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt
      (Nat.add_le_add_right hcapacityLe 1054000)
      (show 32 + 1054000 < 2 ^ 32 by norm_num))]
    omega
  have hpagesMono : 17 ≤ allocStore.wasm.mem.pages := by
    have hm := hsuccess.pages_mono
    have hentryPages : entryStore.wasm.mem.pages = 17 := by rfl
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
  have hentryStatusCapacity :
      entryStore.wasm.mem.read32 decodeStatusVector = 0 := by
    simp [entryStore, decodeFrameStore, decodeConfig, Mem.read32,
      Mem.write64, Mem.write32] <;> bv_decide
  have hentryStatusPointer :
      entryStore.wasm.mem.read32 (decodeStatusVector + 4) = 1 := by
    simp [entryStore, decodeFrameStore, decodeConfig, Mem.read32,
      Mem.write64, Mem.write32] <;> bv_decide
  have hentryStatusLength :
      entryStore.wasm.mem.read32 (decodeStatusVector + 8) = 0 := by
    simp [entryStore, decodeFrameStore, decodeConfig, Mem.read32,
      Mem.write64, Mem.write32] <;> bv_decide
  have hfinalStatus (addr value : UInt32)
      (haddrLower : 1048540 ≤ addr.toNat)
      (haddrUpper : addr.toNat + 4 ≤ 1048560)
      (hentry : entryStore.wasm.mem.read32 addr = value) :
      finalStore.wasm.mem.read32 addr = value := by
    have hframed : framed.wasm.mem.read32 addr = value := by
      simp only [framed, readToEndFrameStore]
      rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
      · exact hentry
      all_goals right
      all_goals exact le_trans (by decide) haddrLower
    have hafter : after.wasm.mem.read32 addr = value := by
      rw [readAdapterResultStore_read32_disjoint]
      · exact (readChunkFrameStore_read32_after_frame framed firstChunkFrame
          addr (le_trans (by decide) haddrLower)
          (le_trans (by decide) haddrLower)
          (le_trans (by decide) haddrLower)
          (le_trans (by decide) haddrLower)).trans hframed
      · right
        change 1048456 + bytes.length ≤ addr.toNat
        omega
      · right; exact le_trans (by decide) haddrLower
      · right; exact le_trans (by decide) haddrLower
    have hbase : base.wasm.mem.read32 addr = value := by
      exact hafter
    have halloc : allocStore.wasm.mem.read32 addr = value :=
      (hsuccess.fresh_preserves_read32
        (le_trans haddrUpper (by decide))).trans hbase
    have hpost : postGrow.wasm.mem.read32 addr = value := by
      simp only [postGrow, growResultOkStore]
      rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
        Mem.read32_write32_disjoint]
      · exact halloc
      all_goals right
      all_goals exact le_trans (by decide) haddrLower
    have hreserved : reserved.wasm.mem.read32 addr = value := by
      simp only [reserved, reserveFinishStore, reserveVectorStore]
      rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint]
      · exact hpost
      all_goals right
      all_goals exact le_trans (by decide) haddrLower
    have hcopied : copied.wasm.mem.read32 addr = value := by
      exact (Mem.read32_copy_before reserved.wasm.mem data.toNat
        firstChunkBuffer.toNat count.toNat addr (by
          rw [hdataNat]
          exact le_trans haddrUpper (by decide))).trans hreserved
    exact (readChunkFinishedStore_read32_other copied readToEndResult
      readToEndVector count 0 readToEndStack addr
      (by right; exact le_trans (by decide) haddrLower)
      (by right; exact le_trans (by decide) haddrLower)
      (by right; exact le_trans (by decide) haddrLower)).trans hcopied
  refine
    { split := ?_
      input_eq := ?_
      output_eq := ?_
      oom_eq := ?_
      runtime_module := ?_
      runtime_host := ?_
      memory_cap := ?_
      pages_lower := ?_
      pages_upper := ?_
      global_eq := ?_
      status_capacity := hfinalStatus decodeStatusVector 0 (by decide)
        (by decide) hentryStatusCapacity
      status_pointer := hfinalStatus (decodeStatusVector + 4) 1 (by decide)
        (by decide) hentryStatusPointer
      status_length := hfinalStatus (decodeStatusVector + 8) 0 (by decide)
        (by decide) hentryStatusLength
      capacity_eq := ?_
      data_eq := ?_
      length_eq := ?_
      bump_eq := ?_
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
      afterUniversalRead, framed, entryStore, decodeConfig,
      Universal.State.ofInput, StdIO.State.ofInput]
    rfl
  · rw [show finalStore.wasm.host = allocStore.wasm.host by rfl, hhost]
    change after.wasm.host.oom.raised = false
    simp [after, readAdapterResultStore, universalReadStore,
      afterUniversalRead, framed, entryStore, decodeConfig,
      Universal.State.ofInput, StdIO.State.ofInput]
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
    have hcap : base.wasm.memoryCap base.runtime.currentModule 0 = 65536 := by
      rfl
    have hp : base.wasm.mem.pages ≤ 65536 := by
      have hentryPages : entryStore.wasm.mem.pages = 17 := by rfl
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
  · have hbaseGlobal : globalAt? base 0 =
        some (.i32 (firstChunkFrame - 16)) := by
      have hentryGlobal : globalAt? entryStore 0 = some (.i32 decodeStack) := by
        simp only [entryStore, decodeFrameStore, globalAt?,
          canonicalGlobalIndex_zero]
        have hinitial : globalAt? (decodeConfig input).store 0 =
            some (.i32 1048576) := by rfl
        have hzero : 0 < (decodeConfig input).store.wasm.globals.globals.length :=
          (getElem?_eq_some_iff.mp hinitial).1
        exact List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero
      have hframedGlobal : globalAt? framed 0 =
          some (.i32 readToEndStack) := by
        simp only [framed, readToEndFrameStore, globalAt?,
          canonicalGlobalIndex_zero]
        have hzero : 0 < entryStore.wasm.globals.globals.length :=
          (getElem?_eq_some_iff.mp hentryGlobal).1
        exact List.getElem?_set_eq_of_lt (.i32 readToEndStack) hzero
      apply reserveFrameStore_global_zero after _ firstChunkFrame
      rw [readAdapterResultStore_globalAt]
      apply readChunkFrameStore_global_zero framed _ readToEndStack
      exact hframedGlobal
    have hallocGlobal := (hsuccess.globalAt_eq 0).trans hbaseGlobal
    have hreservedGlobal : globalAt? reserved 0 =
        some (.i32 firstChunkFrame) := by
      apply reserveFinishStore_global_zero postGrow readToEndVector data
        capacity firstChunkFrame (firstChunkFrame - 16)
      simpa [postGrow] using hallocGlobal
    simp only [finalStore, readChunkFinishedStore, globalAt?,
      canonicalGlobalIndex_zero]
    have hzero : 0 < copied.wasm.globals.globals.length := by
      have hc : globalAt? copied 0 = some (.i32 firstChunkFrame) := by
        change globalAt? reserved 0 = some (.i32 firstChunkFrame)
        exact hreservedGlobal
      exact (getElem?_eq_some_iff.mp hc).1
    simpa using
      (List.getElem?_set_eq_of_lt (.i32 readToEndStack) hzero)
  · have hreserved : reserved.wasm.mem.read32 readToEndVector = capacity := by
      simp only [reserved, reserveFinishStore, reserveVectorStore]
      rw [Mem.read32_write32_disjoint]
      · exact Mem.read32_write32_same _ _ _
      · decide
    have hcopied : copied.wasm.mem.read32 readToEndVector = capacity := by
      exact (Mem.read32_copy_before reserved.wasm.mem data.toNat
        firstChunkBuffer.toNat count.toNat readToEndVector (by
          rw [hdataNat]
          decide)).trans hreserved
    exact (readChunkFinishedStore_read32_other copied readToEndResult
      readToEndVector count 0 readToEndStack readToEndVector
      (by decide) (by decide) (by decide)).trans hcopied
  · have hreserved : reserved.wasm.mem.read32 (readToEndVector + 4) = data :=
      reserveFinishStore_read_data postGrow readToEndVector data capacity
        firstChunkFrame
    have hcopied : copied.wasm.mem.read32 (readToEndVector + 4) = data := by
      exact (Mem.read32_copy_before reserved.wasm.mem data.toNat
        firstChunkBuffer.toNat count.toNat (readToEndVector + 4) (by
          rw [hdataNat]
          decide)).trans hreserved
    exact (readChunkFinishedStore_read32_other copied readToEndResult
      readToEndVector count 0 readToEndStack (readToEndVector + 4)
      (by decide) (by decide) (by decide)).trans hcopied
  · simp [finalStore, readChunkFinishedStore]
  · have hallocBump : allocStore.wasm.mem.read32 1053960 = bump := by
      simpa [bump] using hsuccess.read_bump (by decide)
    have hpostBump : postGrow.wasm.mem.read32 1053960 = bump := by
      simp only [postGrow, growResultOkStore]
      rw [Mem.read32_write32_disjoint,
        Mem.read32_write32_disjoint, Mem.read32_write32_disjoint]
      · exact hallocBump
      all_goals decide
    have hreservedBump : reserved.wasm.mem.read32 1053960 = bump := by
      simp only [reserved, reserveFinishStore, reserveVectorStore]
      rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint]
      · exact hpostBump
      all_goals decide
    have hcopiedBump : copied.wasm.mem.read32 1053960 = bump := by
      exact (Mem.read32_copy_before reserved.wasm.mem data.toNat
        firstChunkBuffer.toNat count.toNat 1053960 (by
          rw [hdataNat]
          decide)).trans hreservedBump
    exact (readChunkFinishedStore_read32_other copied readToEndResult
      readToEndVector count 0 readToEndStack 1053960
      (by decide) (by decide) (by decide)).trans hcopiedBump
  · have hafterBytes : after.wasm.mem.readBytes firstChunkBuffer.toNat
        bytes.length = bytes := by
      simp only [after, readAdapterResultStore, universalReadStore]
      rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint]
      · exact Mem.readBytes_writeBytes_self _ _ bytes
      · left
        change 1048456 + bytes.length ≤ 1048488
        omega
      · left
        change 1048456 + bytes.length ≤ 1048492
        omega
    have hallocBytes : allocStore.wasm.mem.readBytes firstChunkBuffer.toNat
        bytes.length = bytes := by
      have hp := hsuccess.fresh_preserves_readBytes firstChunkBuffer.toNat
        bytes.length (by
          change 1048456 + bytes.length ≤ 1053960
          omega)
      rw [hp]
      change after.wasm.mem.readBytes firstChunkBuffer.toNat bytes.length = bytes
      exact hafterBytes
    have hpostBytes : postGrow.wasm.mem.readBytes firstChunkBuffer.toNat
        bytes.length = bytes := by
      simp only [postGrow, growResultOkStore]
      rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
        Mem.readBytes_write32_disjoint]
      · exact hallocBytes
      all_goals right
      all_goals change _ ≤ 1048456
      all_goals decide
    have hreservedBytes : reserved.wasm.mem.readBytes firstChunkBuffer.toNat
        bytes.length = bytes := by
      simp only [reserved, reserveFinishStore, reserveVectorStore]
      rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint]
      · exact hpostBytes
      · left
        rw [show firstChunkBuffer.toNat = 1048456 by decide,
          show readToEndVector.toNat = 1048500 by decide]
        omega
      · left
        rw [show firstChunkBuffer.toNat = 1048456 by decide,
          show (readToEndVector + 4).toNat = 1048504 by decide]
        omega
    have hcopiedBytes : copied.wasm.mem.readBytes data.toNat bytes.length =
        bytes := by
      simp only [copied, readChunkCopiedStore]
      rw [hcountNat, Mem.readBytes_copy_destination]
      exact hreservedBytes
    simp only [finalStore, readChunkFinishedStore]
    rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write8_disjoint,
      Mem.readBytes_write32_disjoint]
    · exact hcopiedBytes
    all_goals right; rw [hdataNat]; decide
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

set_option maxRecDepth 1048576 in
theorem first_empty_read_success
    (input bytes : List UInt8)
    (hbytes : bytes = input.take 32) (hempty : bytes = []) :
    let entryStore := decodeFrameStore (decodeConfig input).store
    let framed := readToEndFrameStore entryStore readToEndStack
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let firstStore := readChunkFinishedStore after readToEndResult
      readToEndVector 0 0 readToEndStack
    let vectorWord := firstStore.wasm.mem.read64 (readToEndStack + 4)
    let finalStore := readToEndFinishedStore firstStore decodeInputVector
      readToEndStack decodeStack vectorWord 0
    ReadToEndSuccess input (decodeAfterReadConfig finalStore) := by
  dsimp only
  have hinput : input = [] := by
    rcases List.take_eq_nil_iff.mp (hbytes.symm.trans hempty) with hzero | hnil
    · omega
    · exact hnil
  subst input
  subst bytes
  let entryStore := decodeFrameStore (decodeConfig []).store
  let framed := readToEndFrameStore entryStore readToEndStack
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer []
  let firstStore := readChunkFinishedStore after readToEndResult
    readToEndVector 0 0 readToEndStack
  let vectorWord := firstStore.wasm.mem.read64 (readToEndStack + 4)
  let finalStore := readToEndFinishedStore firstStore decodeInputVector
    readToEndStack decodeStack vectorWord 0
  change ReadToEndSuccess [] (decodeAfterReadConfig finalStore)
  have hframedCapacity : framed.wasm.mem.read32 readToEndVector = 0 := by
    simp [framed, readToEndFrameStore, entryStore, decodeFrameStore,
      Mem.read32, Mem.write64, Mem.write32] <;> bv_decide
  have hframedData : framed.wasm.mem.read32 (readToEndVector + 4) = 1 := by
    simp [framed, readToEndFrameStore, entryStore, decodeFrameStore,
      Mem.read32, Mem.write64, Mem.write32] <;> bv_decide
  have hframedBump : framed.wasm.mem.read32 1053960 = 0 := by
    simp only [framed, entryStore, readToEndFrameStore, decodeFrameStore,
      decodeConfig]
    rw [Mem.read32_write64_disjoint _ 1053960 (readToEndStack + 4) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (readToEndStack + 12) 1053960 _
      (by decide)]
    rw [Mem.read32_write64_disjoint _ 1053960 (decodeStack + 12) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (decodeStack + 20) 1053960 _
      (by decide)]
    exact initial_allocator_bump
  have hafterCapacity : after.wasm.mem.read32 readToEndVector = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame framed firstChunkFrame
        readToEndVector (by decide) (by decide) (by decide) (by decide)).trans
        hframedCapacity
    all_goals simp <;> omega
  have hafterData : after.wasm.mem.read32 (readToEndVector + 4) = 1 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame framed firstChunkFrame
        (readToEndVector + 4) (by decide) (by decide) (by decide)
        (by decide)).trans hframedData
    all_goals simp <;> omega
  have hafterBump : after.wasm.mem.read32 1053960 = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame framed firstChunkFrame
        1053960 (by decide) (by decide) (by decide) (by decide)).trans
        hframedBump
    all_goals simp <;> omega
  have hfirstCapacity : firstStore.wasm.mem.read32 readToEndVector = 0 :=
    (readChunkFinishedStore_read32_other after readToEndResult
      readToEndVector 0 0 readToEndStack readToEndVector
      (by decide) (by decide) (by decide)).trans hafterCapacity
  have hfirstData : firstStore.wasm.mem.read32 (readToEndVector + 4) = 1 :=
    (readChunkFinishedStore_read32_other after readToEndResult
      readToEndVector 0 0 readToEndStack (readToEndVector + 4)
      (by decide) (by decide) (by decide)).trans hafterData
  have hfirstBump : firstStore.wasm.mem.read32 1053960 = 0 :=
    (readChunkFinishedStore_read32_other after readToEndResult
      readToEndVector 0 0 readToEndStack 1053960
      (by decide) (by decide) (by decide)).trans hafterBump
  refine ⟨finalStore, 0, 1, 0, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl rfl, Or.inl rfl,
    Or.inl rfl, ?_, ?_⟩
  · rfl
  · rfl
  · change (default : OOM.State).raised = false
    decide
  · rfl
  · rfl
  · rfl
  · decide
  · change («module».initialStore : Store Universal.State).mem.pages ≤ 65536
    decide
  · simp only [finalStore, readToEndFinishedStore, globalAt?,
      canonicalGlobalIndex_zero]
    have hinitial : globalAt? (decodeConfig []).store 0 =
        some (.i32 1048576) := by rfl
    have hzero : 0 < firstStore.wasm.globals.globals.length := by
      change 0 < (decodeConfig []).store.wasm.globals.globals.length
      exact (getElem?_eq_some_iff.mp hinitial).1
    exact List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · simp [firstStore, readChunkFinishedStore, after,
        readAdapterResultStore, universalReadStore, readChunkFrameStore,
        framed, readToEndFrameStore, entryStore, decodeFrameStore,
        decodeConfig, Mem.read32, Mem.write64, Mem.write32, Mem.write8,
        Mem.writeBytes] <;> bv_decide
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · simp [firstStore, readChunkFinishedStore, after,
        readAdapterResultStore, universalReadStore, readChunkFrameStore,
        framed, readToEndFrameStore, entryStore, decodeFrameStore,
        decodeConfig, Mem.read32, Mem.write64, Mem.write32, Mem.write8,
        Mem.writeBytes] <;> bv_decide
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · simp [firstStore, readChunkFinishedStore, after,
        readAdapterResultStore, universalReadStore, readChunkFrameStore,
        framed, readToEndFrameStore, entryStore, decodeFrameStore,
        decodeConfig, Mem.read32, Mem.write64, Mem.write32, Mem.write8,
        Mem.writeBytes] <;> bv_decide
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_low, Mem.read64_low]
    exact hfirstCapacity
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_high _ _ _ (by decide),
      Mem.read64_high _ _ (by decide)]
    simpa only [show readToEndStack + 4 + 4 = readToEndVector + 4 by
      bv_decide] using hfirstData
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint]
    · exact Mem.read32_write32_same _ _ _
    · decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hfirstBump
    all_goals decide
  · simp [Mem.readBytes]
  · simp
  · norm_num
  · change 1 ≤ firstStore.wasm.mem.pages * 65536
    have hp : firstStore.wasm.mem.pages = 17 := by rfl
    rw [hp]
    decide

set_option maxRecDepth 1048576 in
theorem first_empty_read_outcome
    (input bytes : List UInt8)
    (hbytes : bytes = input.take 32) (hempty : bytes = []) :
    let entryStore := decodeFrameStore (decodeConfig input).store
    let framed := readToEndFrameStore entryStore readToEndStack
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let firstStore := readChunkFinishedStore after readToEndResult
      readToEndVector 0 0 readToEndStack
    ReachesOrOOM
      ({ expr := .running
          ⟨⟨[.i32 decodeInputVector],
              [.i32 readToEndStack, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
            readToEndAfterFirstRead, 0, [], [],
            [(readChunkCallerFrame [] decodeLocals [] decodeAfterRead 0 [] []
              entryStore.runtime.entry)]⟩,
         store := firstStore } : Config Universal.State)
      (ReadToEndSuccess input) := by
  dsimp only
  let entryStore := decodeFrameStore (decodeConfig input).store
  let framed := readToEndFrameStore entryStore readToEndStack
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let firstStore := readChunkFinishedStore after readToEndResult
    readToEndVector 0 0 readToEndStack
  let vectorWord := firstStore.wasm.mem.read64 (readToEndStack + 4)
  let finalStore := readToEndFinishedStore firstStore decodeInputVector
    readToEndStack decodeStack vectorWord 0
  have htag : firstStore.wasm.mem.read8 (readToEndStack + 16) = 4 := by
    simp [firstStore, readChunkFinishedStore, Mem.read8, Mem.write32,
      Mem.write8] <;> bv_decide
  have hcount : firstStore.wasm.mem.read32 (readToEndStack + 20) = 0 := by
    simp [firstStore, readChunkFinishedStore, Mem.read32, Mem.write32,
      Mem.write8] <;> bv_decide
  have hlength : firstStore.wasm.mem.read32 (readToEndStack + 12) = 0 := by
    simp [firstStore, readChunkFinishedStore]
  have hglobal : (globalAt? firstStore 0).isSome = true := by
    simp only [firstStore, readChunkFinishedStore, globalAt?,
      canonicalGlobalIndex_zero]
    have hinitial : globalAt? (decodeConfig input).store 0 =
        some (.i32 1048576) := by rfl
    have hzero : 0 < after.wasm.globals.globals.length := by
      change 0 < (decodeConfig input).store.wasm.globals.globals.length
      exact (getElem?_eq_some_iff.mp hinitial).1
    simp [List.getElem?_set_eq_of_lt (.i32 readToEndStack) hzero]
  have hreach := read_to_end_after_first_eof firstStore [] decodeLocals []
    decodeAfterRead 0 [] [] [] decodeInputVector readToEndStack decodeStack
    vectorWord 0 htag hcount hlength rfl
    (by change 1048513 ≤ firstStore.wasm.mem.pages * 65536
        have hp : firstStore.wasm.mem.pages = 17 := by rfl
        omega)
    (by change 1048520 ≤ firstStore.wasm.mem.pages * 65536
        have hp : firstStore.wasm.mem.pages = 17 := by rfl
        omega)
    (by change 1048512 ≤ firstStore.wasm.mem.pages * 65536
        have hp : firstStore.wasm.mem.pages = 17 := by rfl
        omega)
    (by change 1048508 ≤ firstStore.wasm.mem.pages * 65536
        have hp : firstStore.wasm.mem.pages = 17 := by rfl
        omega)
    (by change 1048576 ≤ firstStore.wasm.mem.pages * 65536
        have hp : firstStore.wasm.mem.pages = 17 := by rfl
        omega)
    (by change 1048572 ≤ firstStore.wasm.mem.pages * 65536
        have hp : firstStore.wasm.mem.pages = 17 := by rfl
        omega)
    (by decide) hglobal (by decide)
  apply ReachesOrOOM.of_reaches (by
    rw [show entryStore.runtime.entry = firstStore.runtime.entry by rfl]
    simpa [finalStore, decodeAfterReadConfig, readChunkCallerFrame] using hreach)
  exact first_empty_read_success input bytes hbytes hempty

set_option maxRecDepth 1048576 in
theorem first_nonempty_read_outcome
    (input bytes : List UInt8)
    (allocStore : MachineStore Universal.State)
    (hbytes : bytes = input.take 32) (hnil : bytes ≠ [])
    (hsuccess :
      let entryStore := decodeFrameStore (decodeConfig input).store
      let framed := readToEndFrameStore entryStore readToEndStack
      let after := readAdapterResultStore
        (readChunkFrameStore framed firstChunkFrame)
        firstChunkResult firstChunkBuffer bytes
      let count := UInt32.ofNat bytes.length
      ByteGrowSuccess (reserveFrameStore after (firstChunkFrame - 16))
        0 1 (reserveNewCapacity 0 count 0) 0 allocStore) :
    let entryStore := decodeFrameStore (decodeConfig input).store
    let framed := readToEndFrameStore entryStore readToEndStack
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    let capacity := reserveNewCapacity 0 count 0
    let data := allocatorPtr 0 1
    let firstStore := readChunkFinishedStore
      (readChunkCopiedStore
        (reserveFinishStore
          (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
            data capacity)
          readToEndVector data capacity firstChunkFrame)
        data firstChunkBuffer count)
      readToEndResult readToEndVector count 0 readToEndStack
    ReachesOrOOM
      ({ expr := .running
          ⟨⟨[.i32 decodeInputVector],
              [.i32 readToEndStack, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
            readToEndAfterFirstRead, 0, [], [],
            [(readChunkCallerFrame [] decodeLocals [] decodeAfterRead 0 [] []
              entryStore.runtime.entry)]⟩,
         store := firstStore } : Config Universal.State)
      (ReadToEndSuccess input) := by
  dsimp only
  let entryStore := decodeFrameStore (decodeConfig input).store
  let framed := readToEndFrameStore entryStore readToEndStack
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let count := UInt32.ofNat bytes.length
  let capacity := reserveNewCapacity 0 count 0
  let data := allocatorPtr 0 1
  let bump := allocatorFinish capacity 1 0
  let reserved := reserveFinishStore
    (growResultOkStore allocStore ((firstChunkFrame - 16) + 4) data capacity)
    readToEndVector data capacity firstChunkFrame
  let firstStore := readChunkFinishedStore
    (readChunkCopiedStore reserved data firstChunkBuffer count)
    readToEndResult readToEndVector count 0 readToEndStack
  have hinv := first_nonempty_read_invariant input bytes allocStore hbytes hnil
    hsuccess
  change ReadToEndInv input bytes (input.drop bytes.length) firstStore capacity
    data count bump at hinv
  have hcountNe : count ≠ 0 := by
    intro hz
    have hn := congrArg UInt32.toNat hz
    have hcountNat : count.toNat = bytes.length := by
      apply UInt32.toNat_ofNat_of_lt'
      change bytes.length < 4294967296
      have hlen : bytes.length ≤ 32 := by
        rw [hbytes, List.length_take]
        omega
      omega
    rw [hcountNat] at hn
    exact hnil (List.eq_nil_of_length_eq_zero (by simpa using hn))
  have htag : firstStore.wasm.mem.read8 (readToEndStack + 16) = 4 := by
    simp only [firstStore, readChunkFinishedStore]
    simp only [Mem.read8]
    rw [Mem.write32_bytes_of_disjoint]
    · simp [Mem.write8]
    · right
      change 1048508 + 4 ≤ 1048512
      omega
  have hcount : firstStore.wasm.mem.read32 (readToEndStack + 20) = count := by
    simp only [firstStore, readChunkFinishedStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by
          change 1048508 + 4 ≤ 1048516
          omega)),
      Mem.read32_write8_disjoint _ _ _ _ (Or.inr (by
          change 1048512 + 1 ≤ 1048516
          omega))]
    change
      ((readChunkCopiedStore reserved data firstChunkBuffer count).wasm.mem.write32
        (readToEndResult + 4) count).read32 (readToEndResult + 4) = count
    exact Mem.read32_write32_same _ _ _
  have hprefix := read_to_end_after_first_nonempty_to_loop firstStore []
    decodeLocals [] decodeAfterRead 0 [] [] [] decodeInputVector readToEndStack
    capacity data count htag hcount hcountNe hinv.capacity_eq hinv.data_eq
    hinv.length_eq
    (by have hp := hinv.pages_lower
        change 1048513 ≤ firstStore.wasm.mem.pages * 65536
        omega)
    (by have hp := hinv.pages_lower
        change 1048520 ≤ firstStore.wasm.mem.pages * 65536
        omega)
    (by have hp := hinv.pages_lower
        rw [show readToEndStack.toNat = 1048496 by decide]
        omega)
    (by have hp := hinv.pages_lower
        rw [show readToEndStack.toNat = 1048496 by decide]
        omega)
    (by have hp := hinv.pages_lower
        change 1048512 ≤ firstStore.wasm.mem.pages * 65536
        omega)
  have hentryRuntime : firstStore.runtime = entryStore.runtime := by
    change allocStore.runtime = entryStore.runtime
    rw [hsuccess.runtime_eq]
    rfl
  apply ReachesOrOOM.prependReaches (by
    rw [show entryStore.runtime.entry = firstStore.runtime.entry from
      (congrArg (fun r => r.entry) hentryRuntime).symm]
    simpa [readChunkCallerFrame, decodeReadLoopConfig, firstStore, reserved,
      capacity, data, count] using hprefix)
  exact read_to_end_loop_outcome input bytes (input.drop bytes.length)
    firstStore capacity data count bump 8192 hinv hcountNe (by decide)

set_option maxRecDepth 1048576 in
theorem decode_read_to_end_outcome (input : List UInt8) :
    ReachesOrOOM (decodeConfig input) (ReadToEndSuccess input) := by
  let entryStore := decodeFrameStore (decodeConfig input).store
  let framed := readToEndFrameStore entryStore readToEndStack
  let bytes := input.take 32
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let count := UInt32.ofNat bytes.length
  have hprefix := decode_to_read_to_end input
  have hfirst := decode_to_first_chunk_outcome input
  apply ReachesOrOOM.prependReaches hprefix
  apply hfirst.bind
  intro final hfinal
  by_cases hempty : bytes = []
  · have hempty' : input.take 32 = [] := by simpa [bytes] using hempty
    simp only [if_pos hempty'] at hfinal
    subst final
    simpa [entryStore, framed, bytes, after, count, readChunkCallerFrame] using
      first_empty_read_outcome input bytes rfl hempty
  · have hempty' : input.take 32 ≠ [] := by simpa [bytes] using hempty
    simp only [if_neg hempty'] at hfinal
    rcases hfinal with ⟨allocStore, hsuccess, rfl⟩
    simpa [entryStore, framed, bytes, after, count, readChunkCallerFrame] using
      first_nonempty_read_outcome input bytes allocStore rfl hempty hsuccess

end Project.HexDecodeStdio
