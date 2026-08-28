import HexEncodeStdio.StoreFacts

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

@[simp] abbrev readToEndStack : UInt32 := 1048512
@[simp] abbrev readToEndVector : UInt32 := 1048516
@[simp] abbrev readToEndResult : UInt32 := 1048528
@[simp] abbrev readToEndIgnored : UInt32 := 1048543
@[simp] abbrev firstChunkFrame : UInt32 := 1048464
@[simp] abbrev firstChunkBuffer : UInt32 := 1048472
@[simp] abbrev firstChunkResult : UInt32 := 1048504

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem read_chunk_first_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 readToEndStack))
    (hbytes : bytes = store.wasm.host.stdio.input.take 32)
    (hpages : store.wasm.mem.pages = 17)
    (hcapacity : store.wasm.mem.read32 readToEndVector = 0)
    (hdata : store.wasm.mem.read32 (readToEndVector + 4) = 1)
    (hlength : store.wasm.mem.read32 (readToEndVector + 8) = 0)
    (hbump : store.wasm.mem.read32 1053960 = 0) :
    let after := readAdapterResultStore
      (readChunkFrameStore store firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    ReachesOrOOM
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 readToEndVector, .i32 readToEndIgnored,
                .i32 readToEndResult] ++ stack⟩,
            [.call 4] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      (fun final =>
        if bytes = [] then
          final =
            { expr := .running
                ⟨⟨outerParams, outerLocalValues, stack⟩,
                  code, arity, remainder, controls, calls⟩
              store := readChunkFinishedStore after readToEndResult
                readToEndVector 0 0 readToEndStack }
        else
          ∃ allocStore,
            ByteGrowSuccess
                (reserveFrameStore after (firstChunkFrame - 16))
                0 1 (reserveNewCapacity 0 count 0) 0 allocStore ∧
            let reserved := reserveFinishStore
              (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
                (allocatorPtr 0 1) (reserveNewCapacity 0 count 0))
              readToEndVector (allocatorPtr 0 1)
                (reserveNewCapacity 0 count 0) firstChunkFrame
            final =
              { expr := .running
                  ⟨⟨outerParams, outerLocalValues, stack⟩,
                    code, arity, remainder, controls, calls⟩
                store := readChunkFinishedStore
                  (readChunkCopiedStore reserved
                    (allocatorPtr 0 1) firstChunkBuffer count)
                  readToEndResult readToEndVector count 0 readToEndStack }) := by
  dsimp only
  simp only [readToEndStack, readToEndVector, readToEndResult,
    readToEndIgnored, firstChunkFrame, firstChunkBuffer,
    firstChunkResult] at *
  let after := readAdapterResultStore
    (readChunkFrameStore store firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let count := UInt32.ofNat bytes.length
  have hprefix := read_chunk_to_after_read store outerParams outerLocalValues
    stack code arity remainder controls calls readToEndResult
    readToEndIgnored readToEndVector readToEndStack bytes hmod henv hglobal
    hbytes (by decide) (by decide) (by rw [hpages]; decide)
  have htoAfter : Reaches
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 readToEndVector, .i32 readToEndIgnored,
                .i32 readToEndResult] ++ stack⟩,
            [.call 4] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      (readChunkAfterReadConfig after outerParams outerLocalValues stack code
        arity remainder controls calls readToEndResult readToEndIgnored
        readToEndVector firstChunkFrame) := by
    simpa [after, readChunkAfterReadConfig, readChunkCalls,
      readChunkCallerFrame] using hprefix
  apply ReachesOrOOM.prependReaches htoAfter
  have hlen : bytes.length ≤ 32 := by
    rw [hbytes, List.length_take]
    omega
  have hcountNat : count.toNat = bytes.length := by
    have hsmall : bytes.length < UInt32.size := by
      change bytes.length < 4294967296
      omega
    simp [count, Nat.mod_eq_of_lt hsmall]
  have hcountLt : count < 33 := by
    rw [UInt32.lt_iff_toNat_lt, hcountNat]
    have h33 : (33 : UInt32).toNat = 33 := by decide
    rw [h33]
    omega
  have htag : after.wasm.mem.read8 (firstChunkFrame + 40) = 4 := by
    apply readAdapterResultStore_read_tag
    decide
  have hcount : after.wasm.mem.read32 (firstChunkFrame + 44) = count := by
    simpa [after, count] using
      readAdapterResultStore_read_count
        (readChunkFrameStore store firstChunkFrame)
        firstChunkResult firstChunkBuffer bytes
  have hafterCapacity : after.wasm.mem.read32 readToEndVector = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        readToEndVector (by decide) (by decide) (by decide) (by decide)).trans
        hcapacity
    all_goals (simp_all <;> omega)
  have hafterData : after.wasm.mem.read32 (readToEndVector + 4) = 1 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        (readToEndVector + 4) (by decide) (by decide) (by decide)
        (by decide)).trans hdata
    all_goals (simp_all <;> omega)
  have hafterLength : after.wasm.mem.read32 (readToEndVector + 8) = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        (readToEndVector + 8) (by decide) (by decide) (by decide)
        (by decide)).trans hlength
    all_goals (simp_all <;> omega)
  have hafterBump : after.wasm.mem.read32 1053960 = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        1053960 (by decide) (by decide) (by decide) (by decide)).trans hbump
    all_goals (simp_all <;> omega)
  have hafterGlobal : globalAt? after 0 = some (.i32 firstChunkFrame) := by
    rw [readAdapterResultStore_globalAt]
    exact readChunkFrameStore_global_zero store firstChunkFrame readToEndStack
      hglobal
  have hafterPages : after.wasm.mem.pages = 17 := by
    simpa [after] using hpages
  have hafterMod : after.runtime.currentModule = «module» := by
    simpa [after] using hmod
  have hafterEnv : after.runtime.currentHost = Universal.envFor «module» := by
    simpa [after] using henv
  by_cases hempty : bytes = []
  · simp only [if_pos hempty]
    have hcountZero : count = 0 := by simp [count, hempty]
    have hsuffix := read_chunk_after_read_eof after outerParams
      outerLocalValues stack code arity remainder controls calls
      readToEndResult readToEndIgnored readToEndVector firstChunkFrame
      0 0 htag (by simpa [hcountZero] using hcount) hafterCapacity
      hafterLength (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by simp [hafterGlobal])
    exact ReachesOrOOM.of_reaches hsuffix (by rfl)
  · simp only [if_neg hempty]
    have hcountNe : count ≠ 0 := by
      intro hz
      have : count.toNat = 0 := congrArg UInt32.toNat hz
      rw [hcountNat] at this
      have hpos : 0 < bytes.length := List.length_pos_iff.mpr hempty
      omega
    have hnotFits : ¬ count ≤ (0 : UInt32) - 0 := by
      simp [hcountNe]
    have hcountPos : 0 < count := UInt32.pos_iff_ne_zero.mpr hcountNe
    have hnewLe : (reserveNewCapacity 0 count 0).toNat ≤ 32 := by
      by_cases hc : count > 8
      · simp [reserveNewCapacity, reserveCandidate, reserveRequired,
          reserveDoubled, hc, hcountPos, hcountNat]
        exact hlen
      · simp [reserveNewCapacity, reserveCandidate, reserveRequired,
          reserveDoubled, hc, hcountPos]
    have hsuccessFacts : ∀ allocStore,
        ByteGrowSuccess
            (reserveFrameStore after (firstChunkFrame - 16)) 0 1
            (reserveNewCapacity 0 count 0) 0 allocStore →
        let reserved := reserveFinishStore
          (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
            (allocatorPtr 0 1) (reserveNewCapacity 0 count 0))
          readToEndVector (allocatorPtr 0 1)
            (reserveNewCapacity 0 count 0) firstChunkFrame
        reserved.wasm.mem.read32 (readToEndVector + 4) = allocatorPtr 0 1 ∧
        reserved.wasm.mem.read32 (readToEndVector + 8) = 0 ∧
        (firstChunkFrame + 8).toNat + count.toNat ≤
          reserved.wasm.mem.pages * 65536 ∧
        (allocatorPtr 0 1 + 0).toNat + count.toNat ≤
          reserved.wasm.mem.pages * 65536 ∧
        readToEndResult.toNat + 4 + 4 ≤
          reserved.wasm.mem.pages * 65536 ∧
        readToEndVector.toNat + 4 + 4 ≤
          reserved.wasm.mem.pages * 65536 ∧
        readToEndVector.toNat + 8 + 4 ≤
          reserved.wasm.mem.pages * 65536 ∧
        (globalAt? reserved 0).isSome = true := by
      intro allocStore hsuccess
      let postGrow := growResultOkStore allocStore
        ((firstChunkFrame - 16) + 4) (allocatorPtr 0 1)
        (reserveNewCapacity 0 count 0)
      let reserved := reserveFinishStore postGrow readToEndVector
        (allocatorPtr 0 1) (reserveNewCapacity 0 count 0) firstChunkFrame
      have hmono := hsuccess.pages_mono
      have hbasePages :
          (reserveFrameStore after (firstChunkFrame - 16)).wasm.mem.pages =
            17 := by simpa using hafterPages
      have hpages17 : 17 ≤ allocStore.wasm.mem.pages := by
        rw [← hbasePages]
        exact hmono
      have hreservedPages : reserved.wasm.mem.pages = allocStore.wasm.mem.pages := by
        simp [reserved, postGrow]
      have hglobalBase : globalAt?
          (reserveFrameStore after (firstChunkFrame - 16)) 0 =
          some (.i32 (firstChunkFrame - 16)) :=
        reserveFrameStore_global_zero after _ firstChunkFrame hafterGlobal
      have hglobalAlloc : (globalAt? allocStore 0).isSome = true := by
        have heq : globalAt? allocStore 0 =
            some (.i32 (firstChunkFrame - 16)) :=
          (hsuccess.globalAt_eq 0).trans hglobalBase
        simp [heq]
      have hglobalPost : globalAt? postGrow 0 = globalAt? allocStore 0 := by
        simp [postGrow]
      refine ⟨reserveFinishStore_read_data postGrow readToEndVector
          (allocatorPtr 0 1) (reserveNewCapacity 0 count 0) firstChunkFrame,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply reserveFinishStore_read_length_of_fresh
          (store := reserveFrameStore after (firstChunkFrame - 16))
          (allocStore := allocStore) (frame := firstChunkFrame - 16)
          (vector := readToEndVector) (oldPtr := 1)
          (newCapacity := reserveNewCapacity 0 count 0)
          (oldBump := 0) (length := 0) hsuccess
        · simpa [reserveFrameStore] using hafterLength
        all_goals decide
      · rw [hreservedPages]
        have hc : count.toNat ≤ 32 := hcountNat ▸ hlen
        change 1048472 + count.toNat ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        have hc : count.toNat ≤ 32 := hcountNat ▸ hlen
        change 1054000 + count.toNat ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        change 1048536 ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        change 1048524 ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        change 1048528 ≤ allocStore.wasm.mem.pages * 65536
        omega
      · apply Option.isSome_iff_exists.mpr
        exact ⟨.i32 firstChunkFrame,
          reserveFinishStore_global_zero postGrow readToEndVector
            (allocatorPtr 0 1) (reserveNewCapacity 0 count 0)
            firstChunkFrame (firstChunkFrame - 16)
            (by simpa [postGrow, hglobalPost] using
              (show globalAt? allocStore 0 =
                  some (.i32 (firstChunkFrame - 16)) from
                (hsuccess.globalAt_eq 0).trans hglobalBase))⟩
    exact read_chunk_after_read_reserve after outerParams outerLocalValues
      stack code arity remainder controls calls readToEndResult
      readToEndIgnored readToEndVector firstChunkFrame 0 1 0 count 0
      htag hcount hcountLt hcountNe hnotFits hafterCapacity hafterData
      hafterLength hafterBump hafterMod hafterEnv hafterGlobal
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by simp [reserveRequired])
      (by
        rw [Int32.lt_iff_toInt_lt]
        change ¬(if 2 * (reserveNewCapacity 0 count 0).toNat < 2^32
          then ((reserveNewCapacity 0 count 0).toNat : Int)
          else (reserveNewCapacity 0 count 0).toNat - 2^32) < 0
        rw [if_pos]
        · omega
        · omega)
      (by decide) (by rw [hafterPages]; decide) (by decide) (by decide)
      (by decide) (by
        have hz : reallocatorCopyLen 0 (reserveNewCapacity 0 count 0) = 0 := by
          simp [reallocatorCopyLen]
        rw [hz, hafterPages]
        decide)
      (by
        intro _
        have hz : reallocatorCopyLen 0 (reserveNewCapacity 0 count 0) = 0 := by
          simp [reallocatorCopyLen]
        rw [hz, hafterPages]
        decide)
      (by
        intro memory previousPages hgrow
        have hfacts := mem_grow_some_facts after.wasm.mem memory
          (allocatorRequiredPages (reserveNewCapacity 0 count 0) 1 0 -
            UInt32.ofNat after.wasm.mem.pages)
          (after.wasm.memoryCap after.runtime.currentModule 0)
          previousPages hgrow
        have hfacts := mem_grow_some_facts after.wasm.mem memory
          (allocatorRequiredPages (reserveNewCapacity 0 count 0) 1 0 -
            UInt32.ofNat after.wasm.mem.pages)
          (after.wasm.memoryCap after.runtime.currentModule 0)
          previousPages hgrow
        have hmemPages : 17 ≤ memory.pages := by
          rw [hfacts.2, hafterPages]
          omega
        have hz : reallocatorCopyLen 0 (reserveNewCapacity 0 count 0) = 0 := by
          simp [reallocatorCopyLen]
        rw [hz]
        constructor
        · change 1 ≤ memory.pages * 65536
          omega
        · change 1054000 ≤ memory.pages * 65536
          omega)
      hsuccessFacts

end Project.HexEncodeStdio
