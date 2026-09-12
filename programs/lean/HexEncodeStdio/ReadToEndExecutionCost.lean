import HexEncodeStdio.ReadToEndResourceCost
import HexEncodeStdio.ReadToEndLoop
import HexEncodeStdio.ReserveResourceCost
import HexEncodeStdio.ReadChunkResourceCost
import HexEncodeStdio.InputInitializationCost

/-! # Work and physical resources of the adaptive read-to-end execution -/

namespace Project.HexEncodeStdio.ReadToEndResourceCost

open Wasm Wasm.SmallStep Project.HexStdio Project.HexStdio.Spec ReadChunkCost

/-- An actual normal-return reader trace with retained allocation and initialized
byte potentials. The page term charges physical growth along that same trace. -/
def Result (input : List UInt8) (initial : Config Universal.State)
    (capacity initialized unread slack : Nat) : Prop :=
  ∃ final trace amount,
    CostedSteps CostedStdIO.work initial trace final amount ∧
    (∀ kind ∈ trace, HostPrimaryMemoryKind kind) ∧
    ReadToEndSuccess input final ∧
    (final.store.wasm.mem.read32 1053960).toNat ≤ inputFrontierBound input.length ∧
    final.store.wasm.mem.pages ≤ max initial.store.wasm.mem.pages
      (AllocatorResourceCost.requiredPages (inputFrontierBound input.length)) ∧
    amount + capacity + initialized + 65536 * initial.store.wasm.mem.pages ≤
      513 * unread + slack + 2 * capacityBound input.length +
        65536 * final.store.wasm.mem.pages

/-- Composition retains the precise intermediate physical store. -/
theorem Result.prepend {input : List UInt8} {initial middle : Config Universal.State}
    {trace : List StepKind} {amount capacity initialized unread slack
      nextCapacity nextInitialized nextUnread nextSlack : Nat}
    (first : CostedSteps CostedStdIO.work initial trace middle amount)
    (labels : ∀ kind ∈ trace, HostPrimaryMemoryKind kind)
    (pages : middle.store.wasm.mem.pages ≤ max initial.store.wasm.mem.pages
      (AllocatorResourceCost.requiredPages (inputFrontierBound input.length)))
    (budget : amount + capacity + initialized + 65536 * initial.store.wasm.mem.pages +
        513 * nextUnread + nextSlack ≤
      513 * unread + slack + nextCapacity + nextInitialized +
        65536 * middle.store.wasm.mem.pages)
    (suffix : Result input middle nextCapacity nextInitialized nextUnread nextSlack) :
    Result input initial capacity initialized unread slack := by
  obtain ⟨final, tail, total, execution, tailLabels, success, frontier, pageBound, workBound⟩ := suffix
  refine ⟨final, trace ++ tail, amount + total, first.trans execution, ?_, success,
    frontier, ?_, ?_⟩
  · intro kind member
    rcases List.mem_append.mp member with first | second
    · exact labels kind first
    · exact tailLabels kind second
  · omega
  · omega

theorem Result.prepend_scalar {input : List UInt8} {initial middle : Config Universal.State}
    {count capacity initialized unread slack nextCapacity nextInitialized nextUnread nextSlack : Nat}
    (first : ScalarReadRun initial middle count)
    (pages : middle.store.wasm.mem.pages = initial.store.wasm.mem.pages)
    (budget : count + capacity + initialized + 513 * nextUnread + nextSlack ≤
      513 * unread + slack + nextCapacity + nextInitialized)
    (suffix : Result input middle nextCapacity nextInitialized nextUnread nextSlack) :
    Result input initial capacity initialized unread slack := by
  obtain ⟨trace, execution, _, labels⟩ := first.costed
  exact Result.prepend execution labels (by rw [pages]; exact Nat.le_max_left _ _)
    (by rw [pages]; omega) suffix

theorem read_then_scalar {initial middle final : Config Universal.State} {n m bytes : Nat}
    (first : ReadCostRun initial middle n bytes) (second : ScalarReadRun middle final m) :
    ReadCostRun initial final (n + m) bytes := by
  obtain ⟨front, firstRun, frontLength, frontLabels⟩ := first
  obtain ⟨tail, secondRun, tailLength, tailLabels⟩ := second.costed
  refine ⟨front ++ tail, ?_, by simp [frontLength, tailLength], ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using firstRun.trans secondRun
  · intro kind member
    rcases List.mem_append.mp member with first | second
    · exact frontLabels kind first
    · exact tailLabels kind second

/-- The transfer, zero-fill and next-iteration credits compose even when the
actual read is zero. A positive read pays the next loop's fixed credit. -/
theorem Result.prepend_read {input remaining bytes : List UInt8}
    {initial middle : Config Universal.State} {capacity length filled target scalar bulk : Nat}
    (first : ReadCostRun initial middle scalar bulk)
    (hbulk : bulk = target - filled + bytes.length)
    (hscalar : scalar ≤ 73) (hfilled : filled ≤ target) (hbytes : bytes.length ≤ remaining.length)
    (pages : middle.store.wasm.mem.pages = initial.store.wasm.mem.pages)
    (suffix : Result input middle capacity (length + target)
      (remaining.drop bytes.length).length (if bytes = [] then 22 else 547)) :
    Result input initial capacity (length + filled) remaining.length 256 := by
  subst bulk
  obtain ⟨trace, execution, _, labels⟩ := first
  apply Result.prepend execution labels (by rw [pages]; exact Nat.le_max_left _ _) _ suffix
  rw [pages, List.length_drop]
  by_cases hempty : bytes = []
  · simp only [hempty, List.length_nil, if_pos, Nat.sub_zero]
    omega
  · simp only [if_neg hempty]
    have hb := List.length_pos_iff.mpr hempty
    omega

/-- EOF's descriptor-copy and actual caller return preserve the checked input
and both resource bounds. Initialized bytes may exceed consumed bytes. -/
theorem return_cost (input : List UInt8) (store : MachineStore Universal.State)
    (chunk capacity data length filled target count bump : UInt32) (initialized : Nat)
    (hinv : BoundedReadInv input input []
      (readToEndLengthStore store readToEndStack count length)
      capacity data (length + count) bump)
    (hinitialized : initialized ≤ capacity.toNat) :
    Result input
      (readToEndReturnConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length filled target count)
      capacity.toNat initialized 0 13 := by
  let updated := readToEndLengthStore store readToEndStack count length
  let vectorWord := updated.wasm.mem.read64 (readToEndStack + 4)
  let finalStore := readToEndFinishedStore updated 1048552
    readToEndStack 1048544 vectorWord (length + count)
  have hreach := read_to_end_return_steps_trace store [] encodeLocals []
    (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
    capacity data length filled target count 1048544 vectorWord
    (by simp [readToEndLengthStore]) rfl
    (by have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.toReadToEndInv.pages_lower
        change 1048528 ≤ store.wasm.mem.pages * 65536
        omega)
    (by have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.toReadToEndInv.pages_lower
        change 1048524 ≤ store.wasm.mem.pages * 65536
        omega)
    (by have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.toReadToEndInv.pages_lower
        change 1048564 ≤ store.wasm.mem.pages * 65536
        omega)
    (by have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.toReadToEndInv.pages_lower
        change 1048560 ≤ store.wasm.mem.pages * 65536
        omega)
    (by decide)
    (by simp [hinv.toReadToEndInv.global_eq])
    (by decide)
  obtain ⟨trace, execution, _, labels⟩ := hreach.costed
  refine ⟨encodeAfterReadConfig finalStore, trace, 13, ?_, labels, ?_, ?_, ?_, ?_⟩
  · simpa [updated, vectorWord, finalStore, encodeAfterReadConfig] using execution
  · simpa [finalStore, updated, vectorWord, encodeAfterReadConfig, encodeLocals]
      using hinv.toReadToEndInv.finished_success
  · change (((updated.wasm.mem.write32 (1048552 + 8) (length + count)).write64
        1048552 vectorWord).read32 1053960).toNat ≤ inputFrontierBound input.length
    rw [Mem.read32_write64_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)]
    rw [hinv.toReadToEndInv.bump_eq]
    have hb := hinv.bump_upper
    have hc := hinv.capacity_upper
    unfold inputFrontierBound
    omega
  · exact Nat.le_max_left _ _
  · change 13 + capacity.toNat + initialized + 65536 * store.wasm.mem.pages ≤
      513 * 0 + 13 + 2 * capacityBound input.length + 65536 * store.wasm.mem.pages
    have hc := hinv.capacity_upper
    omega

set_option maxHeartbeats 1200000 in
theorem after_read_cost
    (input consumed remaining : List UInt8)
    (store readStore : MachineStore Universal.State)
    (capacity data length bump chunk filled target count : UInt32)
    (bytes : List UInt8)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat)
    (hspare : length ≠ capacity)
    (htarget : readToEndTarget chunk capacity length = target)
    (hfilled : filled.toNat ≤ target.toNat)
    (hbytes : bytes = remaining.take target.toNat)
    (hcount : count = UInt32.ofNat bytes.length)
    (hreadStore : readStore = readAdapterResultStore
      (readToEndFillStore store (filled + (length + data)) (target - filled))
      (readToEndStack + 16) (length + data) bytes)
    (hrecurse : ∀ (consumed' remaining' : List UInt8)
      (store' : MachineStore Universal.State)
      (capacity' data' length' bump' chunk' filled'
        previousCount previousTarget previousBase previousSpare : UInt32),
      remaining'.length < remaining.length →
      BoundedReadInv input consumed' remaining' store' capacity' data' length' bump' →
      length' ≠ 0 →
      0 < chunk'.toNat →
      filled'.toNat ≤
        (readToEndTarget chunk' capacity' length').toNat →
      Result input
        (encodeReadContinuedConfig store' chunk' capacity' data' length'
          filled' previousCount previousTarget previousBase previousSpare)
        capacity'.toNat (length'.toNat + filled'.toNat) remaining'.length 512) :
    Result input
      (readToEndAfterReadSuccessConfig readStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
        capacity data length filled target count)
      capacity.toNat (length.toNat + target.toNat)
        (remaining.drop bytes.length).length (if bytes = [] then 22 else 547) := by
  let hinv := hbounded.toReadToEndInv
  have hfilledOriginal : filled.toNat ≤
      (readToEndTarget chunk capacity length).toNat := by
    simpa [htarget] using hfilled
  have hafter := hinv.after_read hfilledOriginal
  let updated := readToEndAppliedStore store data length filled target bytes
  have hafter' : ReadToEndInv input (consumed ++ bytes)
      (remaining.drop bytes.length) updated capacity data
      (length + UInt32.ofNat bytes.length) bump := by
    simpa [updated, htarget, hbytes] using hafter
  have hcountNat : count.toNat = bytes.length := by
    rw [hcount]
    apply UInt32.toNat_ofNat_of_lt'
    have hle := hinv.bytes_length_le_target (chunk := chunk)
    have hle' : bytes.length ≤ target.toNat := by
      simp [hbytes]
    have ht := hinv.target_le_spare (chunk := chunk)
    have hc := hinv.capacity_small
    have ht' : target.toNat ≤ capacity.toNat := by
      rw [← htarget]
      exact le_trans ht (Nat.sub_le _ _)
    norm_num at hc ⊢
    omega
  have hcountLe : count ≤ target := by
    apply UInt32.le_iff_toNat_le.mpr
    rw [hcountNat]
    simp [hbytes]
  have hlengthBound : readToEndStack.toNat + 12 + 4 ≤
      readStore.wasm.mem.pages * 65536 := by
    have hp : 17 ≤ readStore.wasm.mem.pages := by
      rw [hreadStore]
      simpa only [readAdapterResultStore_pages, readToEndFillStore,
        Mem.fill_pages] using hinv.pages_lower
    change 1048528 ≤ readStore.wasm.mem.pages * 65536
    omega
  have hupdated : updated =
      readToEndLengthStore readStore readToEndStack count length := by
    simp [updated, readToEndAppliedStore, hreadStore, hcount]
  have hnewInv : ReadToEndInv input (consumed ++ bytes)
      (remaining.drop bytes.length)
      (readToEndLengthStore readStore readToEndStack count length)
      capacity data (length + count) bump := by
    rw [← hupdated]
    simpa [hcount] using hafter'
  by_cases hempty : bytes = []
  · have htargetPos := hinv.target_positive hchunk hspare
    have htargetPos' : 0 < target.toNat := by simpa [htarget] using htargetPos
    have hremainingNil : remaining = [] := by
      rcases List.take_eq_nil_iff.mp (by simpa [hbytes] using hempty) with
        hzero | hnil
      · omega
      · exact hnil
    have hconsumed : consumed = input := by
      simpa [hremainingNil] using hinv.split
    have hcountZero : count = 0 := by simp [hcount, hempty]
    have hreturn := read_to_end_after_read_eof_steps_trace readStore [] encodeLocals []
      (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
      capacity data length filled target count hcountZero hlengthBound
    have hnewBounded : BoundedReadInv input input []
        (readToEndLengthStore readStore readToEndStack count length)
        capacity data (length + count) bump := by
      refine ⟨?_, hbounded.capacity_upper, hbounded.bump_upper⟩
      rw [hremainingNil, hempty] at hnewInv
      simpa [hconsumed] using hnewInv
    have hinitialized : length.toNat + target.toNat ≤ capacity.toNat := by
      have ht := hinv.target_le_spare (chunk := chunk)
      rw [htarget] at ht
      have hl := hinv.length_le_capacity
      omega
    have hsuffix := return_cost input readStore chunk capacity data length filled target count bump
      (length.toNat + target.toNat) hnewBounded hinitialized
    apply Result.prepend_scalar hreturn rfl _ hsuffix
    simp only [hempty, if_pos, hremainingNil, List.length_nil, List.drop_nil]
    omega

  · have hcountNe : count ≠ 0 := by
      intro hz
      have hzNat := congrArg UInt32.toNat hz
      rw [hcountNat] at hzNat
      exact hempty (List.eq_nil_of_length_eq_zero (by simpa using hzNat))
    have hdecrease : (remaining.drop bytes.length).length < remaining.length := by
      rw [List.length_drop]
      have hpos : 0 < bytes.length := List.length_pos_iff.mpr hempty
      have hle : bytes.length ≤ remaining.length := by
        simp [hbytes]
      omega
    have hnextLength : (length + count).toNat =
        length.toNat + count.toNat := by
      calc
        (length + count).toNat = (consumed ++ bytes).length :=
          hnewInv.length_nat
        _ = consumed.length + bytes.length := List.length_append
        _ = length.toNat + count.toNat := by
          rw [hinv.length_nat, hcountNat]
    have hnextLengthNe : length + count ≠ 0 := by
      intro hz
      have hzNat := congrArg UInt32.toNat hz
      rw [hnextLength] at hzNat
      have hc : count.toNat ≠ 0 := by
        intro hz
        apply hcountNe
        apply UInt32.toNat_inj.mp
        simpa using hz
      simp at hzNat
      omega
    have hnextFilled : (target - count).toNat ≤
        (readToEndTarget chunk capacity (length + count)).toNat := by
      have hcNat : count.toNat ≤ target.toNat :=
        UInt32.le_iff_toNat_le.mp hcountLe
      simpa [htarget] using hinv.next_filled_le_target
        (chunk := chunk) (count := count) hnewInv
        (by simpa [htarget] using hcNat) hnextLength
    have hinitialized : (length + count).toNat + (target - count).toNat =
        length.toNat + target.toNat := by
      rw [hnextLength, UInt32.toNat_sub_of_le target count (UInt32.le_iff_toNat_le.mp hcountLe)]
      have hc := UInt32.le_iff_toNat_le.mp hcountLe
      omega
    by_cases hspareLt : capacity - length < chunk
    · have hreach := read_to_end_after_read_spare_lt_steps_trace readStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
        capacity data length filled target count hcountNe hspareLt hlengthBound
      have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length) updated
        capacity data (length + count) bump chunk (target - count)
        count target (length + data) (capacity - length) hdecrease
        (by exact ⟨by simpa [updated, hcount] using hafter', hbounded.capacity_upper, hbounded.bump_upper⟩) hnextLengthNe hchunk hnextFilled
      refine Result.prepend_scalar (nextCapacity := capacity.toNat)
        (nextInitialized := (length + count).toNat + (target - count).toNat)
        (nextUnread := (remaining.drop bytes.length).length) (nextSlack := 512)
        hreach rfl ?_ ?_
      · simp only [if_neg hempty]
        omega
      · simpa only [encodeReadContinuedConfig, hupdated] using hsuffix
    · by_cases hpartial : target ≠ count
      · have hreach := read_to_end_after_read_partial_steps_trace readStore [] encodeLocals []
          (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
          capacity data length filled target count hcountNe hspareLt hpartial
          hlengthBound
        have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length) updated
          capacity data (length + count) bump chunk (target - count)
          count target (length + data) (capacity - length) hdecrease
          (by exact ⟨by simpa [updated, hcount] using hafter', hbounded.capacity_upper, hbounded.bump_upper⟩) hnextLengthNe hchunk hnextFilled
        refine Result.prepend_scalar (nextCapacity := capacity.toNat)
          (nextInitialized := (length + count).toNat + (target - count).toNat)
          (nextUnread := (remaining.drop bytes.length).length) (nextSlack := 512)
          hreach rfl ?_ ?_
        · simp only [if_neg hempty]
          omega
        · simpa only [encodeReadContinuedConfig, hupdated] using hsuffix
      · have hfull : target = count := not_ne_iff.mp hpartial
        by_cases hnegative : chunk.toInt32 < (0 : UInt32).toInt32
        · have hreach := read_to_end_after_read_full_saturate_steps_trace readStore []
            encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
            readToEndStack chunk capacity data length filled target count
            hcountNe hspareLt hfull hnegative hlengthBound
          have hfilledZero : target - count = 0 := by
            rw [hfull]
            simp
          have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length)
            updated capacity data (length + count) bump 4294967295 0 1 target
            (length + data) (capacity - length) hdecrease
            (by exact ⟨by simpa [updated, hcount] using hafter', hbounded.capacity_upper, hbounded.bump_upper⟩) hnextLengthNe
            (by decide) (by simp)
          refine Result.prepend_scalar (nextCapacity := capacity.toNat)
            (nextInitialized := (length + count).toNat + (target - count).toNat)
            (nextUnread := (remaining.drop bytes.length).length) (nextSlack := 512)
            hreach rfl ?_ ?_
          · simp only [if_neg hempty]
            omega
          · simpa only [encodeReadContinuedConfig, hupdated, hfilledZero] using hsuffix
        · have hreach := read_to_end_after_read_full_double_steps_trace readStore []
            encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
            readToEndStack chunk capacity data length filled target count
            hcountNe hspareLt hfull hnegative hlengthBound
          have hfilledZero : target - count = 0 := by
            rw [hfull]
            simp
          have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length)
            updated capacity data (length + count) bump (chunk <<< 1) 0 0
            target (length + data) (capacity - length) hdecrease
            (by exact ⟨by simpa [updated, hcount] using hafter', hbounded.capacity_upper, hbounded.bump_upper⟩) hnextLengthNe
            (shiftLeft_one_pos chunk hchunk hnegative) (by simp)
          refine Result.prepend_scalar (nextCapacity := capacity.toNat)
            (nextInitialized := (length + count).toNat + (target - count).toNat)
            (nextUnread := (remaining.drop bytes.length).length) (nextSlack := 512)
            hreach rfl ?_ ?_
          · simp only [if_neg hempty]
            omega
          · simpa only [encodeReadContinuedConfig, hupdated, hfilledZero] using hsuffix


set_option maxHeartbeats 1200000 in
theorem continued_direct_cost
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk filled previousTarget previousBase
      previousSpare : UInt32)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat)
    (hspare : length ≠ capacity)
    (hfilled : filled.toNat ≤
      (readToEndTarget chunk capacity length).toNat)
    (hrecurse : ∀ (consumed' remaining' : List UInt8)
      (store' : MachineStore Universal.State)
      (capacity' data' length' bump' chunk' filled'
        previousCount' previousTarget' previousBase' previousSpare' : UInt32),
      remaining'.length < remaining.length →
      BoundedReadInv input consumed' remaining' store' capacity' data' length' bump' →
      length' ≠ 0 →
      0 < chunk'.toNat →
      filled'.toNat ≤
        (readToEndTarget chunk' capacity' length').toNat →
      Result input
        (encodeReadContinuedConfig store' chunk' capacity' data' length'
          filled' previousCount' previousTarget' previousBase' previousSpare')
        capacity'.toNat (length'.toNat + filled'.toNat) remaining'.length 512) :
    Result input
      (readToEndContinuedDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length filled previousTarget previousBase previousSpare)
      capacity.toNat (length.toNat + filled.toNat) remaining.length 256 := by
  let hinv := hbounded.toReadToEndInv
  let target := readToEndTarget chunk capacity length
  let bytes := remaining.take target.toNat
  let count := UInt32.ofNat bytes.length
  let remainCount := target - filled
  have hbounds := hinv.direct_read_bounds (chunk := chunk) (filled := filled)
    hfilled
  have hcountLe : count ≤ target := by
    apply UInt32.le_iff_toNat_le.mpr
    have ht : target.toNat ≤ capacity.toNat := by
      exact le_trans (by simpa [target] using
        hinv.target_le_spare (chunk := chunk)) (Nat.sub_le _ _)
    have hc : bytes.length < UInt32.size := by
      have hbl : bytes.length ≤ target.toNat := by simp [bytes]
      have hcap : capacity.toNat < UInt32.size := by
        have hs := hinv.capacity_small
        norm_num [UInt32.size] at hs ⊢
        omega
      exact lt_of_le_of_lt (le_trans hbl ht) hcap
    rw [show count.toNat = bytes.length from
      UInt32.toNat_ofNat_of_lt' hc]
    exact List.length_take_le target.toNat remaining
  have htagBound (s : MachineStore Universal.State)
      (hp : s.wasm.mem.pages = store.wasm.mem.pages) :
      readToEndStack.toNat + 16 + 1 ≤ s.wasm.mem.pages * 65536 := by
    rw [hp]
    have := hinv.pages_lower
    change 1048529 ≤ store.wasm.mem.pages * 65536
    omega
  have hcountBound (s : MachineStore Universal.State)
      (hp : s.wasm.mem.pages = store.wasm.mem.pages) :
      readToEndStack.toNat + 20 + 4 ≤ s.wasm.mem.pages * 65536 := by
    rw [hp]
    have := hinv.pages_lower
    change 1048536 ≤ store.wasm.mem.pages * 65536
    omega
  by_cases hremainZero : remainCount = 0
  · let readStore := readAdapterResultStore store (readToEndStack + 16)
      (length + data) bytes
    have hdirect := read_to_end_continued_direct_read_no_fill_cost store []
      encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
      readToEndStack chunk capacity data length filled target previousTarget
      previousBase previousSpare bytes rfl (by simpa [remainCount] using
        hremainZero) hinv.runtime_module hinv.runtime_host
      (by simp [bytes, hinv.input_eq]) hbounds.2.1 hbounds.2.2
    have hafterAdapter := read_to_end_continued_after_adapter_success_steps_trace readStore
      [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
      readToEndStack chunk capacity data length filled target 0 count
      (readAdapterResultStore_read_tag store (readToEndStack + 16)
        (length + data) bytes (by decide))
      (readAdapterResultStore_read_count store (readToEndStack + 16)
        (length + data) bytes)
      hcountLe (htagBound readStore (by rfl))
      (hcountBound readStore (by rfl))
    have hsub : (target - filled).toNat = target.toNat - filled.toNat :=
      UInt32.toNat_sub_of_le target filled hfilled
    refine Result.prepend_read (bytes := bytes) (remaining := remaining) (read_then_scalar hdirect hafterAdapter) ?_ (by decide)
      hfilled (by simp only [bytes, List.length_take]; exact Nat.min_le_right _ _) rfl ?_
    · have hz : target.toNat - filled.toNat = 0 := by
        rw [← hsub]
        change remainCount.toNat = 0
        rw [hremainZero]
        rfl
      change bytes.length = target.toNat - filled.toNat + bytes.length
      simp only [hz, Nat.zero_add]
    · apply after_read_cost input consumed remaining store
        readStore capacity data length bump chunk filled target count bytes hbounded
        hchunk hspare rfl (by simpa [target] using hfilled) rfl rfl
      · have hrNat : (target - filled).toNat = 0 := by
          simpa [remainCount] using congrArg UInt32.toNat hremainZero
        simp only [readStore]
        congr 1
        simp [readToEndFillStore, hrNat, Mem.fill_zero]
      · exact hrecurse
  · let filledStore := readToEndFillStore store
      (filled + (length + data)) remainCount
    let readStore := readAdapterResultStore filledStore (readToEndStack + 16)
      (length + data) bytes
    have hdirect := read_to_end_continued_direct_read_cost store [] encodeLocals []
      (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
      capacity data length filled target remainCount previousTarget previousBase
      previousSpare bytes rfl rfl hremainZero hinv.runtime_module
      hinv.runtime_host (by simp [bytes, hinv.input_eq]) hbounds.1 hbounds.2.1
      hbounds.2.2
    have hafterAdapter := read_to_end_continued_after_adapter_success_steps_trace readStore
      [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
      readToEndStack chunk capacity data length filled target remainCount count
      (readAdapterResultStore_read_tag filledStore (readToEndStack + 16)
        (length + data) bytes (by decide))
      (readAdapterResultStore_read_count filledStore (readToEndStack + 16)
        (length + data) bytes)
      hcountLe (htagBound readStore (by rfl))
      (hcountBound readStore (by rfl))
    have hsub : (target - filled).toNat = target.toNat - filled.toNat :=
      UInt32.toNat_sub_of_le target filled hfilled
    refine Result.prepend_read (bytes := bytes) (remaining := remaining) (read_then_scalar hdirect hafterAdapter) ?_ (by decide)
      hfilled (by simp only [bytes, List.length_take]; exact Nat.min_le_right _ _) rfl ?_
    · change remainCount.toNat + bytes.length = target.toNat - filled.toNat + bytes.length
      rw [show remainCount.toNat = target.toNat - filled.toNat from hsub]
    · apply after_read_cost input consumed remaining store
        readStore capacity data length bump chunk filled target count bytes hbounded
        hchunk hspare rfl (by simpa [target] using hfilled) rfl rfl
      · rfl
      · exact hrecurse

set_option maxHeartbeats 1200000 in
theorem grown_direct_cost
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk previousTarget previousBase scratch9
      status : UInt32)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat)
    (hspare : length ≠ capacity)
    (hstatus : (status &&& 4294967040) ||| 4 = 4)
    (hrecurse : ∀ (consumed' remaining' : List UInt8)
      (store' : MachineStore Universal.State)
      (capacity' data' length' bump' chunk' filled'
        previousCount' previousTarget' previousBase' previousSpare' : UInt32),
      remaining'.length < remaining.length →
      BoundedReadInv input consumed' remaining' store' capacity' data' length' bump' →
      length' ≠ 0 →
      0 < chunk'.toNat →
      filled'.toNat ≤
        (readToEndTarget chunk' capacity' length').toNat →
      Result input
        (encodeReadContinuedConfig store' chunk' capacity' data' length'
          filled' previousCount' previousTarget' previousBase' previousSpare')
        capacity'.toNat (length'.toNat + filled'.toNat) remaining'.length 512) :
    Result input
      (readToEndGrownDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length 0 previousTarget previousBase scratch9 status)
      capacity.toNat (length.toNat + 0) remaining.length 256 := by
  let hinv := hbounded.toReadToEndInv
  let target := readToEndTarget chunk capacity length
  let bytes := remaining.take target.toNat
  let count := UInt32.ofNat bytes.length
  have htargetPos := hinv.target_positive hchunk hspare
  have htargetNe : target ≠ 0 := by
    intro hz
    have := congrArg UInt32.toNat hz
    have hp : 0 < target.toNat := by simpa [target] using htargetPos
    simp at this
    omega
  have hbounds := hinv.direct_read_bounds (chunk := chunk) (filled := 0) (by simp)
  let filledStore := readToEndFillStore store (length + data) target
  let readStore := readAdapterResultStore filledStore (readToEndStack + 16)
    (length + data) bytes
  have hcountLe : count ≤ target := by
    apply UInt32.le_iff_toNat_le.mpr
    have ht : target.toNat ≤ capacity.toNat := by
      exact le_trans (by simpa [target] using
        hinv.target_le_spare (chunk := chunk)) (Nat.sub_le _ _)
    have hc : bytes.length < UInt32.size := by
      have hbl : bytes.length ≤ target.toNat := by simp [bytes]
      have hcap : capacity.toNat < UInt32.size := by
        have hs := hinv.capacity_small
        norm_num [UInt32.size] at hs ⊢
        omega
      exact lt_of_le_of_lt (le_trans hbl ht) hcap
    rw [show count.toNat = bytes.length from UInt32.toNat_ofNat_of_lt' hc]
    exact List.length_take_le target.toNat remaining
  have hdirect := read_to_end_grown_direct_read_cost store [] encodeLocals []
    (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
    capacity data length 0 target target previousTarget previousBase scratch9
    status bytes rfl (by simp) htargetNe hinv.runtime_module hinv.runtime_host
    (by simp [bytes, hinv.input_eq]) (by simpa [filledStore] using hbounds.1)
    hbounds.2.1 hbounds.2.2
  have htagBound : readToEndStack.toNat + 16 + 1 ≤
      readStore.wasm.mem.pages * 65536 := by
    have hp : 17 ≤ readStore.wasm.mem.pages := by
      change 17 ≤ store.wasm.mem.pages
      exact hinv.pages_lower
    change 1048529 ≤ readStore.wasm.mem.pages * 65536
    omega
  have hcountBound : readToEndStack.toNat + 20 + 4 ≤
      readStore.wasm.mem.pages * 65536 := by
    have hp : 17 ≤ readStore.wasm.mem.pages := by
      change 17 ≤ store.wasm.mem.pages
      exact hinv.pages_lower
    change 1048536 ≤ readStore.wasm.mem.pages * 65536
    omega
  have hafterAdapter := read_to_end_grown_after_adapter_success_steps_trace readStore []
    encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
    readToEndStack chunk capacity data length 0 target target count previousBase
    scratch9 status hstatus
    (readAdapterResultStore_read_tag filledStore (readToEndStack + 16)
      (length + data) bytes (by decide))
    (readAdapterResultStore_read_count filledStore (readToEndStack + 16)
      (length + data) bytes)
    hcountLe htagBound hcountBound
  have hcombined := read_then_scalar hdirect (by
    simpa [readStore, filledStore] using hafterAdapter)
  refine Result.prepend_read (bytes := bytes) (remaining := remaining) hcombined ?_ (by decide)
    (by omega : 0 ≤ target.toNat)
    (by simp only [bytes, List.length_take]; exact Nat.min_le_right _ _) rfl ?_
  · simp
  · apply after_read_cost input consumed remaining store
      readStore capacity data length bump chunk 0 target count bytes hbounded hchunk
      hspare rfl (by simp) rfl rfl
    · simp [readStore, filledStore]
    · exact hrecurse

/-- Actual byte reallocation and installation in the read vector. The bounded
frontier proves successful growth from the original physical cap. -/
theorem growth_cost (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk scratch9 status : UInt32)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hfull : length = capacity) (hfit : InputFits input.length) :
    let allocStore := ReserveResourceCost.allocationStore store capacity data
      (readToEndNewCapacity capacity) bump
    let grown := readToEndGrownStore allocStore capacity bump
    ∃ trace, trace.length ≤ 119 ∧
      CostedSteps CostedStdIO.work
        (readToEndGrowCallConfig store [] encodeLocals []
          (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
          chunk capacity data length 0 scratch9 status) trace
        (readToEndGrownDirectConfig grown [] encodeLocals []
          (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
          chunk (readToEndNewCapacity capacity) bump length 0
          (readToEndNewCapacity capacity) (capacity <<< 1) scratch9 status)
        (trace.length + capacity.toNat + 65536 * (grown.wasm.mem.pages - store.wasm.mem.pages)) ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) ∧
      BoundedReadInv input consumed remaining grown (readToEndNewCapacity capacity) bump length
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump) ∧
      grown.wasm.mem.pages = max store.wasm.mem.pages (AllocatorResourceCost.requiredPages
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat) := by
  dsimp only
  let hinv := hbounded.toReadToEndInv
  let allocStore := ReserveResourceCost.allocationStore store capacity data
    (readToEndNewCapacity capacity) bump
  let grown := readToEndGrownStore allocStore capacity bump
  let okStore := growResultOkStore allocStore (readToEndStack + 16)
    (allocatorPtr bump 1) (readToEndNewCapacity capacity)
  have hbase : allocatorBase bump = bump := by simp [allocatorBase, hinv.bump_ne_zero]
  have hfinish := growth_finish_bound hbounded hfull hfit
  have hfit' : (allocatorBase bump).toNat + (readToEndNewCapacity capacity).toNat < 2147483648 := by
    rw [hbase]
    rw [hinv.finish_toNat] at hfinish
    exact hfinish.2
  have hcapNe : capacity ≠ 0 := by
    intro hz
    have hc := hinv.capacity_pos
    rw [hz] at hc
    contradiction
  obtain ⟨front, frontLength, frontRun, success, frontLabels⟩ :=
    ReserveResourceCost.byte_grow_cost store
      [.i32 1048552]
      [.i32 readToEndStack, .i32 chunk, .i32 capacity, .i32 length, .i32 0,
        .i32 data, .i32 (readToEndNewCapacity capacity),
        .i32 (capacity <<< 1), .i32 scratch9, .i32 0, .i32 status,
        .i32 0, .i32 0, .i64 0]
      [] (readToEndGrowthCheck.drop 23) 0 [] readToEndGrowthControls
      [{ locals := ⟨[], encodeLocals, []⟩, continuation := Project.HexStdio.func10.drop 9,
         resultArity := 0, callerRemainder := [], control := [], returningInstance := store.runtime.entry }]
      (readToEndStack + 16) capacity data (readToEndNewCapacity capacity) bump
      hinv.runtime_module hinv.memory_cap hinv.pages_upper hinv.bump_eq
      (by have hp := hinv.pages_lower; omega) hfit'
      (readToEndNewCapacity_gt capacity hinv.capacity_small) hinv.data_bound
      (by have hp := hinv.pages_lower; change 1048540 ≤ _; omega)
  have hgrown := hbounded.after_growth hfull hfit success
  have hpages : 17 ≤ okStore.wasm.mem.pages := by
    change 17 ≤ allocStore.wasm.mem.pages
    exact le_trans hinv.pages_lower success.pages_mono
  have after := read_to_end_after_grow_success_steps_trace okStore []
    encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
    readToEndStack chunk capacity data length 0 scratch9 status bump
    (by simpa [okStore] using (growResultOkStore_read_tag allocStore
      (readToEndStack + 16) (allocatorPtr bump 1) (readToEndNewCapacity capacity)))
    (by simpa [okStore, hinv.allocator_ptr] using
      (growResultOkStore_read_ptr allocStore (readToEndStack + 16)
        (allocatorPtr bump 1) (readToEndNewCapacity capacity) (by decide)))
    (by change 1048532 ≤ okStore.wasm.mem.pages * 65536; omega)
    (by change 1048536 ≤ okStore.wasm.mem.pages * 65536; omega)
    (by change 1048524 ≤ okStore.wasm.mem.pages * 65536; omega)
    (by change 1048520 ≤ okStore.wasm.mem.pages * 65536; omega)
  obtain ⟨tail, tailRun, tailLength, tailLabels⟩ := after.costed
  have first : CostedSteps CostedStdIO.work
      (readToEndGrowCallConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length 0 scratch9 status) front
      (readToEndAfterGrowConfig okStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length 0 scratch9 status)
      (front.length + capacity.toNat + 65536 *
        (AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat +
          (readToEndNewCapacity capacity).toNat) - store.wasm.mem.pages)) := by
    have hruntime : okStore.runtime = store.runtime := success.runtime_eq
    simpa only [readToEndGrowCallConfig, readToEndAfterGrowConfig, growResultFinal,
      okStore, allocStore, hruntime, List.cons_append, List.nil_append] using frontRun
  have pages : grown.wasm.mem.pages = max store.wasm.mem.pages (AllocatorResourceCost.requiredPages
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat) := by
    change allocStore.wasm.mem.pages = _
    rw [ReserveResourceCost.allocationStore_pages, hbase, hinv.finish_toNat]
  refine ⟨front ++ tail, ?_, ?_, ?_, hgrown, pages⟩
  · simp only [List.length_append, tailLength]
    simp only [if_neg hcapNe] at frontLength
    omega
  · have complete := first.trans tailRun
    convert complete using 1
    · simp only [readToEndGrownStore, okStore, allocStore, hinv.allocator_ptr]
    · rw [List.length_append, tailLength, pages, hbase, hinv.finish_toNat]
      omega
  · intro kind member
    rcases List.mem_append.mp member with head | rest
    · have label := frontLabels kind head
      cases kind <;> first | exact label | trivial
    · exact tailLabels kind rest


set_option maxHeartbeats 1200000 in
/-- Complete adaptive loop: its induction follows actual positive reads. Growth
before EOF is included, and every allocator guard follows from the input bound. -/
theorem continued_loop_cost (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk filled previousCount previousTarget
      previousBase previousSpare : UInt32)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hlengthNe : length ≠ 0) (hchunk : 0 < chunk.toNat)
    (hfilled : filled.toNat ≤ (readToEndTarget chunk capacity length).toNat)
    (hfit : InputFits input.length) :
    Result input
      (encodeReadContinuedConfig store chunk capacity data length filled
        previousCount previousTarget previousBase previousSpare)
      capacity.toNat (length.toNat + filled.toNat) remaining.length 512 := by
  induction hmeasure : remaining.length using Nat.strong_induction_on
      generalizing consumed remaining store capacity data length bump chunk
        filled previousCount previousTarget previousBase previousSpare with
  | h n ih =>
      subst hmeasure
      let hinv := hbounded.toReadToEndInv
      have hdataBound : readToEndStack.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536 := by
        have hp := hinv.pages_lower
        change 1048524 ≤ store.wasm.mem.pages * 65536
        omega
      by_cases hfull : length = capacity
      · have htargetZero : readToEndTarget chunk capacity length = 0 := by
          simp [readToEndTarget, hfull]
        have hfilledZero : filled = 0 := by
          apply UInt32.toNat_inj.mp
          have hf := hfilled
          rw [htargetZero] at hf
          simpa using Nat.eq_zero_of_le_zero hf
        subst filled
        have first := read_to_end_continued_loop_to_grow_steps_trace store []
          encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
          readToEndStack chunk capacity data length 0 previousCount
          previousTarget previousBase previousSpare hlengthNe hfull hinv.data_eq hdataBound
        let allocStore := ReserveResourceCost.allocationStore store capacity data
          (readToEndNewCapacity capacity) bump
        let grown := readToEndGrownStore allocStore capacity bump
        obtain ⟨trace, traceLength, execution, labels, newInvariant, pages⟩ :=
          growth_cost input consumed remaining store capacity data length bump chunk
            previousSpare 4 hbounded hfull hfit
        have hlengthNewNe : length ≠ readToEndNewCapacity capacity := by
          intro heq
          have hg := readToEndNewCapacity_gt capacity hinv.capacity_small
          have hn := congrArg UInt32.toNat heq
          rw [hfull] at hn
          omega
        have suffix := grown_direct_cost input consumed remaining grown
          (readToEndNewCapacity capacity) bump length
          (allocatorFinish (readToEndNewCapacity capacity) 1 bump) chunk
          (readToEndNewCapacity capacity) (capacity <<< 1) previousSpare 4
          newInvariant hchunk hlengthNewNe (by decide) (by
            intro consumed' remaining' store' capacity' data' length' bump'
              chunk' filled' previousCount' previousTarget' previousBase'
              previousSpare' hless inv' lengthNe' chunk'Pos filled'Bound
            exact ih remaining'.length hless consumed' remaining' store'
              capacity' data' length' bump' chunk' filled' previousCount'
              previousTarget' previousBase' previousSpare' inv' lengthNe'
              chunk'Pos filled'Bound rfl)
        refine Result.prepend_scalar (nextCapacity := capacity.toNat)
          (nextInitialized := length.toNat) (nextUnread := remaining.length) (nextSlack := 474)
          first rfl (by simp; omega) ?_
        apply Result.prepend execution labels _ _ suffix
        · change grown.wasm.mem.pages ≤ max store.wasm.mem.pages
            (AllocatorResourceCost.requiredPages (inputFrontierBound input.length))
          rw [pages]
          have finish := (growth_finish_bound hbounded hfull hfit).1
          have required : AllocatorResourceCost.requiredPages
              (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
              AllocatorResourceCost.requiredPages (inputFrontierBound input.length) := by
            unfold AllocatorResourceCost.requiredPages
            omega
          omega
        · change trace.length + capacity.toNat + 65536 * (grown.wasm.mem.pages - store.wasm.mem.pages) +
              capacity.toNat + length.toNat + 65536 * store.wasm.mem.pages + 513 * remaining.length + 256 ≤
            513 * remaining.length + 474 + (readToEndNewCapacity capacity).toNat +
              (length.toNat + 0) + 65536 * grown.wasm.mem.pages
          have hc := copied_capacity_bound hbounded
          have hp : store.wasm.mem.pages ≤ grown.wasm.mem.pages := by rw [pages]; omega
          omega
      · have first := read_to_end_continued_loop_skip_growth_steps_trace store []
          encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
          readToEndStack chunk capacity data length filled previousCount
          previousTarget previousBase previousSpare hlengthNe hfull hinv.data_eq hdataBound
        have suffix := continued_direct_cost input consumed remaining store
          capacity data length bump chunk filled previousTarget previousBase previousSpare
          hbounded hchunk hfull hfilled (by
            intro consumed' remaining' store' capacity' data' length' bump'
              chunk' filled' previousCount' previousTarget' previousBase'
              previousSpare' hless inv' lengthNe' chunk'Pos filled'Bound
            exact ih remaining'.length hless consumed' remaining' store'
              capacity' data' length' bump' chunk' filled' previousCount'
              previousTarget' previousBase' previousSpare' inv' lengthNe'
              chunk'Pos filled'Bound rfl)
        exact Result.prepend_scalar first rfl (by omega) suffix


set_option maxHeartbeats 1200000 in
theorem initial_direct_cost
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk : UInt32)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat) (hspare : length ≠ capacity) (hfit : InputFits input.length) :
    Result input
      (readToEndDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length 0)
      capacity.toNat (length.toNat + 0) remaining.length 256 := by
  let hinv := hbounded.toReadToEndInv
  let target := readToEndTarget chunk capacity length
  let bytes := remaining.take target.toNat
  let count := UInt32.ofNat bytes.length
  let filledStore := readToEndFillStore store (length + data) target
  let readStore := readAdapterResultStore filledStore (readToEndStack + 16)
    (length + data) bytes
  have htargetPos := hinv.target_positive hchunk hspare
  have htargetNe : target ≠ 0 := by
    intro hz
    have hz' := congrArg UInt32.toNat hz
    have hp : 0 < target.toNat := by simpa [target] using htargetPos
    simp at hz'
    omega
  have hbounds := hinv.direct_read_bounds (chunk := chunk) (filled := 0) (by simp)
  have hcountLe : count ≤ target := by
    apply UInt32.le_iff_toNat_le.mpr
    have ht : target.toNat ≤ capacity.toNat := by
      exact le_trans (by simpa [target] using
        hinv.target_le_spare (chunk := chunk)) (Nat.sub_le _ _)
    have hc : bytes.length < UInt32.size := by
      have hbl : bytes.length ≤ target.toNat := by simp [bytes]
      have hcap : capacity.toNat < UInt32.size := by
        have hs := hinv.capacity_small
        norm_num [UInt32.size] at hs ⊢
        omega
      exact lt_of_le_of_lt (le_trans hbl ht) hcap
    rw [show count.toNat = bytes.length from UInt32.toNat_ofNat_of_lt' hc]
    exact List.length_take_le target.toNat remaining
  have hdirect := read_to_end_direct_read_cost store [] encodeLocals []
    (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack chunk
    capacity data length 0 target target bytes rfl (by simp) htargetNe
    hinv.runtime_module hinv.runtime_host (by simp [bytes, hinv.input_eq])
    (by simpa [filledStore] using hbounds.1) hbounds.2.1 hbounds.2.2
  have htagBound : readToEndStack.toNat + 16 + 1 ≤
      readStore.wasm.mem.pages * 65536 := by
    have hp : 17 ≤ readStore.wasm.mem.pages := by
      change 17 ≤ store.wasm.mem.pages
      exact hinv.pages_lower
    change 1048529 ≤ readStore.wasm.mem.pages * 65536
    omega
  have hcountBound : readToEndStack.toNat + 20 + 4 ≤
      readStore.wasm.mem.pages * 65536 := by
    have hp : 17 ≤ readStore.wasm.mem.pages := by
      change 17 ≤ store.wasm.mem.pages
      exact hinv.pages_lower
    change 1048536 ≤ readStore.wasm.mem.pages * 65536
    omega
  have hafterAdapter := read_to_end_after_adapter_success_steps_trace readStore []
    encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
    readToEndStack chunk capacity data length 0 target target count
    (readAdapterResultStore_read_tag filledStore (readToEndStack + 16)
      (length + data) bytes (by decide))
    (readAdapterResultStore_read_count filledStore (readToEndStack + 16)
      (length + data) bytes)
    hcountLe htagBound hcountBound
  have hdirect' : ReadCostRun
      (readToEndDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length 0)
      (readToEndAfterAdapterConfig readStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552 readToEndStack
        chunk capacity data length 0 target target) 47 (target.toNat + bytes.length) := by
    simpa [readStore, filledStore] using hdirect
  refine Result.prepend_read (bytes := bytes) (remaining := remaining)
    (read_then_scalar hdirect' hafterAdapter) ?_ (by decide)
    (by omega : 0 ≤ target.toNat)
    (by simp only [bytes, List.length_take]; exact Nat.min_le_right _ _) rfl ?_
  · simp
  · apply after_read_cost input consumed remaining store
      readStore capacity data length bump chunk 0 target count bytes hbounded hchunk
      hspare rfl (by simp) rfl rfl
    · simp [readStore, filledStore]
    · intro consumed' remaining' store' capacity' data' length' bump' chunk'
        filled' previousCount' previousTarget' previousBase' previousSpare'
        hless hinv' hlengthNe' hchunk' hfilled'
      exact continued_loop_cost input consumed' remaining' store'
        capacity' data' length' bump' chunk' filled' previousCount'
        previousTarget' previousBase' previousSpare' hinv' hlengthNe' hchunk'
        hfilled' hfit

set_option maxHeartbeats 1200000 in
/-- Complete nonempty read-to-end loop from its actual first-iteration boundary. -/
theorem loop_cost (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State) (capacity data length bump chunk : UInt32)
    (hbounded : BoundedReadInv input consumed remaining store capacity data length bump)
    (hlengthNe : length ≠ 0) (hchunk : 0 < chunk.toNat) (hfit : InputFits input.length) :
    Result input (encodeReadLoopConfig store chunk capacity data length 0)
      capacity.toNat (length.toNat + 0) remaining.length 512 := by
  let hinv := hbounded.toReadToEndInv
  have hdataBound : readToEndStack.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536 := by
    have hp := hinv.pages_lower
    change 1048524 ≤ store.wasm.mem.pages * 65536
    omega
  by_cases hfull : length = capacity
  · have first := read_to_end_loop_to_grow_steps_trace store []
      encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
      readToEndStack chunk capacity data length 0 hlengthNe hfull hinv.data_eq hdataBound
    let allocStore := ReserveResourceCost.allocationStore store capacity data
      (readToEndNewCapacity capacity) bump
    let grown := readToEndGrownStore allocStore capacity bump
    obtain ⟨trace, traceLength, execution, labels, newInvariant, pages⟩ :=
      growth_cost input consumed remaining store capacity data length bump chunk
        0 0 hbounded hfull hfit
    have hlengthNewNe : length ≠ readToEndNewCapacity capacity := by
      intro heq
      have hg := readToEndNewCapacity_gt capacity hinv.capacity_small
      have hn := congrArg UInt32.toNat heq
      rw [hfull] at hn
      omega
    have suffix := grown_direct_cost input consumed remaining grown
      (readToEndNewCapacity capacity) bump length
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump) chunk
      (readToEndNewCapacity capacity) (capacity <<< 1) 0 0
      newInvariant hchunk hlengthNewNe (by decide) (by
        intro consumed' remaining' store' capacity' data' length' bump'
          chunk' filled' previousCount' previousTarget' previousBase'
          previousSpare' hless inv' lengthNe' chunk'Pos filled'Bound
        exact continued_loop_cost input consumed' remaining' store'
          capacity' data' length' bump' chunk' filled' previousCount'
          previousTarget' previousBase' previousSpare' inv' lengthNe'
          chunk'Pos filled'Bound hfit)

    refine Result.prepend_scalar (nextCapacity := capacity.toNat)
      (nextInitialized := length.toNat) (nextUnread := remaining.length) (nextSlack := 474)
      first rfl (by simp; omega) ?_
    apply Result.prepend execution labels _ _ suffix
    · change grown.wasm.mem.pages ≤ max store.wasm.mem.pages
        (AllocatorResourceCost.requiredPages (inputFrontierBound input.length))
      rw [pages]
      have finish := (growth_finish_bound hbounded hfull hfit).1
      have required : AllocatorResourceCost.requiredPages
          (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
          AllocatorResourceCost.requiredPages (inputFrontierBound input.length) := by
        unfold AllocatorResourceCost.requiredPages
        omega
      omega
    · change trace.length + capacity.toNat + 65536 * (grown.wasm.mem.pages - store.wasm.mem.pages) +
          capacity.toNat + length.toNat + 65536 * store.wasm.mem.pages + 513 * remaining.length + 256 ≤
        513 * remaining.length + 474 + (readToEndNewCapacity capacity).toNat +
          (length.toNat + 0) + 65536 * grown.wasm.mem.pages
      have hc := copied_capacity_bound hbounded
      have hp : store.wasm.mem.pages ≤ grown.wasm.mem.pages := by rw [pages]; omega
      omega
  · have first := read_to_end_loop_skip_growth_steps_trace store []
      encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048552
      readToEndStack chunk capacity data length 0 hlengthNe hfull hinv.data_eq hdataBound
    have suffix := initial_direct_cost input consumed remaining store
      capacity data length bump chunk hbounded hchunk hfull hfit
    exact Result.prepend_scalar first rfl (by omega) suffix


theorem scalar_then_read {initial middle final : Config Universal.State} {n m bytes : Nat}
    (first : ScalarReadRun initial middle n) (second : ReadCostRun middle final m bytes) :
    ReadCostRun initial final (n + m) bytes := by
  obtain ⟨front, firstRun, frontLength, frontLabels⟩ := first.costed
  obtain ⟨tail, secondRun, tailLength, tailLabels⟩ := second
  refine ⟨front ++ tail, ?_, by simp [frontLength, tailLength], ?_⟩
  · simpa only [Nat.add_assoc] using firstRun.trans secondRun
  · intro kind member
    rcases List.mem_append.mp member with first | second
    · exact frontLabels kind first
    · exact tailLabels kind second

theorem chunk_prepend_scalar {initial middle : Config Universal.State}
    {post : Config Universal.State → Prop} {n bound bytes : Nat}
    (first : ScalarReadRun initial middle n)
    (second : ReadChunkResourceCost.ChunkCostOutcome middle post bound bytes) :
    ReadChunkResourceCost.ChunkCostOutcome initial post (n + bound) bytes := by
  obtain ⟨final, scalar, scalarBound, execution, result⟩ := second
  exact ⟨final, n + scalar, Nat.add_le_add_left scalarBound n, scalar_then_read first execution, result⟩

set_option maxHeartbeats 1200000 in
theorem first_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : store.wasm.mem.pages = 17)
    (hbump : store.wasm.mem.read32 1053960 = 0) :
    let bytes := store.wasm.host.stdio.input.take 32
    let framed := readToEndFrameStore store readToEndStack
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    ReadChunkResourceCost.ChunkCostOutcome
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, .i32 1048552 :: stack⟩,
            [.call 10] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      (fun final =>
        if bytes = [] then
          final =
            { expr := .running
                ⟨⟨[.i32 1048552],
                    [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
                      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                      .i32 0, .i32 0, .i64 0], []⟩,
                  readToEndAfterFirstRead, 0, [], [],
                  { locals := ⟨outerParams, outerLocalValues, stack⟩
                    continuation := code
                    resultArity := arity
                    callerRemainder := remainder
                    control := controls
                    returningInstance := store.runtime.entry } :: calls⟩
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
                  ⟨⟨[.i32 1048552],
                      [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0, .i64 0], []⟩,
                    readToEndAfterFirstRead, 0, [], [],
                    { locals := ⟨outerParams, outerLocalValues, stack⟩
                      continuation := code
                      resultArity := arity
                      callerRemainder := remainder
                      control := controls
                      returningInstance := store.runtime.entry } :: calls⟩
                store := readChunkFinishedStore
                  (readChunkCopiedStore reserved
                    (allocatorPtr 0 1) firstChunkBuffer count)
                  readToEndResult readToEndVector count 0 readToEndStack }) 286 (2 * bytes.length) := by
  dsimp only
  let framed := readToEndFrameStore store readToEndStack
  let bytes := store.wasm.host.stdio.input.take 32
  have hprefix := read_to_end_to_first_chunk_steps_trace store outerParams outerLocalValues
    stack code arity remainder controls calls 1048552 1048544 hmod hglobal
    (by rw [hpages]; decide)
  apply chunk_prepend_scalar (bound := 265) hprefix
  apply ReadChunkResourceCost.first_chunk_cost framed
      [.i32 1048552]
      [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0, .i64 0]
      [] readToEndAfterFirstRead 0 [] []
      ({ locals := ⟨outerParams, outerLocalValues, stack⟩
         continuation := code
         resultArity := arity
         callerRemainder := remainder
         control := controls
         returningInstance := store.runtime.entry } :: calls)
      bytes
  · simpa [framed] using hmod
  · simpa [framed] using henv
  · exact hcap
  · simp only [framed, readToEndFrameStore, globalAt?,
      canonicalGlobalIndex_zero] at hglobal ⊢
    have hzero : 0 < store.wasm.globals.globals.length :=
      (getElem?_eq_some_iff.mp hglobal).1
    simpa using (List.getElem?_set_eq_of_lt (.i32 readToEndStack) hzero)
  · rfl
  · simpa [framed] using hpages
  · simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32]
    decide
  · simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32]
    decide
  · rw [show readToEndVector + 8 = readToEndStack + 12 by decide]
    simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32]
  · simp only [framed, readToEndFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hbump
    · right; decide
    · right; decide


/-- The call10 configuration reached by the unchanged named encode export. -/
def readCallConfig (input : List UInt8) : Config Universal.State :=
  ⟨.running ⟨⟨[], encodeLocals, [.i32 1048552]⟩,
    [.call 10] ++ func10.drop 9, 0, [], [], []⟩, encodeFrameStore input⟩

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 100000 in
/-- The complete nonempty input call, including the fixed first chunk and the
adaptive reader, with no assumed allocation or future execution. -/
theorem nonempty_cost (input : List UInt8) (hinput : input ≠ [])
    (hfit : InputFits input.length) :
    Result input (readCallConfig input) 0 0 input.length 821 := by
  let bytes := input.take 32
  have hbytes : bytes = input.take 32 := rfl
  have hbytesNe : bytes ≠ [] := by
    cases input with
    | nil => exact (hinput rfl).elim
    | cons byte rest => simp [bytes]
  have hfirst := first_cost (encodeFrameStore input)
    [] encodeLocals [] (func10.drop 9) 0 [] [] []
    (by rfl) (by rfl) (by rfl) (by
      simp [encodeFrameStore, encodeInitialStore, globalAt?,
        canonicalGlobalIndex_zero]
      decide) (by rfl) (by
      simp [encodeFrameStore, encodeInitialStore, Mem.read32]
      decide)
  obtain ⟨first, scalar, scalarBound, firstRun, hfirstPost⟩ := hfirst
  have hstoreInput :
      (encodeFrameStore input).wasm.host.stdio.input = input := rfl
  rw [hstoreInput, ← hbytes] at hfirstPost
  simp only [hbytesNe, ↓reduceIte] at hfirstPost
  rcases hfirstPost with ⟨allocStore, hsuccess, rfl⟩
  let count := UInt32.ofNat bytes.length
  let capacity := reserveNewCapacity 0 count 0
  let data := allocatorPtr 0 1
  let bump := allocatorFinish capacity 1 0
  let framed := readToEndFrameStore (encodeFrameStore input) readToEndStack
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let reserved := reserveFinishStore
    (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
      data capacity)
    readToEndVector data capacity firstChunkFrame
  let finalStore := readChunkFinishedStore
    (readChunkCopiedStore reserved data firstChunkBuffer count)
    readToEndResult readToEndVector count 0 readToEndStack
  have hbounded : BoundedReadInv input bytes (input.drop bytes.length) finalStore
      capacity data count bump := by
    apply InputInitializationCost.first_bounded_invariant input bytes allocStore hbytes hbytesNe
    exact hsuccess
  let hinv := hbounded.toReadToEndInv
  have htoLoop := read_to_end_after_first_nonempty_to_loop_steps_trace finalStore
    [] encodeLocals [] (func10.drop 9) 0 [] [] [] 1048552 readToEndStack
    capacity data count
    (by
      simp [finalStore, readChunkFinishedStore, Mem.read8, Mem.write32,
        Mem.write8])
    (by
      simp only [finalStore, readChunkFinishedStore]
      rw [Mem.read32_write32_disjoint, Mem.read32_write8_disjoint]
      · exact Mem.read32_write32_same _ _ _
      all_goals decide)
    (by
      intro hz
      have := hinv.length_nat
      rw [hz] at this
      simp at this
      exact hbytesNe (List.eq_nil_of_length_eq_zero this.symm))
    hinv.capacity_eq hinv.data_eq hinv.length_eq
    (by have hp := hinv.pages_lower; change 1048529 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048536 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048520 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048524 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048528 ≤ _; omega)
  have hentryEq : finalStore.runtime.entry =
      (encodeFrameStore input).runtime.entry := by
    change allocStore.runtime.entry = (encodeFrameStore input).runtime.entry
    rw [hsuccess.runtime_eq]
    rfl
  rw [hentryEq] at htoLoop
  have loop := loop_cost input bytes (input.drop bytes.length)
    finalStore capacity data count bump 8192 hbounded
    (by
      intro hz
      have := hinv.length_nat
      rw [hz] at this
      simp at this
      exact hbytesNe (List.eq_nil_of_length_eq_zero this.symm))
    (by decide) hfit
  have firstPages : finalStore.wasm.mem.pages = 17 := by
    change allocStore.wasm.mem.pages = 17
    apply ReserveResourceCost.first_allocation_pages hsuccess rfl
    have hc := first_capacity_toNat bytes hbytesNe (by simp only [bytes, List.length_take]; omega)
    rw [hc]
    have hb : bytes.length ≤ 32 := by simp [bytes]
    omega
  have joined : Result input _ capacity.toNat count.toNat
      (input.drop bytes.length).length 535 :=
    Result.prepend_scalar htoLoop rfl (by omega) loop
  obtain ⟨trace, execution, _, labels⟩ := firstRun
  apply Result.prepend execution labels _ _ joined
  · change finalStore.wasm.mem.pages ≤ max 17
      (AllocatorResourceCost.requiredPages (inputFrontierBound input.length))
    rw [firstPages]
    exact Nat.le_max_left _ _
  · change scalar + 2 * bytes.length + 0 + 0 + 65536 * 17 +
        513 * (input.drop bytes.length).length + 535 ≤
      513 * input.length + 821 + capacity.toNat + count.toNat + 65536 * finalStore.wasm.mem.pages
    rw [firstPages, List.length_drop]
    have hb : bytes.length ≤ input.length := by simp [bytes]
    omega


/-- The concrete first-EOF store: the input descriptor remains capacity zero,
pointer one and length zero. -/
def emptyAfterFirstStore : MachineStore Universal.State :=
  let framed := readToEndFrameStore (encodeFrameStore []) readToEndStack
  let after := readAdapterResultStore (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer []
  readChunkFinishedStore after readToEndResult readToEndVector 0 0 readToEndStack

def emptyStore : MachineStore Universal.State :=
  readToEndFinishedStore emptyAfterFirstStore 1048552 readToEndStack 1048544 4294967296 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1200000 in
/-- Empty input takes its actual first-EOF arm and restores the original caller.
The reader performs no allocation or growth on this path. -/
theorem empty_cost :
    ∃ trace amount, amount ≤ 311 ∧
      CostedSteps CostedStdIO.work (readCallConfig []) trace (encodeAfterReadConfig emptyStore) amount ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  have first := first_cost (encodeFrameStore []) [] encodeLocals [] (func10.drop 9)
    0 [] [] [] rfl rfl rfl
    (by simp [encodeFrameStore, encodeInitialStore, globalAt?, canonicalGlobalIndex_zero]; decide)
    rfl (by simp [encodeFrameStore, encodeInitialStore, Mem.read32]; decide)
  obtain ⟨config, scalar, scalarBound, run, post⟩ := first
  have hbytes : (encodeFrameStore []).wasm.host.stdio.input.take 32 = [] := rfl
  simp only [hbytes] at post
  subst config
  have after := read_to_end_after_first_eof_steps_trace emptyAfterFirstStore [] encodeLocals []
    (func10.drop 9) 0 [] [] [] 1048552 readToEndStack 1048544 4294967296 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have combined := read_then_scalar run after
  obtain ⟨trace, execution, _, labels⟩ := combined
  refine ⟨trace, scalar + 25, by omega, ?_, labels⟩
  simpa only [hbytes, List.length_nil, Nat.mul_zero, Nat.add_zero, readCallConfig,
    encodeAfterReadConfig, emptyStore, emptyAfterFirstStore, readToEndFinishedStore,
    readChunkFinishedStore, readAdapterResultStore, readChunkFrameStore,
    readToEndFrameStore] using execution

set_option maxRecDepth 100000 in
theorem empty_store_facts :
    emptyStore.runtime.currentModule = Project.HexStdio.module ∧
    emptyStore.runtime.currentHost = Universal.envFor Project.HexStdio.module ∧
    emptyStore.wasm.mem.pages = 17 ∧
    emptyStore.wasm.mem.read32 1048552 = 0 ∧
    emptyStore.wasm.mem.read32 1048556 = 1 ∧
    emptyStore.wasm.mem.read32 1048560 = 0 ∧
    globalAt? emptyStore 0 = some (.i32 1048544) ∧
    emptyStore.wasm.host.stdio.input = [] ∧
    emptyStore.wasm.host.stdio.output = [] ∧
    emptyStore.wasm.host.oom.raised = false := by
  exact ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, rfl, rfl, rfl⟩


set_option maxRecDepth 100000 in
/-- A closed numerical interface for the complete nonempty call10 execution.
The physical page difference is exactly the growth term used by the trace. -/
theorem nonempty_call_cost (input : List UInt8) (hinput : input ≠ [])
    (hfit : InputFits input.length) :
    ∃ final trace amount,
      CostedSteps CostedStdIO.work (readCallConfig input) trace final amount ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) ∧
      ReadToEndSuccess input final ∧
      (final.store.wasm.mem.read32 1053960).toNat ≤ inputFrontierBound input.length ∧
      final.store.wasm.mem.pages ≤ max 17
        (AllocatorResourceCost.requiredPages (inputFrontierBound input.length)) ∧
      amount ≤ 517 * input.length + 885 + 65536 * (final.store.wasm.mem.pages - 17) := by
  obtain ⟨final, trace, amount, execution, labels, success, frontier, pages, budget⟩ :=
    nonempty_cost input hinput hfit
  refine ⟨final, trace, amount, execution, labels, success, frontier, pages, ?_⟩
  change amount + 0 + 0 + 65536 * 17 ≤
    513 * input.length + 821 + 2 * capacityBound input.length +
      65536 * final.store.wasm.mem.pages at budget
  unfold capacityBound at budget
  omega


end Project.HexEncodeStdio.ReadToEndResourceCost
