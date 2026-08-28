import HexEncodeStdio.ReadToEndRecursive
import HexEncodeStdio.ReadToEndTransition

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem read_to_end_after_read_recursive
    (input consumed remaining : List UInt8)
    (store readStore : MachineStore Universal.State)
    (capacity data length bump chunk filled target count : UInt32)
    (bytes : List UInt8)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
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
      ReadToEndInv input consumed' remaining' store' capacity' data' length' bump' →
      length' ≠ 0 →
      0 < chunk'.toNat →
      filled'.toNat ≤
        (readToEndTarget chunk' capacity' length').toNat →
      ReachesOrOOM
        (encodeReadContinuedConfig store' chunk' capacity' data' length'
          filled' previousCount previousTarget previousBase previousSpare)
        (ReadToEndSuccess input)) :
    ReachesOrOOM
      (readToEndAfterReadSuccessConfig readStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
        capacity data length filled target count)
      (ReadToEndSuccess input) := by
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
      simpa [hbytes, htarget] using hle
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
    simpa [hbytes] using List.length_take_le target.toNat remaining
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
    have hreturn := read_to_end_after_read_eof readStore [] encodeLocals []
      (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
      capacity data length filled target count hcountZero hlengthBound
    apply ReachesOrOOM.prependReaches hreturn
    apply read_to_end_return_success input readStore chunk capacity data length
      filled target count bump
    rw [hremainingNil, hempty] at hnewInv
    simpa [hconsumed] using hnewInv
  · have hcountNe : count ≠ 0 := by
      intro hz
      have hzNat := congrArg UInt32.toNat hz
      rw [hcountNat] at hzNat
      exact hempty (List.eq_nil_of_length_eq_zero (by simpa using hzNat))
    have hdecrease : (remaining.drop bytes.length).length < remaining.length := by
      rw [List.length_drop]
      have hpos : 0 < bytes.length := List.length_pos_iff.mpr hempty
      have hle : bytes.length ≤ remaining.length := by
        simpa [hbytes] using List.length_take_le target.toNat remaining
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
    by_cases hspareLt : capacity - length < chunk
    · have hreach := read_to_end_after_read_spare_lt readStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
        capacity data length filled target count hcountNe hspareLt hlengthBound
      apply ReachesOrOOM.prependReaches hreach
      have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length) updated
        capacity data (length + count) bump chunk (target - count)
        count target (length + data) (capacity - length) hdecrease
        (by simpa [updated, hcount] using hafter') hnextLengthNe hchunk hnextFilled
      simpa only [encodeReadContinuedConfig, hupdated] using hsuffix
    · by_cases hpartial : target ≠ count
      · have hreach := read_to_end_after_read_partial readStore [] encodeLocals []
          (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
          capacity data length filled target count hcountNe hspareLt hpartial
          hlengthBound
        apply ReachesOrOOM.prependReaches hreach
        have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length) updated
          capacity data (length + count) bump chunk (target - count)
          count target (length + data) (capacity - length) hdecrease
          (by simpa [updated, hcount] using hafter') hnextLengthNe hchunk hnextFilled
        simpa only [encodeReadContinuedConfig, hupdated] using hsuffix
      · have hfull : target = count := not_ne_iff.mp hpartial
        by_cases hnegative : chunk.toInt32 < (0 : UInt32).toInt32
        · have hreach := read_to_end_after_read_full_saturate readStore []
            encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
            readToEndStack chunk capacity data length filled target count
            hcountNe hspareLt hfull hnegative hlengthBound
          apply ReachesOrOOM.prependReaches hreach
          have hfilledZero : target - count = 0 := by
            rw [hfull]
            simp
          have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length)
            updated capacity data (length + count) bump 4294967295 0 1 target
            (length + data) (capacity - length) hdecrease
            (by simpa [updated, hcount] using hafter') hnextLengthNe
            (by decide) (by simp)
          simpa only [encodeReadContinuedConfig, hupdated, hfilledZero] using hsuffix
        · have hreach := read_to_end_after_read_full_double readStore []
            encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
            readToEndStack chunk capacity data length filled target count
            hcountNe hspareLt hfull hnegative hlengthBound
          apply ReachesOrOOM.prependReaches hreach
          have hfilledZero : target - count = 0 := by
            rw [hfull]
            simp
          have hsuffix := hrecurse (consumed ++ bytes) (remaining.drop bytes.length)
            updated capacity data (length + count) bump (chunk <<< 1) 0 0
            target (length + data) (capacity - length) hdecrease
            (by simpa [updated, hcount] using hafter') hnextLengthNe
            (shiftLeft_one_pos chunk hchunk hnegative) (by simp)
          simpa only [encodeReadContinuedConfig, hupdated, hfilledZero] using hsuffix

set_option maxHeartbeats 800000 in
theorem read_to_end_continued_direct_outcome
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk filled previousTarget previousBase
      previousSpare : UInt32)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat)
    (hspare : length ≠ capacity)
    (hfilled : filled.toNat ≤
      (readToEndTarget chunk capacity length).toNat)
    (hrecurse : ∀ (consumed' remaining' : List UInt8)
      (store' : MachineStore Universal.State)
      (capacity' data' length' bump' chunk' filled'
        previousCount' previousTarget' previousBase' previousSpare' : UInt32),
      remaining'.length < remaining.length →
      ReadToEndInv input consumed' remaining' store' capacity' data' length' bump' →
      length' ≠ 0 →
      0 < chunk'.toNat →
      filled'.toNat ≤
        (readToEndTarget chunk' capacity' length').toNat →
      ReachesOrOOM
        (encodeReadContinuedConfig store' chunk' capacity' data' length'
          filled' previousCount' previousTarget' previousBase' previousSpare')
        (ReadToEndSuccess input)) :
    ReachesOrOOM
      (readToEndContinuedDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack
        chunk capacity data length filled previousTarget previousBase previousSpare)
      (ReadToEndSuccess input) := by
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
    have hdirect := read_to_end_continued_direct_read_no_fill store []
      encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
      readToEndStack chunk capacity data length filled target previousTarget
      previousBase previousSpare bytes rfl (by simpa [remainCount] using
        hremainZero) hinv.runtime_module hinv.runtime_host
      (by simp [bytes, hinv.input_eq]) hbounds.2.1 hbounds.2.2
    have hafterAdapter := read_to_end_continued_after_adapter_success readStore
      [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
      readToEndStack chunk capacity data length filled target 0 count
      (readAdapterResultStore_read_tag store (readToEndStack + 16)
        (length + data) bytes (by decide))
      (readAdapterResultStore_read_count store (readToEndStack + 16)
        (length + data) bytes)
      hcountLe (htagBound readStore (by rfl))
      (hcountBound readStore (by rfl))
    apply ReachesOrOOM.prependReaches (hdirect.trans hafterAdapter)
    apply read_to_end_after_read_recursive input consumed remaining store
      readStore capacity data length bump chunk filled target count bytes hinv
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
    have hdirect := read_to_end_continued_direct_read store [] encodeLocals []
      (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
      capacity data length filled target remainCount previousTarget previousBase
      previousSpare bytes rfl rfl hremainZero hinv.runtime_module
      hinv.runtime_host (by simp [bytes, hinv.input_eq]) hbounds.1 hbounds.2.1
      hbounds.2.2
    have hafterAdapter := read_to_end_continued_after_adapter_success readStore
      [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
      readToEndStack chunk capacity data length filled target remainCount count
      (readAdapterResultStore_read_tag filledStore (readToEndStack + 16)
        (length + data) bytes (by decide))
      (readAdapterResultStore_read_count filledStore (readToEndStack + 16)
        (length + data) bytes)
      hcountLe (htagBound readStore (by rfl))
      (hcountBound readStore (by rfl))
    apply ReachesOrOOM.prependReaches (hdirect.trans hafterAdapter)
    apply read_to_end_after_read_recursive input consumed remaining store
      readStore capacity data length bump chunk filled target count bytes hinv
      hchunk hspare rfl (by simpa [target] using hfilled) rfl rfl
    · rfl
    · exact hrecurse

set_option maxHeartbeats 800000 in
theorem read_to_end_grown_direct_outcome
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk previousTarget previousBase scratch9
      status : UInt32)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat)
    (hspare : length ≠ capacity)
    (hstatus : (status &&& 4294967040) ||| 4 = 4)
    (hrecurse : ∀ (consumed' remaining' : List UInt8)
      (store' : MachineStore Universal.State)
      (capacity' data' length' bump' chunk' filled'
        previousCount' previousTarget' previousBase' previousSpare' : UInt32),
      remaining'.length < remaining.length →
      ReadToEndInv input consumed' remaining' store' capacity' data' length' bump' →
      length' ≠ 0 →
      0 < chunk'.toNat →
      filled'.toNat ≤
        (readToEndTarget chunk' capacity' length').toNat →
      ReachesOrOOM
        (encodeReadContinuedConfig store' chunk' capacity' data' length'
          filled' previousCount' previousTarget' previousBase' previousSpare')
        (ReadToEndSuccess input)) :
    ReachesOrOOM
      (readToEndGrownDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack
        chunk capacity data length 0 previousTarget previousBase scratch9 status)
      (ReadToEndSuccess input) := by
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
  have hdirect := read_to_end_grown_direct_read store [] encodeLocals []
    (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
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
  have hafterAdapter := read_to_end_grown_after_adapter_success readStore []
    encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
    readToEndStack chunk capacity data length 0 target target count previousBase
    scratch9 status hstatus
    (readAdapterResultStore_read_tag filledStore (readToEndStack + 16)
      (length + data) bytes (by decide))
    (readAdapterResultStore_read_count filledStore (readToEndStack + 16)
      (length + data) bytes)
    hcountLe htagBound hcountBound
  have hcombined := hdirect.trans (by
    simpa [readStore, filledStore] using hafterAdapter)
  apply ReachesOrOOM.prependReaches hcombined
  apply read_to_end_after_read_recursive input consumed remaining store
    readStore capacity data length bump chunk 0 target count bytes hinv hchunk
    hspare rfl (by simp) rfl rfl
  · simp [readStore, filledStore]
  · exact hrecurse

set_option maxHeartbeats 1000000 in
theorem read_to_end_continued_outcome
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk filled previousCount previousTarget
      previousBase previousSpare : UInt32)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hlengthNe : length ≠ 0)
    (hchunk : 0 < chunk.toNat)
    (hfilled : filled.toNat ≤
      (readToEndTarget chunk capacity length).toNat) :
    ReachesOrOOM
      (encodeReadContinuedConfig store chunk capacity data length filled
        previousCount previousTarget previousBase previousSpare)
      (ReadToEndSuccess input) := by
  induction hmeasure : remaining.length using Nat.strong_induction_on
      generalizing consumed remaining store capacity data length bump chunk
        filled previousCount previousTarget previousBase previousSpare with
  | h n ih =>
      subst hmeasure
      have hdataBound : readToEndStack.toNat + 8 + 4 ≤
          store.wasm.mem.pages * 65536 := by
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
        have hprefix := read_to_end_continued_loop_to_grow store []
          encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
          readToEndStack chunk capacity data length 0 previousCount
          previousTarget previousBase previousSpare hlengthNe hfull hinv.data_eq
          hdataBound
        apply ReachesOrOOM.prependReaches hprefix
        by_cases hfinishNegative :
            (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toInt32 <
              (0 : UInt32).toInt32
        · exact Or.inr (read_to_end_grow_signed_oom input consumed remaining
            store [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] []
            1048564 readToEndStack chunk capacity data length 0
            previousSpare 4 bump hinv hfinishNegative)
        · have hfinishSmall :=
            UInt32.toNat_lt_signed_limit_of_not_negative _ hfinishNegative
          have hgrow := read_to_end_grow_call_outcome store [] encodeLocals []
            (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack
            chunk capacity data length 0 previousSpare 4 bump
            hinv.runtime_module hinv.runtime_host hinv.bump_eq
            (by have hp := hinv.pages_lower; omega)
            (by have hp := hinv.pages_upper; omega)
            (readToEndNewCapacity_nonnegative capacity hinv.capacity_small)
            (by simpa [hinv.allocator_ptr] using hinv.bump_ne_zero)
            (by have hp := hinv.pages_lower; change 1048540 ≤ _; omega)
            (by simpa [hinv.copy_length] using hinv.data_bound)
            (fun hrequired => hinv.destination_bound hfinishSmall hrequired)
            (fun memory previousPages hg =>
              hinv.grown_copy_bounds hfinishSmall memory previousPages hg)
          apply hgrow.bind
          intro after hafter
          rcases hafter with ⟨allocStore, halloc, rfl⟩
          let okStore := growResultOkStore allocStore (readToEndStack + 16)
            (allocatorPtr bump 1) (readToEndNewCapacity capacity)
          have hpages : 17 ≤ okStore.wasm.mem.pages := by
            change 17 ≤ allocStore.wasm.mem.pages
            exact le_trans hinv.pages_lower halloc.pages_mono
          have hafterGrow := read_to_end_after_grow_success okStore []
            encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
            readToEndStack chunk capacity data length 0 previousSpare 4 bump
            (by simpa [okStore] using (growResultOkStore_read_tag allocStore
              (readToEndStack + 16) (allocatorPtr bump 1)
              (readToEndNewCapacity capacity)))
            (by simpa [okStore, hinv.allocator_ptr] using
              (growResultOkStore_read_ptr allocStore (readToEndStack + 16)
                (allocatorPtr bump 1) (readToEndNewCapacity capacity)
                (by decide)))
            (by change 1048532 ≤ okStore.wasm.mem.pages * 65536; omega)
            (by change 1048536 ≤ okStore.wasm.mem.pages * 65536; omega)
            (by change 1048524 ≤ okStore.wasm.mem.pages * 65536; omega)
            (by change 1048520 ≤ okStore.wasm.mem.pages * 65536; omega)
          apply ReachesOrOOM.prependReaches hafterGrow
          have hgrown := halloc.grown_invariant hinv hfinishNegative
          have hlengthNewNe : length ≠ readToEndNewCapacity capacity := by
            intro heq
            have hg := readToEndNewCapacity_gt capacity hinv.capacity_small
            have hn := congrArg UInt32.toNat heq
            rw [hfull] at hn
            omega
          have hsuffix := read_to_end_grown_direct_outcome input consumed remaining
            (readToEndGrownStore allocStore capacity bump)
            (readToEndNewCapacity capacity) bump length
            (allocatorFinish (readToEndNewCapacity capacity) 1 bump) chunk
            (readToEndNewCapacity capacity) (capacity <<< 1) previousSpare 4
            hgrown hchunk hlengthNewNe (by decide) (by
            intro consumed' remaining' store' capacity' data' length' bump'
              chunk' filled' previousCount' previousTarget' previousBase'
              previousSpare' hless hinv' hlengthNe' hchunk' hfilled'
            exact ih remaining'.length hless consumed' remaining' store'
              capacity' data' length' bump' chunk' filled' previousCount'
              previousTarget' previousBase' previousSpare' hinv' hlengthNe'
              hchunk' hfilled' rfl)
          simpa [readToEndGrownStore, okStore, hinv.allocator_ptr] using hsuffix
      · have hprefix := read_to_end_continued_loop_skip_growth store []
          encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
          readToEndStack chunk capacity data length filled previousCount
          previousTarget previousBase previousSpare hlengthNe hfull hinv.data_eq
          hdataBound
        apply ReachesOrOOM.prependReaches hprefix
        apply read_to_end_continued_direct_outcome input consumed remaining store
          capacity data length bump chunk filled previousTarget previousBase
          previousSpare hinv hchunk hfull hfilled
        intro consumed' remaining' store' capacity' data' length' bump' chunk'
          filled' previousCount' previousTarget' previousBase' previousSpare'
          hless hinv' hlengthNe' hchunk' hfilled'
        exact ih remaining'.length hless consumed' remaining' store'
          capacity' data' length' bump' chunk' filled' previousCount'
          previousTarget' previousBase' previousSpare' hinv' hlengthNe'
          hchunk' hfilled' rfl

set_option maxHeartbeats 800000 in
theorem read_to_end_initial_direct_outcome
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk : UInt32)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat) (hspare : length ≠ capacity) :
    ReachesOrOOM
      (readToEndDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack
        chunk capacity data length 0)
      (ReadToEndSuccess input) := by
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
  have hdirect := read_to_end_direct_read store [] encodeLocals []
    (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
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
  have hafterAdapter := read_to_end_after_adapter_success readStore []
    encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
    readToEndStack chunk capacity data length 0 target target count
    (readAdapterResultStore_read_tag filledStore (readToEndStack + 16)
      (length + data) bytes (by decide))
    (readAdapterResultStore_read_count filledStore (readToEndStack + 16)
      (length + data) bytes)
    hcountLe htagBound hcountBound
  have hdirect' : Reaches
      (readToEndDirectConfig store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack
        chunk capacity data length 0)
      (readToEndAfterAdapterConfig readStore [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack
        chunk capacity data length 0 target target) := by
    simpa [readStore, filledStore] using hdirect
  apply ReachesOrOOM.prependReaches (hdirect'.trans hafterAdapter)
  apply read_to_end_after_read_recursive input consumed remaining store
    readStore capacity data length bump chunk 0 target count bytes hinv hchunk
    hspare rfl (by simp) rfl rfl
  · simp [readStore, filledStore]
  · intro consumed' remaining' store' capacity' data' length' bump' chunk'
      filled' previousCount' previousTarget' previousBase' previousSpare'
      hless hinv' hlengthNe' hchunk' hfilled'
    exact read_to_end_continued_outcome input consumed' remaining' store'
      capacity' data' length' bump' chunk' filled' previousCount'
      previousTarget' previousBase' previousSpare' hinv' hlengthNe' hchunk'
      hfilled'

set_option maxHeartbeats 1000000 in
theorem read_to_end_loop_outcome
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump chunk : UInt32)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hlengthNe : length ≠ 0) (hchunk : 0 < chunk.toNat) :
    ReachesOrOOM (encodeReadLoopConfig store chunk capacity data length 0)
      (ReadToEndSuccess input) := by
  have hdataBound : readToEndStack.toNat + 8 + 4 ≤
      store.wasm.mem.pages * 65536 := by
    have hp := hinv.pages_lower
    change 1048524 ≤ store.wasm.mem.pages * 65536
    omega
  by_cases hfull : length = capacity
  · have hprefix := read_to_end_loop_to_grow store [] encodeLocals []
      (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
      capacity data length 0 hlengthNe hfull hinv.data_eq hdataBound
    apply ReachesOrOOM.prependReaches hprefix
    by_cases hnegative :
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toInt32 <
          (0 : UInt32).toInt32
    · exact Or.inr (read_to_end_grow_signed_oom input consumed remaining store
        [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
        readToEndStack chunk capacity data length 0 0 0 bump hinv hnegative)
    · have hfinishSmall :=
        UInt32.toNat_lt_signed_limit_of_not_negative _ hnegative
      have hgrow := read_to_end_grow_call_outcome store [] encodeLocals []
        (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
        capacity data length 0 0 0 bump hinv.runtime_module hinv.runtime_host
        hinv.bump_eq
        (by have hp := hinv.pages_lower; omega)
        (by have hp := hinv.pages_upper; omega)
        (readToEndNewCapacity_nonnegative capacity hinv.capacity_small)
        (by simpa [hinv.allocator_ptr] using hinv.bump_ne_zero)
        (by have hp := hinv.pages_lower
            change 1048540 ≤ store.wasm.mem.pages * 65536
            omega)
        (by rw [hinv.copy_length]; exact hinv.data_bound)
        (hinv.destination_bound hfinishSmall)
        (hinv.grown_copy_bounds hfinishSmall)
      rcases hgrow with ⟨afterGrow, hreach, allocStore, hsuccess, rfl⟩ | htrap
      · let grownStore := readToEndGrownStore allocStore capacity bump
        have htag := growResultOkStore_read_tag allocStore
          (readToEndStack + 16) (allocatorPtr bump 1)
          (readToEndNewCapacity capacity)
        have hptr := growResultOkStore_read_ptr allocStore
          (readToEndStack + 16) (allocatorPtr bump 1)
          (readToEndNewCapacity capacity) (by decide)
        have hallocPages : 17 ≤ allocStore.wasm.mem.pages :=
          le_trans hinv.pages_lower hsuccess.pages_mono
        have hafterGrow := read_to_end_after_grow_success
          (growResultOkStore allocStore (readToEndStack + 16)
            (allocatorPtr bump 1) (readToEndNewCapacity capacity))
          [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564
          readToEndStack chunk capacity data length 0 0 0
          (allocatorPtr bump 1) htag hptr
          (by change 1048532 ≤ allocStore.wasm.mem.pages * 65536; omega)
          (by change 1048536 ≤ allocStore.wasm.mem.pages * 65536; omega)
          (by change 1048524 ≤ allocStore.wasm.mem.pages * 65536; omega)
          (by change 1048520 ≤ allocStore.wasm.mem.pages * 65536; omega)
        apply ReachesOrOOM.prependReaches (hreach.trans hafterGrow)
        have hgrownInv := hsuccess.grown_invariant hinv hnegative
        have hnewSpare : length ≠ readToEndNewCapacity capacity := by
          intro heq
          have hg := readToEndNewCapacity_gt capacity hinv.capacity_small
          have hn := congrArg UInt32.toNat heq
          rw [hfull] at hn
          omega
        have htail := read_to_end_grown_direct_outcome input consumed remaining
          grownStore (readToEndNewCapacity capacity) bump length
          (allocatorFinish (readToEndNewCapacity capacity) 1 bump) chunk
          (readToEndNewCapacity capacity) (capacity <<< 1) 0 0 hgrownInv hchunk
          hnewSpare (by decide) (by
            intro consumed' remaining' store' capacity' data' length' bump'
              chunk' filled' previousCount' previousTarget' previousBase'
              previousSpare' hless hinv' hlengthNe' hchunk' hfilled'
            exact read_to_end_continued_outcome input consumed' remaining' store'
              capacity' data' length' bump' chunk' filled' previousCount'
              previousTarget' previousBase' previousSpare' hinv' hlengthNe'
              hchunk' hfilled')
        have htargetZero : readToEndTarget chunk capacity length = 0 := by
          simp [readToEndTarget, hfull]
        simpa [grownStore, readToEndGrownStore, hinv.allocator_ptr,
          htargetZero] using htail
      · exact Or.inr htrap
  · have hprefix := read_to_end_loop_skip_growth store [] encodeLocals []
      (Project.HexStdio.func10.drop 9) 0 [] [] [] 1048564 readToEndStack chunk
      capacity data length 0 hlengthNe hfull hinv.data_eq hdataBound
    apply ReachesOrOOM.prependReaches hprefix
    exact read_to_end_initial_direct_outcome input consumed remaining store
      capacity data length bump chunk hinv hchunk hfull

end Project.HexEncodeStdio
