import HexDecodeStdio.ReadToEndGrowthFacts

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem ReadToEndInv.spare_toNat
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (capacity - length).toNat = capacity.toNat - length.toNat := by
  exact UInt32.toNat_sub_of_le capacity length h.length_le_capacity

theorem ReadToEndInv.target_toNat
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump chunk : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (readToEndTarget chunk capacity length).toNat =
      min chunk.toNat (capacity.toNat - length.toNat) := by
  simp only [readToEndTarget]
  split
  next hlt =>
    rw [min_eq_left]
    have hn := UInt32.lt_iff_toNat_lt.mp hlt
    rw [h.spare_toNat] at hn
    exact Nat.le_of_lt hn
  next hnlt =>
    rw [h.spare_toNat, min_eq_right]
    exact Nat.le_of_not_gt (fun hlt => hnlt
      (UInt32.lt_iff_toNat_lt.mpr (by simpa [h.spare_toNat] using hlt)))

theorem ReadToEndInv.target_le_spare
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump chunk : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (readToEndTarget chunk capacity length).toNat ≤
      capacity.toNat - length.toNat := by
  rw [h.target_toNat]
  exact Nat.min_le_right _ _

theorem ReadToEndInv.length_data_toNat
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (length + data).toNat = data.toNat + length.toNat := by
  simp only [UInt32.toNat_add]
  have hb := h.data_capacity_bump
  have hl := h.length_le_capacity
  have hs := h.bump_signed
  norm_num at hs ⊢
  omega

theorem ReadToEndInv.target_positive
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump chunk : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hchunk : 0 < chunk.toNat) (hspare : length ≠ capacity) :
    0 < (readToEndTarget chunk capacity length).toNat := by
  rw [h.target_toNat]
  apply (Nat.lt_min).2
  constructor
  · exact hchunk
  · have hle := h.length_le_capacity
    have hne : length.toNat ≠ capacity.toNat := by
      intro heq
      apply hspare
      exact UInt32.toNat_inj.mp heq
    omega

theorem Mem.read32_fill_before (m : Mem) (destination count : Nat)
    (address : UInt32) (hbefore : address.toNat + 4 ≤ destination)
    (value : UInt8) :
    (m.fill destination count value).read32 address = m.read32 address := by
  simp only [Mem.read32, Mem.fill]
  rw [if_neg, if_neg, if_neg, if_neg]
  all_goals omega

theorem Mem.read32_fill_disjoint (m : Mem) (destination count : Nat)
    (address : UInt32)
    (h : address.toNat + 4 ≤ destination ∨
      destination + count ≤ address.toNat) (value : UInt8) :
    (m.fill destination count value).read32 address = m.read32 address := by
  simp only [Mem.read32, Mem.fill]
  rw [if_neg, if_neg, if_neg, if_neg]
  all_goals rcases h with hbefore | hafter <;> omega

theorem Mem.read64_low (m : Mem) (address : UInt32) :
    (m.read64 address).toUInt32 = m.read32 address := by
  simp [Mem.read64, Mem.read32]
  bv_decide

theorem Mem.read64_high (m : Mem) (address : UInt32)
    (hnext : (address + 4).toNat = address.toNat + 4) :
    ((m.read64 address >>> 32).toUInt32) = m.read32 (address + 4) := by
  simp [Mem.read64, Mem.read32, hnext,
    show address.toNat + 4 + 1 = address.toNat + 5 by omega,
    show address.toNat + 4 + 2 = address.toNat + 6 by omega,
    show address.toNat + 4 + 3 = address.toNat + 7 by omega]
  bv_decide

theorem Mem.read32_write64_low (m : Mem) (address : UInt32) (value : UInt64) :
    (m.write64 address value).read32 address = value.toUInt32 := by
  simp [Mem.write64, Mem.read32]
  bv_decide

theorem Mem.read32_write64_high (m : Mem) (address : UInt32) (value : UInt64)
    (hnext : (address + 4).toNat = address.toNat + 4) :
    (m.write64 address value).read32 (address + 4) =
      (value >>> 32).toUInt32 := by
  simp [Mem.write64, Mem.read32, hnext,
    show address.toNat + 4 + 1 = address.toNat + 5 by omega,
    show address.toNat + 4 + 2 = address.toNat + 6 by omega,
    show address.toNat + 4 + 3 = address.toNat + 7 by omega]
  bv_decide

theorem Mem.readBytes_write64_disjoint (m : Mem) (off len : Nat)
    (address : UInt32) (value : UInt64)
    (h : off + len ≤ address.toNat ∨ address.toNat + 8 ≤ off) :
    (m.write64 address value).readBytes off len = m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
      Mem.write64]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg]
    all_goals rcases h with hafter | hbefore <;> omega

def readToEndAppliedStore (store : MachineStore Universal.State)
    (data length filled target : UInt32) (bytes : List UInt8) :
    MachineStore Universal.State :=
  readToEndLengthStore
    (readAdapterResultStore
      (readToEndFillStore store (filled + (length + data)) (target - filled))
      (readToEndStack + 16) (length + data) bytes)
    readToEndStack (UInt32.ofNat bytes.length) length

theorem ReadToEndInv.bytes_length_le_target
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump chunk : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (remaining.take (readToEndTarget chunk capacity length).toNat).length ≤
      (readToEndTarget chunk capacity length).toNat := by
  simp

theorem ReadToEndInv.next_filled_le_target
    {input consumed remaining consumed' remaining' : List UInt8}
    {store nextStore : MachineStore Universal.State}
    {capacity data length nextLength bump chunk count : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hnext : ReadToEndInv input consumed' remaining' nextStore capacity data
      nextLength bump)
    (hcount : count.toNat ≤
      (readToEndTarget chunk capacity length).toNat)
    (hnextLength : nextLength.toNat = length.toNat + count.toNat) :
    (readToEndTarget chunk capacity length - count).toNat ≤
      (readToEndTarget chunk capacity nextLength).toNat := by
  have hcountU : count ≤ readToEndTarget chunk capacity length :=
    UInt32.le_iff_toNat_le.mpr hcount
  rw [UInt32.toNat_sub_of_le _ _ hcountU, h.target_toNat,
    hnext.target_toNat, hnextLength]
  omega

theorem shiftLeft_one_pos (chunk : UInt32) (hpos : 0 < chunk.toNat)
    (hnonnegative : ¬chunk.toInt32 < (0 : UInt32).toInt32) :
    0 < (chunk <<< 1).toNat := by
  have hsmall := UInt32.toNat_lt_signed_limit_of_not_negative chunk hnonnegative
  simp only [UInt32.toNat_shiftLeft, UInt32.reduceToNat]
  norm_num [Nat.shiftLeft_eq]
  omega

theorem ReadToEndInv.direct_read_bounds
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump chunk filled : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfilled : filled.toNat ≤
      (readToEndTarget chunk capacity length).toNat) :
    let target := readToEndTarget chunk capacity length
    let bytes := remaining.take target.toNat
    (filled + (length + data)).toNat + (target - filled).toNat ≤
        store.wasm.mem.pages * 65536 ∧
      (length + data).toNat + bytes.length ≤
        store.wasm.mem.pages * 65536 ∧
      (readToEndStack + 16).toNat + 4 + 4 ≤
        store.wasm.mem.pages * 65536 := by
  dsimp only
  let target := readToEndTarget chunk capacity length
  let bytes := remaining.take target.toNat
  have htargetLe := h.target_le_spare (chunk := chunk)
  have htargetLe' : target.toNat ≤ capacity.toNat - length.toNat := by
    simpa [target] using htargetLe
  have hfilled' : filled.toNat ≤ target.toNat := by simpa [target] using hfilled
  have hlengthTarget : length.toNat + target.toNat ≤ capacity.toNat := by
    have := Nat.add_le_of_le_sub h.length_le_capacity htargetLe'
    omega
  have hlengthFilled : length.toNat + filled.toNat ≤ capacity.toNat := by
    exact le_trans (Nat.add_le_add_left hfilled' _) hlengthTarget
  have hsum : filled.toNat + (length + data).toNat < 2 ^ 32 := by
    rw [h.length_data_toNat]
    have hb32 : bump.toNat < 4294967296 :=
      lt_trans h.bump_signed (by norm_num)
    exact lt_of_le_of_lt
      (calc
        filled.toNat + (data.toNat + length.toNat) =
            data.toNat + (length.toNat + filled.toNat) := by omega
        _ ≤ data.toNat + capacity.toNat := Nat.add_le_add_left hlengthFilled _
        _ = bump.toNat := h.data_capacity_bump)
      hb32
  have hremainingNat : (target - filled).toNat =
      target.toNat - filled.toNat := by
    exact UInt32.toNat_sub_of_le target filled
      (UInt32.le_iff_toNat_le.mpr hfilled')
  have hfillEnd :
      (filled + (length + data)).toNat + (target - filled).toNat ≤
        data.toNat + capacity.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt hsum, h.length_data_toNat,
      hremainingNat]
    omega
  have hbytesLe : bytes.length ≤ target.toNat := by simp [bytes]
  have hreadEnd : (length + data).toNat + bytes.length ≤
      data.toNat + capacity.toNat := by
    rw [h.length_data_toNat]
    omega
  constructor
  · exact le_trans hfillEnd h.data_bound
  constructor
  · exact le_trans hreadEnd h.data_bound
  · have hp := h.pages_lower
    change 1048520 ≤ store.wasm.mem.pages * 65536
    omega

theorem ReadToEndInv.after_read
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump chunk filled : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfilled : filled.toNat ≤
      (readToEndTarget chunk capacity length).toNat) :
    let target := readToEndTarget chunk capacity length
    let bytes := remaining.take target.toNat
    ReadToEndInv input (consumed ++ bytes) (remaining.drop bytes.length)
      (readToEndAppliedStore store data length filled target bytes)
      capacity data (length + UInt32.ofNat bytes.length) bump := by
  dsimp only
  let target := readToEndTarget chunk capacity length
  let bytes := remaining.take target.toNat
  have hbytesLeTarget : bytes.length ≤ target.toNat := by
    simp [bytes]
  have htargetLeSpare : target.toNat ≤ capacity.toNat - length.toNat := by
    exact h.target_le_spare
  have hlengthLeCapacity : length.toNat ≤ capacity.toNat :=
    h.length_le_capacity
  have hfilledLeTarget : filled.toNat ≤ target.toNat := by
    simpa [target] using hfilled
  have hcapacitySmall : capacity.toNat < 2 ^ 31 := by
    have hb := h.bump_signed
    have hc := h.capacity_headroom
    omega
  have hbytesLeCapacity : bytes.length ≤ capacity.toNat := by
    calc
      bytes.length ≤ target.toNat := hbytesLeTarget
      _ ≤ capacity.toNat - length.toNat := htargetLeSpare
      _ ≤ capacity.toNat := Nat.sub_le _ _
  have hfilledLeCapacity : filled.toNat ≤ capacity.toNat := by
    calc
      filled.toNat ≤ target.toNat := hfilledLeTarget
      _ ≤ capacity.toNat - length.toNat := htargetLeSpare
      _ ≤ capacity.toNat := Nat.sub_le _ _
  have hlengthTarget : length.toNat + target.toNat ≤ capacity.toNat := by
    have := Nat.add_le_of_le_sub hlengthLeCapacity htargetLeSpare
    omega
  have hlengthFilled : length.toNat + filled.toNat ≤ capacity.toNat := by
    exact le_trans (Nat.add_le_add_left hfilledLeTarget _)
      hlengthTarget
  have hlengthBytes : length.toNat + bytes.length ≤ capacity.toNat := by
    exact le_trans (Nat.add_le_add_left hbytesLeTarget _)
      hlengthTarget
  have hcountSmall : bytes.length < 2 ^ 32 := by
    have hc := h.capacity_small
    omega
  have hcountNat : (UInt32.ofNat bytes.length).toNat = bytes.length := by
    exact UInt32.toNat_ofNat_of_lt' hcountSmall
  have hnewLengthNat :
      (length + UInt32.ofNat bytes.length).toNat =
        length.toNat + bytes.length := by
    have hsum : length.toNat + bytes.length < 2 ^ 32 :=
      lt_of_le_of_lt hlengthBytes (lt_trans hcapacitySmall (by norm_num))
    rw [UInt32.toNat_add, hcountNat, Nat.mod_eq_of_lt hsum]
  have hpointer : (length + data).toNat = data.toNat + consumed.length := by
    rw [h.length_data_toNat, ← h.length_nat]
  have hfillDestination :
      data.toNat + consumed.length ≤
        (filled + (length + data)).toNat := by
    have hsum : filled.toNat + (length + data).toNat < 2 ^ 32 := by
      rw [h.length_data_toNat]
      have hc := h.data_capacity_bump
      have hb32 : bump.toNat < 4294967296 :=
        lt_trans h.bump_signed (by norm_num)
      norm_num at ⊢
      exact lt_of_le_of_lt
        (calc
          filled.toNat + (data.toNat + length.toNat) =
              data.toNat + (length.toNat + filled.toNat) := by omega
          _ ≤ data.toNat + capacity.toNat := Nat.add_le_add_left hlengthFilled _
          _ = bump.toNat := hc)
        hb32
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt hsum, hpointer]
    omega
  have hremainingNat : (target - filled).toNat =
      target.toNat - filled.toNat := by
    exact UInt32.toNat_sub_of_le target filled
      (UInt32.le_iff_toNat_le.mpr (by simpa [target] using hfilled))
  have hfillEnd :
      (filled + (length + data)).toNat + (target - filled).toNat ≤
        bump.toNat := by
    have hsum : filled.toNat + (length + data).toNat < 2 ^ 32 := by
      rw [h.length_data_toNat]
      have hc := h.data_capacity_bump
      have hb32 : bump.toNat < 4294967296 :=
        lt_trans h.bump_signed (by norm_num)
      norm_num at ⊢
      exact lt_of_le_of_lt
        (calc
          filled.toNat + (data.toNat + length.toNat) =
              data.toNat + (length.toNat + filled.toNat) := by omega
          _ ≤ data.toNat + capacity.toNat := Nat.add_le_add_left hlengthFilled _
          _ = bump.toNat := hc)
        hb32
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt hsum, h.length_data_toNat,
      hremainingNat]
    calc
      filled.toNat + (data.toNat + length.toNat) +
            (target.toNat - filled.toNat) =
          data.toNat + (length.toNat + target.toNat) := by omega
      _ ≤ data.toNat + capacity.toNat := Nat.add_le_add_left hlengthTarget _
      _ = bump.toNat := h.data_capacity_bump
  let filledStore := readToEndFillStore store
    (filled + (length + data)) (target - filled)
  let readStore := readAdapterResultStore filledStore
    (readToEndStack + 16) (length + data) bytes
  have hfilledPrefix : filledStore.wasm.mem.readBytes data.toNat
      consumed.length = consumed := by
    exact (readToEndFillStore_preserves_prefix store data
      (filled + (length + data)) (target - filled) consumed.length
      hfillDestination).trans h.bytes_eq
  have hreadPrefix : readStore.wasm.mem.readBytes data.toNat
      (consumed.length + bytes.length) = consumed ++ bytes := by
    apply readAdapterResultStore_appends filledStore
      (readToEndStack + 16) data (length + data) consumed bytes
    · exact hpointer
    · exact hfilledPrefix
    · decide
    · exact le_trans (by decide) h.data_lower
  have hmetaBeforeFill (addr : UInt32)
      (ha : addr.toNat + 4 ≤ data.toNat) :
      filledStore.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
    apply Mem.read32_fill_before
    exact le_trans ha (le_trans (Nat.le_add_right _ _) hfillDestination)
  have hbufferEnd : (length + data).toNat + bytes.length ≤ bump.toNat := by
    rw [h.length_data_toNat]
    calc
      data.toNat + length.toNat + bytes.length =
          data.toNat + (length.toNat + bytes.length) := by omega
      _ ≤ data.toNat + capacity.toNat := Nat.add_le_add_left hlengthBytes _
      _ = bump.toNat := h.data_capacity_bump
  have hreadPreserves (addr : UInt32)
      (ha : addr.toNat + 4 ≤ (readToEndStack + 16).toNat)
      (hdataAddr : addr.toNat + 4 ≤ data.toNat) :
      readStore.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
    rw [readAdapterResultStore_read32_disjoint filledStore
      (readToEndStack + 16) (length + data) addr bytes]
    · exact hmetaBeforeFill addr hdataAddr
    · exact Or.inl (le_trans hdataAddr (by
        rw [h.length_data_toNat]
        omega))
    · exact Or.inl ha
    · exact Or.inl (by
        change addr.toNat + 4 ≤ (readToEndStack + 20).toNat
        exact le_trans ha (by decide))
  have hreadPreservesStatus (addr : UInt32)
      (ha : addr.toNat + 4 ≤ data.toNat)
      (htag : (readToEndStack + 16).toNat + 1 ≤ addr.toNat)
      (hcount : (readToEndStack + 20).toNat + 4 ≤ addr.toNat) :
      readStore.wasm.mem.read32 addr = store.wasm.mem.read32 addr := by
    rw [readAdapterResultStore_read32_disjoint filledStore
      (readToEndStack + 16) (length + data) addr bytes]
    · exact hmetaBeforeFill addr ha
    · exact Or.inl (le_trans ha (by rw [h.length_data_toNat]; omega))
    · exact Or.inr htag
    · exact Or.inr hcount
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
      status_capacity := ?_
      status_pointer := ?_
      status_length := ?_
      capacity_eq := ?_
      data_eq := ?_
      length_eq := ?_
      bump_eq := ?_
      bytes_eq := ?_
      length_nat := by
        rw [hnewLengthNat, h.length_nat, List.length_append]
      length_le_capacity := by
        rw [hnewLengthNat]
        exact hlengthBytes
      capacity_pos := h.capacity_pos
      capacity_min := h.capacity_min
      data_lower := h.data_lower
      data_capacity_bump := h.data_capacity_bump
      capacity_headroom := h.capacity_headroom
      bump_signed := h.bump_signed
      data_bound := ?_ }
  · have hdrop : remaining.drop bytes.length = remaining.drop target.toNat := by
      simp only [bytes, List.length_take]
      by_cases hle : target.toNat ≤ remaining.length
      · rw [Nat.min_eq_left hle]
      · have hlen : remaining.length ≤ target.toNat :=
          Nat.le_of_lt (Nat.lt_of_not_ge hle)
        rw [Nat.min_eq_right hlen, List.drop_eq_nil_of_le hlen]
        exact List.drop_eq_nil_of_le (le_refl _)
    rw [List.append_assoc, hdrop]
    change consumed ++
      (remaining.take target.toNat ++ remaining.drop target.toNat) = input
    rw [List.take_append_drop, h.split]
  · simp [readToEndAppliedStore, readToEndLengthStore,
      readAdapterResultStore, universalReadStore, readToEndFillStore,
      afterUniversalRead, h.input_eq]
  · simpa [readToEndAppliedStore, readStore, filledStore,
      readAdapterResultStore, universalReadStore, readToEndFillStore,
      readToEndLengthStore, afterUniversalRead] using h.output_eq
  · simpa [readToEndAppliedStore, readStore, filledStore,
      readAdapterResultStore, universalReadStore, readToEndFillStore,
      readToEndLengthStore, afterUniversalRead] using h.oom_eq
  · simpa [readToEndAppliedStore, readToEndLengthStore,
      readAdapterResultStore, universalReadStore, readToEndFillStore] using
      h.runtime_module
  · simpa [readToEndAppliedStore, readToEndLengthStore,
      readAdapterResultStore, universalReadStore, readToEndFillStore] using
      h.runtime_host
  · change store.wasm.memoryCap store.runtime.currentModule 0 = 65536
    exact h.memory_cap
  · change 17 ≤ store.wasm.mem.pages
    exact h.pages_lower
  · change store.wasm.mem.pages ≤ 65536
    exact h.pages_upper
  · change globalAt? store 0 = some (.i32 readToEndStack)
    exact h.global_eq
  · simp only [readToEndAppliedStore, readToEndLengthStore]
    rw [Mem.read32_write32_disjoint]
    · exact (hreadPreservesStatus decodeStatusVector
        (le_trans (by decide) h.data_lower) (by decide) (by decide)).trans
          h.status_capacity
    · decide
  · simp only [readToEndAppliedStore, readToEndLengthStore]
    rw [Mem.read32_write32_disjoint]
    · exact (hreadPreservesStatus (decodeStatusVector + 4)
        (le_trans (by decide) h.data_lower) (by decide) (by decide)).trans
          h.status_pointer
    · decide
  · simp only [readToEndAppliedStore, readToEndLengthStore]
    rw [Mem.read32_write32_disjoint]
    · exact (hreadPreservesStatus (decodeStatusVector + 8)
        (le_trans (by decide) h.data_lower) (by decide) (by decide)).trans
          h.status_length
    · decide
  · simp only [readToEndAppliedStore, readToEndLengthStore]
    rw [Mem.read32_write32_disjoint]
    · exact (hreadPreserves (readToEndStack + 4) (by decide)
        (le_trans (by decide) h.data_lower)).trans h.capacity_eq
    · decide
  · simp only [readToEndAppliedStore, readToEndLengthStore]
    rw [Mem.read32_write32_disjoint]
    · exact (hreadPreserves (readToEndStack + 8) (by decide)
        (le_trans (by decide) h.data_lower)).trans h.data_eq
    · decide
  · simp [readToEndAppliedStore, readToEndLengthStore]
  · simp only [readToEndAppliedStore, readToEndLengthStore]
    rw [Mem.read32_write32_disjoint]
    · rw [readAdapterResultStore_read32_disjoint filledStore
          (readToEndStack + 16) (length + data) 1053960 bytes]
      · exact (hmetaBeforeFill 1053960
          (le_trans (by decide) h.data_lower)).trans h.bump_eq
      · exact Or.inl (le_trans (by decide)
          (le_trans h.data_lower (by rw [h.length_data_toNat]; omega)))
      · exact Or.inr (by decide)
      · exact Or.inr (by decide)
    · decide
  · change (readToEndLengthStore readStore readToEndStack
      (UInt32.ofNat bytes.length) length).wasm.mem.readBytes data.toNat
        (consumed ++ bytes).length = consumed ++ bytes
    rw [readToEndLengthStore_preserves_bytes readStore readToEndStack
      (UInt32.ofNat bytes.length) length data (consumed ++ bytes)
      (le_trans (by decide) h.data_lower)]
    simpa using hreadPrefix
  · change data.toNat + capacity.toNat ≤ store.wasm.mem.pages * 65536
    exact h.data_bound

theorem ReadToEndInv.finished_success
    {input : List UInt8} {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input input [] store capacity data length bump) :
    let vectorWord := store.wasm.mem.read64 (readToEndStack + 4)
    let finalStore := readToEndFinishedStore store decodeInputVector
      readToEndStack decodeStack vectorWord length
    ReadToEndSuccess input (decodeAfterReadConfig finalStore) := by
  dsimp only
  let vectorWord := store.wasm.mem.read64 (readToEndStack + 4)
  let finalStore := readToEndFinishedStore store decodeInputVector
    readToEndStack decodeStack vectorWord length
  have hinputLength : input.length = length.toNat := by
    simpa using h.length_nat.symm
  have hinputSmall : input.length < 2 ^ 32 := by
    rw [hinputLength]
    have hc := h.capacity_small
    have hl := h.length_le_capacity
    omega
  have hlengthValue : length = UInt32.ofNat input.length := by
    apply UInt32.toNat_inj.mp
    rw [h.length_nat, UInt32.toNat_ofNat_of_lt' hinputSmall]
  refine ⟨finalStore, capacity, data, bump, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [finalStore, readToEndFinishedStore] using h.input_eq
  · simpa [finalStore, readToEndFinishedStore] using h.output_eq
  · simpa [finalStore, readToEndFinishedStore] using h.oom_eq
  · simpa [finalStore, readToEndFinishedStore] using h.runtime_module
  · simpa [finalStore, readToEndFinishedStore] using h.runtime_host
  · change store.wasm.memoryCap store.runtime.currentModule 0 = 65536
    exact h.memory_cap
  · change 17 ≤ store.wasm.mem.pages
    exact h.pages_lower
  · change store.wasm.mem.pages ≤ 65536
    exact h.pages_upper
  · simp only [finalStore, readToEndFinishedStore, globalAt?,
      canonicalGlobalIndex_zero]
    have hzero : 0 < store.wasm.globals.globals.length :=
      (getElem?_eq_some_iff.mp h.global_eq).1
    simpa using (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact h.status_capacity
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact h.status_pointer
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact h.status_length
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_low, Mem.read64_low]
    exact h.capacity_eq
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_high _ _ _ (by decide),
      Mem.read64_high _ _ (by decide)]
    simpa only [show readToEndStack + 4 + 4 = readToEndStack + 8 by
      bv_decide] using h.data_eq
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint]
    · rw [Mem.read32_write32_same]
      exact hlengthValue
    · decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact h.bump_eq
    all_goals decide
  · simp only [finalStore, readToEndFinishedStore]
    rw [Mem.readBytes_write64_disjoint, Mem.readBytes_write32_disjoint]
    · exact h.bytes_eq
    all_goals right
    all_goals exact le_trans (by decide) h.data_lower
  · simpa [hinputLength] using h.length_le_capacity
  · exact Or.inr h.data_capacity_bump
  · exact Or.inr h.data_lower
  · right
    have hd := h.data_lower
    have hb := h.data_capacity_bump
    omega
  · exact h.bump_signed
  · change data.toNat + capacity.toNat ≤ store.wasm.mem.pages * 65536
    exact h.data_bound

theorem read_to_end_return_success
    (input : List UInt8) (store : MachineStore Universal.State)
    (chunk capacity data length filled target count bump : UInt32)
    (hinv : ReadToEndInv input input []
      (readToEndLengthStore store readToEndStack count length)
      capacity data (length + count) bump) :
    ReachesOrOOM
      (readToEndReturnConfig store [] decodeLocals [] decodeAfterRead 0 [] [] []
        decodeInputVector readToEndStack chunk capacity data length filled
        target count)
      (ReadToEndSuccess input) := by
  let updated := readToEndLengthStore store readToEndStack count length
  let vectorWord := updated.wasm.mem.read64 (readToEndStack + 4)
  let finalStore := readToEndFinishedStore updated decodeInputVector
    readToEndStack decodeStack vectorWord (length + count)
  have hreach := read_to_end_return store [] decodeLocals [] decodeAfterRead
    0 [] [] [] decodeInputVector readToEndStack chunk capacity data length
    filled target count decodeStack vectorWord
    (by simp [readToEndLengthStore]) rfl
    (by change readToEndStack.toNat + 12 + 4 ≤
        store.wasm.mem.pages * 65536
        have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.pages_lower
        change 1048512 ≤ store.wasm.mem.pages * 65536
        omega)
    (by change readToEndStack.toNat + 4 + 8 ≤
        store.wasm.mem.pages * 65536
        have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.pages_lower
        change 1048508 ≤ store.wasm.mem.pages * 65536
        omega)
    (by change decodeInputVector.toNat + 8 + 4 ≤
        store.wasm.mem.pages * 65536
        have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.pages_lower
        change 1048576 ≤ store.wasm.mem.pages * 65536
        omega)
    (by change decodeInputVector.toNat + 8 ≤
        store.wasm.mem.pages * 65536
        have hp : 17 ≤ store.wasm.mem.pages := by
          simpa [readToEndLengthStore] using hinv.pages_lower
        change 1048572 ≤ store.wasm.mem.pages * 65536
        omega)
    (by decide)
    (by simpa [updated, hinv.global_eq])
    (by bv_decide)
  apply ReachesOrOOM.of_reaches (by
    simpa [updated, vectorWord, finalStore, decodeAfterReadConfig] using hreach)
  change ReadToEndSuccess input (decodeAfterReadConfig finalStore)
  exact hinv.finished_success

end Project.HexDecodeStdio
