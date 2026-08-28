import HexEncodeStdio.ReadToEndInvariant

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem UInt32.toNat_lt_signed_limit_of_not_negative (x : UInt32)
    (h : ¬x.toInt32 < (0 : UInt32).toInt32) :
    x.toNat < 2 ^ 31 := by
  have hn : ¬x.toInt32.toInt < 0 := by
    simpa [Int32.lt_iff_toInt_lt] using h
  simp only [Int32.toInt, UInt32.toBitVec_toInt32,
    BitVec.toInt_eq_toNat_cond, UInt32.toNat_toBitVec] at hn
  have hx := UInt32.toNat_lt_size x
  norm_num at hx
  split at hn
  · omega
  · omega

theorem ReadToEndInv.requiredPages_toNat
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishSmall :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat <
        2 ^ 31) :
    (allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump).toNat =
      (65535 +
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat) /
        65536 := by
  have hadd :
      ((65535 : UInt32) +
          allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat =
        65535 +
          (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    rw [Nat.mod_eq_of_lt]
    norm_num at hfinishSmall ⊢
    omega
  rw [allocatorRequiredPages, UInt32.toNat_shiftRight, hadd]
  change (65535 +
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat) >>> 16 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem ceil_pages_bound {finish pages : Nat}
    (h : (65535 + finish) / 65536 ≤ pages) :
    finish ≤ pages * 65536 := by
  omega

theorem ReadToEndInv.finish_le_pages_of_required_le
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishSmall :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat <
        2 ^ 31)
    (hrequired :
      allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump ≤
        UInt32.ofNat store.wasm.mem.pages) :
    (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
      store.wasm.mem.pages * 65536 := by
  apply ceil_pages_bound
  rw [← h.requiredPages_toNat hfinishSmall]
  have hn := UInt32.le_iff_toNat_le.mp hrequired
  rw [UInt32.toNat_ofNat_of_lt' (show store.wasm.mem.pages < UInt32.size by
    simpa only [UInt32.size] using lt_of_le_of_lt h.pages_upper (by omega))] at hn
  exact hn

theorem ReadToEndInv.destination_bound
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishSmall :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat <
        2 ^ 31)
    (hrequired :
      allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump ≤
        UInt32.ofNat store.wasm.mem.pages) :
    (allocatorPtr bump 1).toNat +
        (reallocatorCopyLen capacity
          (readToEndNewCapacity capacity)).toNat ≤
      store.wasm.mem.pages * 65536 := by
  rw [h.allocator_ptr, h.copy_length]
  have hcap := readToEndNewCapacity_gt capacity h.capacity_small
  have hfinish := h.finish_le_pages_of_required_le hfinishSmall hrequired
  rw [h.finish_toNat] at hfinish
  omega

theorem ReadToEndInv.grown_pages_cover_required
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishSmall :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat <
        2 ^ 31)
    (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages)) :
    (allocatorRequiredPages
        (readToEndNewCapacity capacity) 1 bump).toNat ≤ memory.pages := by
  let required :=
    allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump
  have hpagesSize : store.wasm.mem.pages < UInt32.size := by
    simpa only [UInt32.size] using lt_of_le_of_lt h.pages_upper (by omega)
  have hpagesNat : (UInt32.ofNat store.wasm.mem.pages).toNat =
      store.wasm.mem.pages := UInt32.toNat_ofNat_of_lt' hpagesSize
  have hrequiredSmall : required.toNat < 65536 := by
    rw [show required.toNat =
      (65535 +
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat) /
          65536 from h.requiredPages_toNat hfinishSmall]
    omega
  have hfacts := mem_grow_some_facts store.wasm.mem memory
    (required - UInt32.ofNat store.wasm.mem.pages)
    (store.wasm.memoryCap store.runtime.currentModule 0) previousPages hgrow
  have hmemoryCap := Mem.grow_success_pages_le store.wasm.mem memory
    (required - UInt32.ofNat store.wasm.mem.pages)
    (store.wasm.memoryCap store.runtime.currentModule 0) previousPages hgrow
  rw [h.memory_cap] at hmemoryCap
  change required.toNat ≤ memory.pages
  by_cases hle : UInt32.ofNat store.wasm.mem.pages ≤ required
  · have hdelta :
        (required - UInt32.ofNat store.wasm.mem.pages).toNat =
          required.toNat - store.wasm.mem.pages := by
      rw [UInt32.toNat_sub_of_le required
        (UInt32.ofNat store.wasm.mem.pages) hle, hpagesNat]
    have hleNat := UInt32.le_iff_toNat_le.mp hle
    rw [hpagesNat] at hleNat
    have hmemory := hfacts.2
    change memory.pages = store.wasm.mem.pages +
      (required - UInt32.ofNat store.wasm.mem.pages).toNat at hmemory
    rw [hdelta] at hmemory
    omega
  · have hltNat : required.toNat < store.wasm.mem.pages := by
      by_contra hn
      apply hle
      apply UInt32.le_iff_toNat_le.mpr
      rw [hpagesNat]
      omega
    have hdelta :
        (required - UInt32.ofNat store.wasm.mem.pages).toNat =
          2 ^ 32 - store.wasm.mem.pages + required.toNat := by
      rw [UInt32.toNat_sub, hpagesNat, Nat.mod_eq_of_lt]
      norm_num
      omega
    have hmemory := hfacts.2
    change memory.pages = store.wasm.mem.pages +
      (required - UInt32.ofNat store.wasm.mem.pages).toNat at hmemory
    rw [hdelta] at hmemory
    norm_num at hmemory
    omega

theorem ReadToEndInv.grown_copy_bounds
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishSmall :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat <
        2 ^ 31)
    (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages)) :
    data.toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr bump 1).toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
          memory.pages * 65536 := by
  have hmono := (mem_grow_some_facts store.wasm.mem memory
    (allocatorRequiredPages (readToEndNewCapacity capacity) 1 bump -
      UInt32.ofNat store.wasm.mem.pages)
    (store.wasm.memoryCap store.runtime.currentModule 0) previousPages hgrow).2
  have hcover := h.grown_pages_cover_required hfinishSmall memory
    previousPages hgrow
  constructor
  · rw [h.copy_length]
    exact le_trans h.data_bound (Nat.mul_le_mul_right 65536 (by omega))
  · rw [h.allocator_ptr, h.copy_length]
    have hfinish := h.finish_toNat
    have hcapacity := readToEndNewCapacity_gt capacity h.capacity_small
    have hceil :
        (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
          (allocatorRequiredPages
            (readToEndNewCapacity capacity) 1 bump).toNat * 65536 := by
      apply ceil_pages_bound
      rw [← h.requiredPages_toNat hfinishSmall]
    rw [hfinish] at hceil
    exact le_trans (by omega) (Nat.mul_le_mul_right 65536 hcover)

theorem ReadToEndInv.newCapacity_le_old_bump
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (readToEndNewCapacity capacity).toNat + 32 ≤ bump.toNat := by
  have hnew := readToEndNewCapacity_le capacity h.capacity_small
  have hhead := h.capacity_headroom
  have hdata := h.data_lower
  have hsum := h.data_capacity_bump
  rw [readToEndNewCapacity_toNat capacity h.capacity_small]
  by_cases hc : 32 ≤ capacity.toNat
  · rw [max_eq_right (by omega)]
    omega
  · rw [max_eq_left (by omega)]
    omega

theorem ByteGrowSuccess.finish_bound
    {input consumed remaining : List UInt8}
    {store final : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishSmall :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat <
        2 ^ 31)
    (h : ByteGrowSuccess store capacity data
      (readToEndNewCapacity capacity) bump final) :
    (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
      final.wasm.mem.pages * 65536 := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative =>
      exfalso
      have := hinv.capacity_pos
      simp [hzero] at this
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative =>
      exfalso
      have := hinv.capacity_pos
      simp [hzero] at this
  | reallocNoGrow hnonzero hfit =>
      simpa [reallocatorResultStore_pages] using
        hinv.finish_le_pages_of_required_le hfinishSmall hfit
  | reallocGrow hnonzero memory previousPages hgrow =>
      have hcover := hinv.grown_pages_cover_required hfinishSmall memory
        previousPages hgrow
      have hceil :
          (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
            (allocatorRequiredPages
              (readToEndNewCapacity capacity) 1 bump).toNat * 65536 := by
        apply ceil_pages_bound
        rw [← hinv.requiredPages_toNat hfinishSmall]
      simpa [reallocatorResultStore_pages, allocatorGrownStore] using
        le_trans hceil (Nat.mul_le_mul_right 65536 hcover)

theorem Mem.readBytes_prefix (mem : Mem) (address small large : Nat)
    (h : small ≤ large) :
    mem.readBytes address small = (mem.readBytes address large).take small := by
  apply List.ext_getElem
  · simp [Mem.readBytes, h]
  · intro i hleft hright
    have hi : i < small := by simpa [Mem.readBytes] using hleft
    simp [Mem.readBytes, hi, show i < large by omega]

def readToEndGrownStore (allocStore : MachineStore Universal.State)
    (capacity bump : UInt32) : MachineStore Universal.State :=
  readToEndGrowFinishedStore
    (growResultOkStore allocStore (readToEndStack + 16) bump
      (readToEndNewCapacity capacity))
    readToEndStack bump (readToEndNewCapacity capacity)

theorem ByteGrowSuccess.preserves_read_to_end_length
    {input consumed remaining : List UInt8}
    {store allocStore : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (h : ByteGrowSuccess store capacity data
      (readToEndNewCapacity capacity) bump allocStore) :
    allocStore.wasm.mem.read32 (readToEndStack + 12) = length := by
  have hcapacityNe : capacity ≠ 0 := by
    intro hz
    have := hinv.capacity_pos
    simp [hz] at this
  have hbefore : (readToEndStack + 12).toNat + 4 ≤ bump.toNat := by
    exact le_trans (by decide) (le_trans hinv.data_lower (by
      have := hinv.data_capacity_bump
      have hc := hinv.capacity_pos
      omega))
  have hbumpDisjoint : (readToEndStack + 12).toNat + 4 ≤ 1053960 := by
    decide
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative => contradiction
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative => contradiction
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore, hinv.allocator_ptr,
        hinv.copy_length, hcapacityNe, hinv.bump_ne_zero, or_false, if_false]
      rw [Mem.read32_copy_before _ _ _ _ _ hbefore]
      exact (Mem.read32_write32_disjoint _ 1053960
        (readToEndStack + 12) _ (Or.inl hbumpDisjoint)).trans hinv.length_eq
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore, hinv.allocator_ptr,
        hinv.copy_length, hcapacityNe, hinv.bump_ne_zero, or_false, if_false]
      rw [Mem.read32_copy_before _ _ _ _ _ hbefore]
      simp only [allocatorBumpStore, allocatorGrownStore]
      rw [Mem.read32_write32_disjoint _ 1053960
        (readToEndStack + 12) _ (Or.inl hbumpDisjoint)]
      exact (Mem.grow_success_read32_eq _ _ _ _ _ hgrow _).trans
        hinv.length_eq

theorem ByteGrowSuccess.grown_prefix
    {input consumed remaining : List UInt8}
    {store allocStore : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (h : ByteGrowSuccess store capacity data
      (readToEndNewCapacity capacity) bump allocStore) :
    (readToEndGrownStore allocStore capacity bump).wasm.mem.readBytes
        bump.toNat consumed.length = consumed := by
  have hcapacityNe : capacity ≠ 0 := by
    intro hz
    have := hinv.capacity_pos
    simp [hz] at this
  have hcopy := h.realloc_preserves_bytes hcapacityNe
    (by simpa [hinv.allocator_ptr] using hinv.bump_ne_zero)
    hinv.copy_length
    (by rw [hinv.data_capacity_bump]; have := hinv.bump_signed; norm_num at *; omega)
    (by
      rw [hinv.allocator_ptr]
      have hb := hinv.bump_signed
      have hc := hinv.newCapacity_le_bump
      have hg := readToEndNewCapacity_gt capacity hinv.capacity_small
      norm_num at *
      omega)
    (Or.inr (by exact le_trans (by decide) hinv.data_lower))
  rw [hinv.allocator_ptr] at hcopy
  have hprefix := congrArg (List.take consumed.length) hcopy
  rw [← Mem.readBytes_prefix allocStore.wasm.mem bump.toNat consumed.length
      capacity.toNat (by rw [← hinv.length_nat]; exact hinv.length_le_capacity),
    ← Mem.readBytes_prefix store.wasm.mem data.toNat consumed.length
      capacity.toNat (by rw [← hinv.length_nat]; exact hinv.length_le_capacity),
    hinv.bytes_eq] at hprefix
  have hbumpLower : 1054001 ≤ bump.toNat := by
    have hdataLower := hinv.data_lower
    have hdataBump := hinv.data_capacity_bump
    have hcap := hinv.capacity_pos
    omega
  simp only [readToEndGrownStore, readToEndGrowFinishedStore,
    growResultOkStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  · exact hprefix
  all_goals right
  all_goals exact le_trans (by decide) hbumpLower

theorem ByteGrowSuccess.grown_invariant
    {input consumed remaining : List UInt8}
    {store allocStore : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hfinishNonnegative : ¬
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toInt32 <
        (0 : UInt32).toInt32)
    (h : ByteGrowSuccess store capacity data
      (readToEndNewCapacity capacity) bump allocStore) :
    ReadToEndInv input consumed remaining
      (readToEndGrownStore allocStore capacity bump)
      (readToEndNewCapacity capacity) bump length
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump) := by
  have hfinishSmall :=
    UInt32.toNat_lt_signed_limit_of_not_negative _ hfinishNonnegative
  have hpagesMono := h.pages_mono
  have hpagesCap := h.pages_le_cap hinv.memory_cap hinv.pages_upper
  have hruntime := h.runtime_eq
  have hhost := h.host_eq
  have hglobal := h.globalAt_eq 0
  have hbumpRead := h.read_bump (by
    rw [hinv.allocator_ptr]
    exact le_trans (by decide) (le_trans hinv.data_lower (by
      have := hinv.data_capacity_bump
      omega)))
  have hlengthRead := h.preserves_read_to_end_length hinv
  refine
    { split := hinv.split
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
      bytes_eq := h.grown_prefix hinv
      length_nat := hinv.length_nat
      length_le_capacity := ?_
      capacity_pos := ?_
      capacity_min := ?_
      data_lower := ?_
      data_capacity_bump := ?_
      capacity_headroom := ?_
      bump_signed := hfinishSmall
      data_bound := ?_ }
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, hhost] using hinv.input_eq
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, hhost] using hinv.output_eq
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, hhost] using hinv.oom_eq
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, hruntime] using hinv.runtime_entry
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, hruntime] using hinv.runtime_module
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, hruntime] using hinv.runtime_host
  · change allocStore.wasm.memoryCap allocStore.runtime.currentModule 0 = 65536
    rw [hruntime, h.memoryCap_eq]
    exact hinv.memory_cap
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore] using le_trans hinv.pages_lower hpagesMono
  · simpa [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore] using hpagesCap
  · change globalAt? allocStore 0 = some (.i32 readToEndStack)
    rw [hglobal]
    exact hinv.global_eq
  · simp only [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore]
    exact Mem.read32_write32_same _ _ _
  · simp only [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore]
    rw [Mem.read32_write32_disjoint]
    · exact Mem.read32_write32_same _ _ _
    · decide
  · simp only [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint]
    · exact hlengthRead
    all_goals decide
  · simp only [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint]
    · exact hbumpRead
    all_goals decide
  · have htable := h.preserves_bytes_before 1048576 16 (by decide) (by
      rw [hinv.allocator_ptr]
      have hdataBump : data.toNat ≤ bump.toNat := by
        rw [← hinv.data_capacity_bump]
        omega
      exact le_trans (by decide) (le_trans hinv.data_lower hdataBump))
    simp only [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore]
    rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
      Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
      Mem.readBytes_write32_disjoint]
    · exact htable.trans hinv.table_eq
    all_goals right
    all_goals decide
  · have hg := readToEndNewCapacity_gt capacity hinv.capacity_small
    exact le_trans hinv.length_le_capacity (Nat.le_of_lt hg)
  · exact Nat.zero_lt_of_lt
      (readToEndNewCapacity_gt capacity hinv.capacity_small)
  · exact le_trans hinv.capacity_min
      (Nat.le_of_lt (readToEndNewCapacity_gt capacity hinv.capacity_small))
  · exact le_trans hinv.data_lower (by
      rw [← hinv.data_capacity_bump]
      omega)
  · exact hinv.finish_toNat.symm
  · rw [hinv.finish_toNat]
    have := hinv.newCapacity_le_old_bump
    omega
  · simpa only [readToEndGrownStore, readToEndGrowFinishedStore,
      growResultOkStore, Mem.write32_pages, hinv.finish_toNat] using
        h.finish_bound hinv hfinishSmall

end Project.HexEncodeStdio
