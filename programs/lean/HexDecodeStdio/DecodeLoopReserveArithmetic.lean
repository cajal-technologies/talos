import HexDecodeStdio.DecodeLoopInvariantSteps

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem DecodeLoopInv.bump_ne_zero
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    bump ≠ 0 := by
  intro hz
  have he := h.output_end
  have hc := h.capacity_pos
  rw [hz] at he
  simp at he
  omega

theorem DecodeLoopInv.reserve_new_capacity_toNat
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    (reserveNewCapacity outLen 1 capacity).toNat = 2 * capacity.toNat := by
  have hsmall := h.capacity_small_when_full hfull
  have hshift : (capacity <<< 1).toNat = 2 * capacity.toNat := by
    simp only [UInt32.toNat_shiftLeft, UInt32.reduceToNat]
    norm_num [Nat.shiftLeft_eq]
    omega
  have hadd : (capacity + (1 : UInt32)).toNat = capacity.toNat + 1 := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    rw [Nat.mod_eq_of_lt]
    norm_num at hsmall ⊢
    omega
  have hcandidate : ¬(capacity + (1 : UInt32) > capacity <<< 1) := by
    intro hgt
    have hn := UInt32.lt_iff_toNat_lt.mp hgt
    rw [hadd, hshift] at hn
    have hc := h.capacity_min
    omega
  have height : (capacity <<< 1) > 8 := by
    apply UInt32.lt_iff_toNat_lt.mpr
    rw [hshift]
    have hc := h.capacity_min
    have h8 : (8 : UInt32).toNat = 8 := by decide
    rw [h8]
    omega
  simp only [reserveNewCapacity, reserveCandidate, reserveRequired,
    reserveDoubled, hfull]
  rw [if_neg hcandidate, if_pos height]
  exact hshift

theorem DecodeLoopInv.reserve_new_capacity_eq
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    reserveNewCapacity outLen 1 capacity = capacity <<< 1 := by
  apply UInt32.toNat_inj.mp
  rw [h.reserve_new_capacity_toNat hfull]
  simp only [UInt32.toNat_shiftLeft, UInt32.reduceToNat]
  norm_num [Nat.shiftLeft_eq]
  have hsmall := h.capacity_small_when_full hfull
  omega

theorem DecodeLoopInv.reserve_copy_length
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    reallocatorCopyLen capacity (reserveNewCapacity outLen 1 capacity) =
      capacity := by
  simp only [reallocatorCopyLen]
  rw [if_neg]
  intro hlt
  have hn := UInt32.lt_iff_toNat_lt.mp hlt
  rw [h.reserve_new_capacity_toNat hfull] at hn
  have hc := h.capacity_pos
  omega

theorem DecodeLoopInv.reserve_new_capacity_nonnegative
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    ¬(reserveNewCapacity outLen 1 capacity).toInt32 <
      (0 : UInt32).toInt32 := by
  apply UInt32.toInt32_not_negative_of_small
  rw [h.reserve_new_capacity_toNat hfull]
  have hs := h.capacity_small_when_full hfull
  omega

theorem DecodeLoopInv.reserve_allocator_ptr
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    allocatorPtr bump 1 = bump :=
  allocatorPtr_one_eq bump h.bump_ne_zero

theorem DecodeLoopInv.reserve_finish_toNat
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat =
      bump.toNat + 2 * capacity.toNat := by
  rw [allocatorFinish_one_eq_comm _ _ h.bump_ne_zero]
  simp only [UInt32.toNat_add]
  rw [h.reserve_new_capacity_toNat hfull, Nat.mod_eq_of_lt]
  have hb := h.bump_signed
  have hs := h.capacity_small_when_full hfull
  norm_num at hb hs ⊢
  omega

theorem DecodeLoopInv.reserve_finish_ceiling_noWrap
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    65535 +
        (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat <
      2 ^ 32 := by
  rw [h.reserve_finish_toNat hfull]
  have hb := h.bump_signed
  have hs := h.capacity_allocator_small_when_full hfull
  omega

theorem DecodeLoopInv.reserve_requiredPages_toNat
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    (allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump).toNat =
      (65535 +
        (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat) /
        65536 := by
  have hadd :
      ((65535 : UInt32) +
          allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat =
        65535 +
          (allocatorFinish
            (reserveNewCapacity outLen 1 capacity) 1 bump).toNat := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    rw [Nat.mod_eq_of_lt (h.reserve_finish_ceiling_noWrap hfull)]
  rw [allocatorRequiredPages, UInt32.toNat_shiftRight, hadd]
  change (65535 +
      (allocatorFinish
        (reserveNewCapacity outLen 1 capacity) 1 bump).toNat) >>> 16 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem DecodeLoopInv.reserve_finish_le_pages_of_required_le
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (hrequired :
      allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump ≤
        UInt32.ofNat store.wasm.mem.pages) :
    (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat ≤
      store.wasm.mem.pages * 65536 := by
  apply ceil_pages_bound
  rw [← h.reserve_requiredPages_toNat hfull]
  have hn := UInt32.le_iff_toNat_le.mp hrequired
  rw [UInt32.toNat_ofNat_of_lt' (show store.wasm.mem.pages < UInt32.size by
    simpa only [UInt32.size] using lt_of_le_of_lt h.pages_upper (by omega))] at hn
  exact hn

theorem DecodeLoopInv.reserve_destination_bound
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (hrequired :
      allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump ≤
        UInt32.ofNat store.wasm.mem.pages) :
    (allocatorPtr bump 1).toNat +
        (reallocatorCopyLen capacity
          (reserveNewCapacity outLen 1 capacity)).toNat ≤
      store.wasm.mem.pages * 65536 := by
  rw [h.reserve_allocator_ptr, h.reserve_copy_length hfull]
  have hfinish := h.reserve_finish_le_pages_of_required_le hfull hrequired
  rw [h.reserve_finish_toNat hfull] at hfinish
  omega

theorem DecodeLoopInv.reserve_grown_pages_cover_required
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages)) :
    (allocatorRequiredPages
      (reserveNewCapacity outLen 1 capacity) 1 bump).toNat ≤ memory.pages := by
  let required :=
    allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump
  have hpagesSize : store.wasm.mem.pages < UInt32.size := by
    simpa only [UInt32.size] using lt_of_le_of_lt h.pages_upper (by omega)
  have hpagesNat : (UInt32.ofNat store.wasm.mem.pages).toNat =
      store.wasm.mem.pages := UInt32.toNat_ofNat_of_lt' hpagesSize
  have hrequiredSmall : required.toNat < 65536 := by
    rw [show required.toNat =
      (65535 +
        (allocatorFinish
          (reserveNewCapacity outLen 1 capacity) 1 bump).toNat) / 65536 from
      h.reserve_requiredPages_toNat hfull]
    have hn := h.reserve_finish_ceiling_noWrap hfull
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

theorem DecodeLoopInv.reserve_grown_copy_bounds
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity)
    (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages)) :
    ptr.toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity outLen 1 capacity)).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr bump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity outLen 1 capacity)).toNat ≤
          memory.pages * 65536 := by
  have hmono := (mem_grow_some_facts store.wasm.mem memory
    (allocatorRequiredPages (reserveNewCapacity outLen 1 capacity) 1 bump -
      UInt32.ofNat store.wasm.mem.pages)
    (store.wasm.memoryCap store.runtime.currentModule 0) previousPages hgrow).2
  have hcover := h.reserve_grown_pages_cover_required hfull memory
    previousPages hgrow
  constructor
  · rw [h.reserve_copy_length hfull]
    have hsource : ptr.toNat + capacity.toNat ≤
        store.wasm.mem.pages * 65536 := by
      rw [h.output_end]
      exact h.output_bound
    exact le_trans hsource (Nat.mul_le_mul_right 65536 (by omega))
  · rw [h.reserve_allocator_ptr, h.reserve_copy_length hfull]
    have hfinish := h.reserve_finish_toNat hfull
    have hceil :
        (allocatorFinish (reserveNewCapacity outLen 1 capacity) 1 bump).toNat ≤
          (allocatorRequiredPages
            (reserveNewCapacity outLen 1 capacity) 1 bump).toNat * 65536 := by
      apply ceil_pages_bound
      rw [← h.reserve_requiredPages_toNat hfull]
    rw [hfinish] at hceil
    exact le_trans (by omega) (Nat.mul_le_mul_right 65536 hcover)

end Submission.HexDecodeStdio
