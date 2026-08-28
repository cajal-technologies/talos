import HexEncodeStdio.ReadToEndOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem Mem.readBytes_fill_before (m : Mem) (off len fillOff fillLen : Nat)
    (hbefore : off + len ≤ fillOff) (value : UInt8) :
    (m.fill fillOff fillLen value).readBytes off len = m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range, Mem.fill]
    rw [if_neg]
    omega

theorem Mem.readBytes_writeBytes_append (m : Mem) (off oldLen : Nat)
    (oldBytes newBytes : List UInt8)
    (holdLen : oldBytes.length = oldLen)
    (hold : m.readBytes off oldLen = oldBytes) :
    (m.writeBytes (off + oldLen) newBytes).readBytes off
        (oldLen + newBytes.length) = oldBytes ++ newBytes := by
  apply List.ext_getElem
  · simp [Mem.readBytes, holdLen]
  · intro i hleft hright
    have hi : i < oldLen + newBytes.length := by
      simpa [Mem.readBytes] using hleft
    by_cases hprefix : i < oldLen
    · have hprefix' : i < oldBytes.length := by simpa [holdLen] using hprefix
      rw [List.getElem_append_left hprefix']
      have holdAt := congrArg (fun xs => xs[i]?) hold
      simp only [Mem.readBytes, List.getElem?_map, List.getElem?_range,
        hprefix, ↓reduceDIte, Option.map_some] at holdAt
      rw [List.getElem?_eq_getElem hprefix'] at holdAt
      simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
        Mem.writeBytes]
      rw [dif_neg (by omega)]
      exact Option.some.inj holdAt
    · have hright' : oldBytes.length ≤ i := by
        rw [holdLen]
        omega
      rw [List.getElem_append_right hright']
      simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
        Mem.writeBytes]
      rw [dif_pos (by omega)]
      congr 1
      omega

theorem Mem.readBytes_writeBytes_disjoint (m : Mem) (off len writeOff : Nat)
    (bytes : List UInt8)
    (h : off + len ≤ writeOff ∨ writeOff + bytes.length ≤ off) :
    (m.writeBytes writeOff bytes).readBytes off len = m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
      Mem.writeBytes]
    rw [dif_neg]
    rcases h with hbefore | hafter <;> omega

theorem Mem.readBytes_write8_disjoint (m : Mem) (off len : Nat)
    (addr : UInt32) (value : UInt8)
    (h : off + len ≤ addr.toNat ∨ addr.toNat + 1 ≤ off) :
    (m.write8 addr value).readBytes off len = m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
      Mem.write8]
    rw [if_neg]
    rcases h with hafter | hbefore <;> omega

theorem Mem.readBytes_write32_disjoint (m : Mem) (off len : Nat)
    (addr value : UInt32)
    (h : off + len ≤ addr.toNat ∨ addr.toNat + 4 ≤ off) :
    (m.write32 addr value).readBytes off len = m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
      Mem.write32]
    rw [if_neg, if_neg, if_neg, if_neg]
    all_goals rcases h with hafter | hbefore <;> omega

theorem Mem.readBytes_copy_before (m : Mem) (off len destination source count : Nat)
    (hbefore : off + len ≤ destination) :
    (m.copy destination source count).readBytes off len =
      m.readBytes off len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < len := by simpa [Mem.readBytes] using hleft
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range, Mem.copy]
    rw [if_neg]
    omega

theorem readToEndFillStore_preserves_prefix
    (store : MachineStore Universal.State)
    (data destination count : UInt32) (length : Nat)
    (hbefore : data.toNat + length ≤ destination.toNat) :
    (readToEndFillStore store destination count).wasm.mem.readBytes
        data.toNat length = store.wasm.mem.readBytes data.toNat length := by
  exact Mem.readBytes_fill_before _ _ _ _ _ hbefore _

theorem readAdapterResultStore_preserves_table
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8)
    (hout : (out + 4).toNat + 4 ≤ 1048576)
    (hout8 : out.toNat + 1 ≤ 1048576)
    (hpointer : 1048576 + 16 ≤ pointer.toNat) :
    (readAdapterResultStore store out pointer bytes).wasm.mem.readBytes
        1048576 16 = store.wasm.mem.readBytes 1048576 16 := by
  simp only [readAdapterResultStore, universalReadStore]
  rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inr hout)]
  rw [Mem.readBytes_write8_disjoint _ _ _ _ _ (Or.inr hout8)]
  rw [Mem.readBytes_writeBytes_disjoint _ _ _ _ _ (Or.inl hpointer)]

theorem readToEndLengthStore_preserves_table
    (store : MachineStore Universal.State) (frame count length : UInt32)
    (hframe : (frame + 12).toNat + 4 ≤ 1048576) :
    (readToEndLengthStore store frame count length).wasm.mem.readBytes
        1048576 16 = store.wasm.mem.readBytes 1048576 16 := by
  simp only [readToEndLengthStore]
  apply Mem.readBytes_write32_disjoint
  exact Or.inr hframe

theorem readAdapterResultStore_appends
    (store : MachineStore Universal.State)
    (out data pointer : UInt32) (oldBytes newBytes : List UInt8)
    (hpointer : pointer.toNat = data.toNat + oldBytes.length)
    (hold : store.wasm.mem.readBytes data.toNat oldBytes.length = oldBytes)
    (hout4 : (out + 4).toNat = out.toNat + 4)
    (hmeta : (out + 4).toNat + 4 ≤ data.toNat) :
    (readAdapterResultStore store out pointer newBytes).wasm.mem.readBytes
        data.toNat (oldBytes.length + newBytes.length) =
      oldBytes ++ newBytes := by
  simp only [readAdapterResultStore, universalReadStore]
  rw [Mem.readBytes_write32_disjoint]
  · rw [Mem.readBytes_write8_disjoint]
    · rw [hpointer]
      exact Mem.readBytes_writeBytes_append _ _ _ _ _ rfl hold
    · right
      omega
  · right
    exact hmeta

theorem readToEndLengthStore_preserves_bytes
    (store : MachineStore Universal.State)
    (frame count length data : UInt32) (bytes : List UInt8)
    (hbefore : (frame + 12).toNat + 4 ≤ data.toNat) :
    (readToEndLengthStore store frame count length).wasm.mem.readBytes
        data.toNat bytes.length = store.wasm.mem.readBytes data.toNat bytes.length := by
  exact Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inr hbefore)

theorem ByteGrowSuccess.realloc_preserves_byte
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (holdCapacity : oldCapacity ≠ 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hcopyLength : reallocatorCopyLen oldCapacity newCapacity = oldCapacity)
    (i : Nat) (hi : i < oldCapacity.toNat)
    (holdNoWrap : (oldPtr + UInt32.ofNat i).toNat = oldPtr.toNat + i)
    (hnewNoWrap : (allocatorPtr oldBump 1 + UInt32.ofNat i).toNat =
      (allocatorPtr oldBump 1).toNat + i)
    (hbumpDisjoint : oldPtr.toNat + oldCapacity.toNat ≤ 1053960 ∨
      1053960 + 4 ≤ oldPtr.toNat) :
    final.wasm.mem.read8 (allocatorPtr oldBump 1 + UInt32.ofNat i) =
      store.wasm.mem.read8 (oldPtr + UInt32.ofNat i) := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative => contradiction
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative => contradiction
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore, hptr, hcopyLength,
        holdCapacity, or_false, if_false]
      rw [Mem.copy_read8_in]
      · have hsrcIndex : oldPtr.toNat +
            ((allocatorPtr oldBump 1 + UInt32.ofNat i).toNat -
              (allocatorPtr oldBump 1).toNat) = oldPtr.toNat + i := by
          rw [hnewNoWrap]
          omega
        simp only [allocatorBumpStore, Mem.read8]
        rw [hsrcIndex]
        rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by
          change oldPtr.toNat + i < 1053960 ∨
            1053960 + 4 ≤ oldPtr.toNat + i
          rcases hbumpDisjoint with hbefore | hafter
          · omega
          · omega)]
        simp [holdNoWrap, Mem.read8]
      · rw [hnewNoWrap]
        omega
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore, hptr, hcopyLength,
        holdCapacity, or_false, if_false, allocatorGrownStore]
      rw [Mem.copy_read8_in]
      · have hsrcIndex : oldPtr.toNat +
            ((allocatorPtr oldBump 1 + UInt32.ofNat i).toNat -
              (allocatorPtr oldBump 1).toNat) = oldPtr.toNat + i := by
          rw [hnewNoWrap]
          omega
        simp only [allocatorBumpStore, Mem.read8]
        rw [hsrcIndex]
        rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by
          change oldPtr.toNat + i < 1053960 ∨
            1053960 + 4 ≤ oldPtr.toNat + i
          rcases hbumpDisjoint with hbefore | hafter
          · omega
          · omega)]
        rw [Mem.grow_success_bytes_eq store.wasm.mem memory _ _ _ hgrow]
        simp [holdNoWrap, Mem.read8]
      · rw [hnewNoWrap]
        omega

theorem ByteGrowSuccess.realloc_preserves_bytes
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (holdCapacity : oldCapacity ≠ 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hcopyLength : reallocatorCopyLen oldCapacity newCapacity = oldCapacity)
    (holdNoWrap : oldPtr.toNat + oldCapacity.toNat < UInt32.size)
    (hnewNoWrap : (allocatorPtr oldBump 1).toNat + oldCapacity.toNat <
      UInt32.size)
    (hbumpDisjoint : oldPtr.toNat + oldCapacity.toNat ≤ 1053960 ∨
      1053960 + 4 ≤ oldPtr.toNat) :
    final.wasm.mem.readBytes (allocatorPtr oldBump 1).toNat
        oldCapacity.toNat =
      store.wasm.mem.readBytes oldPtr.toNat oldCapacity.toNat := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < oldCapacity.toNat := by
      simpa [Mem.readBytes] using hleft
    have holdNoWrap' : oldPtr.toNat + oldCapacity.toNat < 4294967296 := by
      simpa only [UInt32.size] using holdNoWrap
    have hnewNoWrap' :
        (allocatorPtr oldBump 1).toNat + oldCapacity.toNat < 4294967296 := by
      simpa only [UInt32.size] using hnewNoWrap
    have holdAdd : (oldPtr + UInt32.ofNat i).toNat = oldPtr.toNat + i := by
      apply Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap
      · omega
      · omega
    have hnewAdd : (allocatorPtr oldBump 1 + UInt32.ofNat i).toNat =
        (allocatorPtr oldBump 1).toNat + i := by
      apply Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap
      · omega
      · omega
    have hbyte := h.realloc_preserves_byte holdCapacity hptr hcopyLength i hi
      holdAdd hnewAdd hbumpDisjoint
    simp only [Mem.read8] at hbyte
    rw [hnewAdd, holdAdd] at hbyte
    simpa only [Mem.readBytes, List.getElem_map, List.getElem_range, Mem.read8]
      using hbyte

/-- Fresh allocation only updates the allocator bump word (and may extend
memory), so every byte range disjoint from that word is preserved. -/
theorem ByteGrowSuccess.fresh_preserves_bytes
    {store final : MachineStore Universal.State}
    {oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr newCapacity oldBump final)
    (off len : Nat)
    (hdisjoint : off + len ≤ 1053960 ∨ 1053960 + 4 ≤ off) :
    final.wasm.mem.readBytes off len = store.wasm.mem.readBytes off len := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative =>
      simp only [allocatorBumpStore]
      exact Mem.readBytes_write32_disjoint _ _ _ _ _ hdisjoint
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative =>
      simp only [allocatorBumpStore, allocatorGrownStore]
      rw [Mem.readBytes_write32_disjoint _ _ _ _ _ hdisjoint]
      apply List.ext_getElem
      · simp [Mem.readBytes]
      · intro i hleft hright
        simp only [Mem.readBytes, List.getElem_map, List.getElem_range]
        rw [Mem.grow_success_bytes_eq store.wasm.mem memory _ _ _ hgrow]
  | reallocNoGrow hnonzero hfit => contradiction
  | reallocGrow hnonzero memory previousPages hgrow => contradiction

/-- Every successful grow preserves a range lying before both the allocator
metadata word and the newly allocated destination. -/
theorem ByteGrowSuccess.preserves_bytes_before
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (off len : Nat)
    (hmeta : off + len ≤ 1053960)
    (hdest : off + len ≤ (allocatorPtr oldBump 1).toNat) :
    final.wasm.mem.readBytes off len = store.wasm.mem.readBytes off len := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative =>
      simp only [allocatorBumpStore]
      exact Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hmeta)
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative =>
      simp only [allocatorBumpStore, allocatorGrownStore]
      rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hmeta)]
      apply List.ext_getElem
      · simp [Mem.readBytes]
      · intro i hleft hright
        simp only [Mem.readBytes, List.getElem_map, List.getElem_range]
        rw [Mem.grow_success_bytes_eq store.wasm.mem memory _ _ _ hgrow]
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore]
      split
      · exact Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hmeta)
      · rw [Mem.readBytes_copy_before]
        · exact Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hmeta)
        · exact hdest
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore]
      split
      · simp only [allocatorBumpStore, allocatorGrownStore]
        rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hmeta)]
        apply List.ext_getElem
        · simp [Mem.readBytes]
        · intro i hleft hright
          simp only [Mem.readBytes, List.getElem_map, List.getElem_range]
          rw [Mem.grow_success_bytes_eq store.wasm.mem memory _ _ _ hgrow]
      · simp only [allocatorBumpStore, allocatorGrownStore]
        rw [Mem.readBytes_copy_before]
        · rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inl hmeta)]
          apply List.ext_getElem
          · simp [Mem.readBytes]
          · intro i hleft hright
            simp only [Mem.readBytes, List.getElem_map, List.getElem_range]
            rw [Mem.grow_success_bytes_eq store.wasm.mem memory _ _ _ hgrow]
        · exact hdest

end Submission.HexDecodeStdio
