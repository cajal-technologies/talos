import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.SmallStepState
import CodeLib.RustStd.U64.AbsDiff

/-!
# Byte-range `pointsToBytes` slicing

Borrow/update a single byte of an owned byte range and get a wand that
restores it (`pointsToBytes_focus`/`_focus_update`), split and rejoin a
range (`pointsToBytes_slice`/`_take_drop`/`_take_drop_join`), view a u64 as
its four bytes (`pointsTo_u64_as_bytes`), and the four consecutive
`(ptr + n).toNat` address facts (`wordAccessFacts`) — all bv-decide-free.
-/

namespace Wasm.SepLogic

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

/-- Four-byte address facts obtained without bit-vector automation. -/
theorem wordAccessFacts (ptr : UInt32) (offset : Nat)
    (hfit : ptr.toNat + offset + 4 < UInt32.size) :
    (ptr + UInt32.ofNat offset).toNat = ptr.toNat + offset ∧
    ((ptr + UInt32.ofNat offset) + 1).toNat =
      (ptr + UInt32.ofNat offset).toNat + 1 ∧
    ((ptr + UInt32.ofNat offset) + 2).toNat =
      (ptr + UInt32.ofNat offset).toNat + 2 ∧
    ((ptr + UInt32.ofNat offset) + 3).toNat =
      (ptr + UInt32.ofNat offset).toNat + 3 := by
  have hadd (n : Nat) (hn : n ≤ offset + 3) :
      (ptr + UInt32.ofNat n).toNat = ptr.toNat + n :=
    Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap ptr n
      (by simp only [UInt32.size] at hfit ⊢; omega)
      (by simp only [UInt32.size] at hfit ⊢; omega)
  refine ⟨hadd offset (by omega), ?_, ?_, ?_⟩
  · rw [show (1 : UInt32) = UInt32.ofNat 1 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 1) (by omega),
      hadd offset (by omega)]
    omega
  · rw [show (2 : UInt32) = UInt32.ofNat 2 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 2) (by omega),
      hadd offset (by omega)]
    omega
  · rw [show (3 : UInt32) = UInt32.ofNat 3 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 3) (by omega),
      hadd offset (by omega)]
    omega

/-- Borrow one byte from an owned byte range and return a wand that restores
the original range. -/
theorem pointsToBytes_focus {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ byte : UInt8,
        (⟨memId, addr + UInt32.ofNat i⟩ ↦w byte) ∗
        (((⟨memId, addr + UInt32.ofNat i⟩ ↦w byte) -∗
          pointsToBytes memId addr bytes) ∗
        ⌜bytes[i]? = some byte⌝)) := by
  induction bytes generalizing addr i with
  | nil => simp at hi
  | cons head tail ih =>
      iintro Hbytes
      ihave Hsplit := (pointsToBytes_cons memId addr head tail).mp $$ Hbytes
      icases Hsplit with ⟨Hhead, Htail⟩
      cases i with
      | zero =>
          have hzero : UInt32.ofNat 0 = 0 := by decide
          iexists head
          isplitl [Hhead]
          · rw [hzero, UInt32.add_zero]
            iexact Hhead
          · isplitl [Htail]
            · rw [hzero, UInt32.add_zero]
              iintro Hhead
              iapply (pointsToBytes_cons memId addr head tail).mpr
              iframe
            · ipureintro
              rfl
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          ihave Hfocus := ih (addr + 1) j hi $$ Htail
          icases Hfocus with ⟨%byte, Hbyte, Hput, %hbyte⟩
          iexists byte
          rw [← byte_offset_succ addr j]
          isplitl [Hbyte]
          · iexact Hbyte
          · isplitl [Hhead Hput]
            · iintro Hbyte
              iapply (pointsToBytes_cons memId addr head tail).mpr
              isplitl [Hhead]
              · iexact Hhead
              · iapply Hput
                rw [byte_offset_succ addr j]
                iexact Hbyte
            · ipureintro
              simpa only [List.getElem?_cons_succ] using hbyte

/-- Borrow one byte and rebuild the range with an updated byte. -/
theorem pointsToBytes_focus_update {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% ∃ byte : UInt8,
        (⟨memId, addr + UInt32.ofNat i⟩ ↦w byte) ∗
        ((∀ newByte : UInt8,
          (⟨memId, addr + UInt32.ofNat i⟩ ↦w newByte) -∗
          pointsToBytes memId addr (bytes.set i newByte)) ∗
        ⌜bytes[i]? = some byte⌝)) := by
  induction bytes generalizing addr i with
  | nil => simp at hi
  | cons head tail ih =>
      iintro Hbytes
      ihave Hsplit := (pointsToBytes_cons memId addr head tail).mp $$ Hbytes
      icases Hsplit with ⟨Hhead, Htail⟩
      cases i with
      | zero =>
          have hzero : UInt32.ofNat 0 = 0 := by decide
          iexists head
          isplitl [Hhead]
          · rw [hzero, UInt32.add_zero]
            iexact Hhead
          · isplitl [Htail]
            · iintro %newByte Hnew
              simp only [List.set]
              iapply (pointsToBytes_cons memId addr newByte tail).mpr
              isplitl [Hnew]
              · rw [hzero, UInt32.add_zero]
                iexact Hnew
              · iexact Htail
            · ipureintro
              rfl
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          ihave Hfocus := ih (addr + 1) j hi $$ Htail
          icases Hfocus with ⟨%byte, Hbyte, Hput, %hbyte⟩
          iexists byte
          rw [← byte_offset_succ addr j]
          isplitl [Hbyte]
          · iexact Hbyte
          · isplitl [Hhead Hput]
            · iintro %newByte Hnew
              simp only [List.set]
              iapply (pointsToBytes_cons memId addr head
                (tail.set j newByte)).mpr
              isplitl [Hhead]
              · iexact Hhead
              · ispecialize Hput $$ %newByte
                iapply Hput
                rw [byte_offset_succ addr j]
                iexact Hnew
            · ipureintro
              simpa only [List.getElem?_cons_succ] using hbyte

/-- Split an owned byte range after `n` bytes. -/
theorem pointsToBytes_take_drop {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% pointsToBytes memId addr (bytes.take n) ∗
        pointsToBytes memId (addr + UInt32.ofNat n) (bytes.drop n)) := by
  have hlen : (bytes.take n).length = n := List.length_take_of_le hn
  iintro Hbytes
  ihave Hbytes' : pointsToBytes memId addr
      (bytes.take n ++ bytes.drop n) $$ [Hbytes]
  · rw [List.take_append_drop]
    iexact Hbytes
  ihave Hsplit := (pointsToBytes_append memId addr
    (bytes.take n) (bytes.drop n)).mp $$ Hbytes'
  have haddr : addr + UInt32.ofNat (bytes.take n).length =
      addr + UInt32.ofNat n := by rw [hlen]
  ihave Hsplit' : (iprop% pointsToBytes memId addr (bytes.take n) ∗
      pointsToBytes memId (addr + UInt32.ofNat n) (bytes.drop n)) $$ [Hsplit]
  · rw [← haddr]
    iexact Hsplit
  iexact Hsplit'

/-- Reassemble the halves produced by `pointsToBytes_take_drop`. -/
theorem pointsToBytes_take_drop_join {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    (iprop% pointsToBytes memId addr (bytes.take n) ∗
      pointsToBytes memId (addr + UInt32.ofNat n) (bytes.drop n)) ⊢
      pointsToBytes (α := α) memId addr bytes := by
  have hlen : (bytes.take n).length = n := List.length_take_of_le hn
  have haddr : addr + UInt32.ofNat (bytes.take n).length =
      addr + UInt32.ofNat n := by rw [hlen]
  iintro Hsplit
  ihave Hsplit' : (iprop% pointsToBytes memId addr (bytes.take n) ∗
      pointsToBytes memId
        (addr + UInt32.ofNat (bytes.take n).length) (bytes.drop n)) $$ [Hsplit]
  · rw [haddr]
    iexact Hsplit
  ihave Hbytes := (pointsToBytes_append memId addr
    (bytes.take n) (bytes.drop n)).mpr $$ Hsplit'
  have heq : pointsToBytes (α := α) memId addr
      (bytes.take n ++ bytes.drop n) = pointsToBytes memId addr bytes := by
    rw [List.take_append_drop]
  ihave Hbytes' : pointsToBytes memId addr bytes $$ [Hbytes]
  · rw [← heq]
    iexact Hbytes
  iexact Hbytes'

/-- Split out a contiguous slice while retaining both surrounding ranges. -/
theorem pointsToBytes_slice {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (memId : Nat) (addr : UInt32) (bytes : List UInt8) (start count : Nat)
    (hstart : start ≤ bytes.length)
    (hcount : count ≤ (bytes.drop start).length) :
    pointsToBytes (α := α) memId addr bytes ⊢
      (iprop% pointsToBytes memId addr (bytes.take start) ∗
        pointsToBytes memId (addr + UInt32.ofNat start)
          ((bytes.drop start).take count) ∗
        pointsToBytes memId
          ((addr + UInt32.ofNat start) + UInt32.ofNat count)
          ((bytes.drop start).drop count)) := by
  iintro Hbytes
  ihave Hfirst := pointsToBytes_take_drop memId addr bytes start hstart $$ Hbytes
  icases Hfirst with ⟨Hbefore, Htail⟩
  ihave Hsecond := pointsToBytes_take_drop memId
    (addr + UInt32.ofNat start) (bytes.drop start) count hcount $$ Htail
  icases Hsecond with ⟨Hmiddle, Hafter⟩
  iframe

/-- A little-endian u64 assertion is the corresponding eight-byte slice. -/
theorem pointsTo_u64_as_bytes {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (addr : UInt32) (word : UInt64) :
    pointsTo_u64 memId addr word ⊣⊢
      pointsToBytes memId addr
        [u64Byte word 0, u64Byte word 1, u64Byte word 2, u64Byte word 3,
         u64Byte word 4, u64Byte word 5, u64Byte word 6, u64Byte word 7] := by
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; congr 1
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; congr 1
  have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; congr 1
  have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; congr 1
  have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; congr 1
  have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; congr 1
  simp only [pointsTo_u64, pointsToBytes, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

/-- Borrow an eight-byte word from a byte window and return a wand restoring
the unchanged range. -/
theorem pointsToBytes_focus_u64 {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] (memId : Nat) (base : UInt32)
    (bytes : List UInt8) (i : Nat) (word : UInt64)
    (hi : i + 8 ≤ bytes.length)
    (hword : (bytes.drop i).take 8 =
      [u64Byte word 0, u64Byte word 1, u64Byte word 2, u64Byte word 3,
       u64Byte word 4, u64Byte word 5, u64Byte word 6, u64Byte word 7]) :
    pointsToBytes (α := α) memId base bytes ⊢
      (iprop% pointsTo_u64 memId (base + UInt32.ofNat i) word ∗
        (pointsTo_u64 memId (base + UInt32.ofNat i) word -∗
          pointsToBytes memId base bytes)) := by
  iintro Hbytes
  ihave ⟨Hpre, Hmid, Hpost⟩ := pointsToBytes_slice memId base bytes i 8
    (by omega) (by simp [List.length_drop]; omega) $$ Hbytes
  isplitl [Hmid]
  · iapply (pointsTo_u64_as_bytes memId
      (base + UInt32.ofNat i) word).mpr
    irw_exact [← hword] with Hmid
  iintro Hword
  ihave Hmid := (pointsTo_u64_as_bytes memId
    (base + UInt32.ofNat i) word).mp $$ Hword
  isimp only [← hword] at Hmid
  iapply_frame pointsToBytes_take_drop_join memId base bytes i (by omega)
  iapply_frame pointsToBytes_take_drop_join memId
    (base + UInt32.ofNat i) (bytes.drop i) 8
    (by simp [List.length_drop]; omega)

/-! ## Word windows -/

/-- The four little-endian bytes of a `UInt32`. -/
def u32Bytes (word : UInt32) : List UInt8 :=
  [u32Byte word 0, u32Byte word 1, u32Byte word 2, u32Byte word 3]

end Wasm.SepLogic
