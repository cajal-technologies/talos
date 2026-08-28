import Mathlib
import CodeLib

/-!
Local helper module for the submission. Solvers may add lemmas and definitions
here (and in sibling modules under `Submission/`) and import them from
`Project.HexEncodeStdio.lean`.
-/

namespace Project.HexEncodeStdio.Helpers

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private theorem packed_u64Byte_low (lo hi : UInt32) (i : Nat) (hi4 : i < 4) :
    u64Byte (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) i = u32Byte lo i := by
  interval_cases i <;> simp only [u64Byte, u32Byte] <;> bv_decide

private theorem packed_u64Byte_high (lo hi : UInt32) (i : Nat) (hi4 : i < 4) :
    u64Byte (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) (i + 4) = u32Byte hi i := by
  interval_cases i <;> simp only [u64Byte, u32Byte] <;> bv_decide

/-- Split a little-endian 64-bit cell into its low and high 32-bit halves. -/
theorem pointsTo_u64_pair_split {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    (memId : Nat) (addr lo hi : UInt32) :
    pointsTo_u64 (α := α) memId addr
        (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) ⊢
      (iprop% pointsTo_u32 memId addr lo ∗
        pointsTo_u32 memId (addr + 4) hi) := by
  rw [(pointsTo_u64_eq memId addr
      (lo.toUInt64 ||| (hi.toUInt64 <<< 32))).to_eq,
    (pointsTo_u32_eq memId addr lo).to_eq,
    (pointsTo_u32_eq memId (addr + 4) hi).to_eq]
  rw [packed_u64Byte_low lo hi 0 (by omega),
    packed_u64Byte_low lo hi 1 (by omega),
    packed_u64Byte_low lo hi 2 (by omega),
    packed_u64Byte_low lo hi 3 (by omega),
    packed_u64Byte_high lo hi 0 (by omega),
    packed_u64Byte_high lo hi 1 (by omega),
    packed_u64Byte_high lo hi 2 (by omega),
    packed_u64Byte_high lo hi 3 (by omega)]
  have h5 : addr + 5 = (addr + 4) + 1 := by bv_decide
  have h6 : addr + 6 = (addr + 4) + 2 := by bv_decide
  have h7 : addr + 7 = (addr + 4) + 3 := by bv_decide
  rw [← h5, ← h6, ← h7]
  iintro H
  icases H with ⟨H0, H⟩
  icases H with ⟨H1, H⟩
  icases H with ⟨H2, H⟩
  icases H with ⟨H3, H⟩
  icases H with ⟨H4, H⟩
  icases H with ⟨H5, H⟩
  icases H with ⟨H6, H7⟩
  isplitl [H0 H1 H2 H3]
  · iframe
  · iframe

/-- Join adjacent low and high 32-bit cells into their little-endian word. -/
theorem pointsTo_u64_pair_join {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    (memId : Nat) (addr lo hi : UInt32) :
    (iprop% pointsTo_u32 memId addr lo ∗
      pointsTo_u32 memId (addr + 4) hi) ⊢
    pointsTo_u64 (α := α) memId addr
      (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) := by
  rw [(pointsTo_u64_eq memId addr
      (lo.toUInt64 ||| (hi.toUInt64 <<< 32))).to_eq,
    (pointsTo_u32_eq memId addr lo).to_eq,
    (pointsTo_u32_eq memId (addr + 4) hi).to_eq]
  rw [packed_u64Byte_low lo hi 0 (by omega),
    packed_u64Byte_low lo hi 1 (by omega),
    packed_u64Byte_low lo hi 2 (by omega),
    packed_u64Byte_low lo hi 3 (by omega),
    packed_u64Byte_high lo hi 0 (by omega),
    packed_u64Byte_high lo hi 1 (by omega),
    packed_u64Byte_high lo hi 2 (by omega),
    packed_u64Byte_high lo hi 3 (by omega)]
  have h5 : addr + 5 = (addr + 4) + 1 := by bv_decide
  have h6 : addr + 6 = (addr + 4) + 2 := by bv_decide
  have h7 : addr + 7 = (addr + 4) + 3 := by bv_decide
  rw [← h5, ← h6, ← h7]
  iintro H
  icases H with ⟨Hlo, Hhi⟩
  icases Hlo with ⟨H0, Hlo⟩
  icases Hlo with ⟨H1, Hlo⟩
  icases Hlo with ⟨H2, H3⟩
  icases Hhi with ⟨H4, Hhi⟩
  icases Hhi with ⟨H5, Hhi⟩
  icases Hhi with ⟨H6, H7⟩
  iframe

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
      (by norm_num [UInt32.size] at hfit ⊢; omega)
      (by norm_num [UInt32.size] at hfit ⊢; omega)
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

/-- Borrow one byte from an owned byte range.  The returned wand puts the
borrowed cell back and reconstructs the original range.  Keeping this lemma
at the `pointsToBytes` level avoids exposing address arithmetic in every
table/input lookup of the encoder. -/
theorem pointsToBytes_focus {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
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
              isplitl [Hhead]
              · iexact Hhead
              · iexact Htail
            · ipureintro; rfl
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

/-- Borrow one byte and permit replacing it before rebuilding the byte range. -/
theorem pointsToBytes_focus_update {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
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
              iapply (pointsToBytes_cons memId addr head (tail.set j newByte)).mpr
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
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
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

/-- Reassemble the two halves produced by `pointsToBytes_take_drop`. -/
theorem pointsToBytes_take_drop_join {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
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

/-- Zero-offset store rule with its points-to address normalized. -/
theorem wp_store8_zero {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {address value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldByte : UInt8) :
    ▷ (⟨0, address⟩ ↦w oldByte) -∗
    ▷ ((⟨0, address⟩ ↦w value.toUInt8) -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) -∗
    WP (.running ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
      .store8 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  simpa only [UInt32.add_zero] using
    (Wasm.SmallStep.wp_store8 (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value) oldByte (by simp))

end Project.HexEncodeStdio.Helpers
