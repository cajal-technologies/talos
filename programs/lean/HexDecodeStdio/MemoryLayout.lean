import HexDecodeStdio.DecodeCore

namespace Submission.HexDecodeStdio

open Wasm
open Iris Iris.ProgramLogic
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC} {α : Type}

/-- Preserve the three padding bytes of an eight-byte I/O result record while
replacing its one-byte tag and four-byte count. -/
def ioWord (old : UInt64) (tag : UInt8) (count : UInt32) : UInt64 :=
  (old &&& (0x00000000ffffff00 : UInt64)) ||| tag.toUInt64 |||
    (count.toUInt64 <<< 32)

theorem pointsTo_ioWord [WasmSmallStepGS hlc α]
    (addr : UInt32) (old : UInt64) (tag : UInt8) (count : UInt32) :
    pointsTo_u64 (α := α) 0 addr (ioWord old tag count) ⊣⊢
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr⟩ (DFrac.own 1) (some tag)) ∗
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr + 1⟩ (DFrac.own 1) (some (u64Byte old 1))) ∗
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr + 2⟩ (DFrac.own 1) (some (u64Byte old 2))) ∗
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr + 3⟩ (DFrac.own 1) (some (u64Byte old 3))) ∗
      pointsTo_u32 0 (addr + 4) count := by
  simp only [pointsTo_u64, pointsTo_u32, ioWord, u64Byte, u32Byte]
  rw [show addr + 4 + 1 = addr + 5 by bv_decide,
    show addr + 4 + 2 = addr + 6 by bv_decide,
    show addr + 4 + 3 = addr + 7 by bv_decide]
  let w := (old &&& (0x00000000ffffff00 : UInt64)) ||| tag.toUInt64 |||
    (count.toUInt64 <<< 32)
  have h0 : w.toUInt8 = tag := by simp [w]; bv_decide
  have h1 : (w >>> 8).toUInt8 = (old >>> 8).toUInt8 := by
    simp [w]; bv_decide
  have h2 : (w >>> 16).toUInt8 = (old >>> 16).toUInt8 := by
    simp [w]; bv_decide
  have h3 : (w >>> 24).toUInt8 = (old >>> 24).toUInt8 := by
    simp [w]; bv_decide
  have h4 : (w >>> 32).toUInt8 = count.toUInt8 := by
    simp [w]; bv_decide
  have h5 : (w >>> 40).toUInt8 = (count >>> 8).toUInt8 := by
    simp [w]; bv_decide
  have h6 : (w >>> 48).toUInt8 = (count >>> 16).toUInt8 := by
    simp [w]; bv_decide
  have h7 : (w >>> 56).toUInt8 = (count >>> 24).toUInt8 := by
    simp [w]; bv_decide
  change
    ({ memId := 0, addr := addr } ↦ some w.toUInt8 ∗
      { memId := 0, addr := addr + 1 } ↦ some (w >>> 8).toUInt8 ∗
      { memId := 0, addr := addr + 2 } ↦ some (w >>> 16).toUInt8 ∗
      { memId := 0, addr := addr + 3 } ↦ some (w >>> 24).toUInt8 ∗
      { memId := 0, addr := addr + 4 } ↦ some (w >>> 32).toUInt8 ∗
      { memId := 0, addr := addr + 5 } ↦ some (w >>> 40).toUInt8 ∗
      { memId := 0, addr := addr + 6 } ↦ some (w >>> 48).toUInt8 ∗
      { memId := 0, addr := addr + 7 } ↦ some (w >>> 56).toUInt8) ⊣⊢ _
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  exact .rfl

theorem pointsTo_u64_as_ioWord [WasmSmallStepGS hlc α]
    (addr : UInt32) (old : UInt64) :
    pointsTo_u64 (α := α) 0 addr old ⊣⊢
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr⟩ (DFrac.own 1) (some (u64Byte old 0))) ∗
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr + 1⟩ (DFrac.own 1) (some (u64Byte old 1))) ∗
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr + 2⟩ (DFrac.own 1) (some (u64Byte old 2))) ∗
      (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, addr + 3⟩ (DFrac.own 1) (some (u64Byte old 3))) ∗
      pointsTo_u32 0 (addr + 4) ((old >>> 32).toUInt32) := by
  simp only [pointsTo_u64, pointsTo_u32, u64Byte, u32Byte]
  rw [show addr + 4 + 1 = addr + 5 by bv_decide,
    show addr + 4 + 2 = addr + 6 by bv_decide,
    show addr + 4 + 3 = addr + 7 by bv_decide]
  have h4 : (old >>> 32).toUInt8 = ((old >>> 32).toUInt32).toUInt8 := by
    bv_decide
  have h5 : (old >>> 40).toUInt8 = (((old >>> 32).toUInt32 >>> 8).toUInt8) := by
    bv_decide
  have h6 : (old >>> 48).toUInt8 = (((old >>> 32).toUInt32 >>> 16).toUInt8) := by
    bv_decide
  have h7 : (old >>> 56).toUInt8 = (((old >>> 32).toUInt32 >>> 24).toUInt8) := by
    bv_decide
  rw [h4, h5, h6, h7]
  exact .rfl

/-- Split a little-endian 64-bit memory word into its low and high 32-bit
halves. -/
theorem pointsTo_u64_as_u32s [WasmSmallStepGS hlc α]
    (addr : UInt32) (word : UInt64) :
    pointsTo_u64 (α := α) 0 addr word ⊣⊢
      pointsTo_u32 (α := α) 0 addr word.toUInt32 ∗
      pointsTo_u32 (α := α) 0 (addr + 4) (word >>> 32).toUInt32 := by
  simp only [pointsTo_u64, pointsTo_u32, u64Byte, u32Byte]
  rw [show addr + 4 + 1 = addr + 5 by bv_decide,
    show addr + 4 + 2 = addr + 6 by bv_decide,
    show addr + 4 + 3 = addr + 7 by bv_decide]
  have h0 : word.toUInt8 = word.toUInt32.toUInt8 := by bv_decide
  have h1 : (word >>> 8).toUInt8 = (word.toUInt32 >>> 8).toUInt8 := by
    bv_decide
  have h2 : (word >>> 16).toUInt8 = (word.toUInt32 >>> 16).toUInt8 := by
    bv_decide
  have h3 : (word >>> 24).toUInt8 = (word.toUInt32 >>> 24).toUInt8 := by
    bv_decide
  have h4 : (word >>> 32).toUInt8 = ((word >>> 32).toUInt32).toUInt8 := by
    bv_decide
  have h5 : (word >>> 40).toUInt8 =
      (((word >>> 32).toUInt32 >>> 8).toUInt8) := by bv_decide
  have h6 : (word >>> 48).toUInt8 =
      (((word >>> 32).toUInt32 >>> 16).toUInt8) := by bv_decide
  have h7 : (word >>> 56).toUInt8 =
      (((word >>> 32).toUInt32 >>> 24).toUInt8) := by bv_decide
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
    isplitl [H0 H1 H2 H3]
    · isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      isplitl [H2] <;> iassumption
    isplitl [H4]
    · iexact H4
    isplitl [H5]
    · iexact H5
    isplitl [H6] <;> iassumption
  · iintro ⟨⟨H0, H1, H2, H3⟩, H4, H5, H6, H7⟩
    isplitl [H0]
    · iexact H0
    isplitl [H1]
    · iexact H1
    isplitl [H2]
    · iexact H2
    isplitl [H3]
    · iexact H3
    isplitl [H4]
    · iexact H4
    isplitl [H5]
    · iexact H5
    isplitl [H6] <;> iassumption

theorem pointsTo_u64_zero_as_bytes [WasmSmallStepGS hlc α] (addr : UInt32) :
    pointsTo_u64 (α := α) 0 addr 0 ⊣⊢
      pointsToBytes 0 addr (List.replicate 8 (0 : UInt8)) := by
  simp [pointsTo_u64, pointsToBytes, u64Byte]
  rw [show addr + 1 + 1 = addr + 2 by bv_decide,
    show addr + 2 + 1 = addr + 3 by bv_decide,
    show addr + 3 + 1 = addr + 4 by bv_decide,
    show addr + 4 + 1 = addr + 5 by bv_decide,
    show addr + 5 + 1 = addr + 6 by bv_decide,
    show addr + 6 + 1 = addr + 7 by bv_decide]
  simp only [(BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

set_option maxHeartbeats 2000000 in
theorem four_u64_zero_as_bytes [WasmSmallStepGS hlc α] (addr : UInt32) :
    pointsTo_u64 (α := α) 0 addr 0 ∗
      pointsTo_u64 0 (addr + 8) 0 ∗
      pointsTo_u64 0 (addr + 16) 0 ∗
      pointsTo_u64 0 (addr + 24) 0 ⊣⊢
    pointsToBytes 0 addr (List.replicate 32 0) := by
  let z := List.replicate 8 (0 : UInt8)
  have hrep : List.replicate 32 (0 : UInt8) = z ++ (z ++ (z ++ z)) := by
    decide
  rw [hrep]
  constructor
  · iintro ⟨H0, H8, H16, H24⟩
    ihave H0 := (pointsTo_u64_zero_as_bytes addr).mp $$ H0
    ihave H8 := (pointsTo_u64_zero_as_bytes (addr + 8)).mp $$ H8
    ihave H16 := (pointsTo_u64_zero_as_bytes (addr + 16)).mp $$ H16
    ihave H24 := (pointsTo_u64_zero_as_bytes (addr + 24)).mp $$ H24
    iapply (pointsToBytes_append 0 addr z (z ++ (z ++ z))).mpr
    isplitl [H0]
    · iexact H0
    have h8 : addr + UInt32.ofNat z.length = addr + 8 := by
      simp [z]
    rw [h8]
    iapply (pointsToBytes_append 0 (addr + 8) z (z ++ z)).mpr
    isplitl [H8]
    · iexact H8
    have h16 : addr + 8 + UInt32.ofNat z.length = addr + 16 := by
      simp [z]
      bv_decide
    rw [h16]
    iapply (pointsToBytes_append 0 (addr + 16) z z).mpr
    isplitl [H16]
    · iexact H16
    have h24 : addr + 16 + UInt32.ofNat z.length = addr + 24 := by
      simp [z]
      bv_decide
    rw [h24]
    iexact H24
  · iintro H
    ihave Hparts :=
      (pointsToBytes_append 0 addr z (z ++ (z ++ z))).mp $$ H
    icases Hparts with ⟨H0, Hrest⟩
    have h8 : addr + UInt32.ofNat z.length = addr + 8 := by simp [z]
    isimp only [h8] at Hrest
    ihave Hparts :=
      (pointsToBytes_append 0 (addr + 8) z (z ++ z)).mp $$ Hrest
    icases Hparts with ⟨H8, Hrest⟩
    have h16 : addr + 8 + UInt32.ofNat z.length = addr + 16 := by
      simp [z]
      bv_decide
    isimp only [h16] at Hrest
    ihave Hparts :=
      (pointsToBytes_append 0 (addr + 16) z z).mp $$ Hrest
    icases Hparts with ⟨H16, H24⟩
    have h24 : addr + 16 + UInt32.ofNat z.length = addr + 24 := by
      simp [z]
      bv_decide
    isimp only [h24] at H24
    ihave H0 := (pointsTo_u64_zero_as_bytes addr).mpr $$ H0
    ihave H8 := (pointsTo_u64_zero_as_bytes (addr + 8)).mpr $$ H8
    ihave H16 := (pointsTo_u64_zero_as_bytes (addr + 16)).mpr $$ H16
    ihave H24 := (pointsTo_u64_zero_as_bytes (addr + 24)).mpr $$ H24
    iframe

end Submission.HexDecodeStdio
