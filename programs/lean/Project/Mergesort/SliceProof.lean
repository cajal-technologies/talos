import Project.Mergesort.Machine

/-!
# Contracts for generated slice helpers

These are the first leaf contracts on the successful recursive-sort path.
They are proved against the original generated functions, not replacement
Wasm.  The split-at-unchecked helper writes two `(pointer, length)` slice
descriptors into its caller-provided return area.
-/

namespace Project.Mergesort.SliceProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Machine

private theorem slotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 16 ≤ UInt32.size)
    (hoffset : offset ≤ 12) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private def splitParams (resultPtr dataPtr length mid sourceLoc : UInt32) :
    List Value :=
  [.i32 resultPtr, .i32 dataPtr, .i32 length, .i32 mid, .i32 sourceLoc]

private def splitLocals (suffixPtr suffixLength : UInt32) : List Value :=
  [.i32 suffixPtr, .i32 suffixLength]

/-- Exact total contract for generated local function `func96`
(`core::slice::raw::split_at_unchecked`). -/
theorem splitAtUnchecked_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (resultPtr dataPtr length mid sourceLoc : UInt32)
    (old0 old1 old2 old3 : UInt32)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size) :
    pointsTo_u32 resultPtr old0 ∗
      pointsTo_u32 (resultPtr + 4) old1 ∗
      pointsTo_u32 (resultPtr + 8) old2 ∗
      pointsTo_u32 (resultPtr + 12) old3 ⊢
    WP (.running
      ⟨⟨splitParams resultPtr dataPtr length mid sourceLoc,
          splitLocals 0 0, []⟩,
        func96, 0, [], [], []⟩ : Expr Unit) @ s; E
      [{ values,
        ⌜values = []⌝ ∗
        pointsTo_u32 (resultPtr + 0) dataPtr ∗
        pointsTo_u32 (resultPtr + 4) mid ∗
        pointsTo_u32 (resultPtr + 8)
          (dataPtr + (mid <<< (3 % 32))) ∗
        pointsTo_u32 (resultPtr + 12) (length - mid) }] := by
  obtain ⟨h00, h01, h02, h03⟩ :=
    slotFacts resultPtr 0 hroom (by decide)
  obtain ⟨h40, h41, h42, h43⟩ :=
    slotFacts resultPtr 4 hroom (by decide)
  obtain ⟨h80, h81, h82, h83⟩ :=
    slotFacts resultPtr 8 hroom (by decide)
  obtain ⟨h120, h121, h122, h123⟩ :=
    slotFacts resultPtr 12 hroom (by decide)
  iintro ⟨H0, H1, H2, H3⟩
  simp only [func96]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave H0' : pointsTo_u32 (resultPtr + 0) old0 $$ [H0]
  · rw [UInt32.add_zero]
    iexact H0
  iapply twp_store32 old0 h00 h01 h02 h03 $$ H0'
  iintro H0
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old1 h40 h41 h42 h43 $$ H1
  iintro H1
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old2 h80 h81 h82 h83 $$ H2
  iintro H2
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old3 h120 h121 h122 h123 $$ H3
  iintro H3
  iapply twp_returnFromFunction
  iapply twp.value rfl
  isplitr
  · ipureintro
    rfl
  isplitl [H0]
  · iexact H0
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · rw [UInt32.add_comm dataPtr]
    iexact H2
  · iexact H3

/-- Exact successful-path contract for generated local function `func9`, the
`RangeFrom` slice-index helper used for the recursive right half. -/
theorem rangeFrom_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (resultPtr start dataPtr length sourceLoc : UInt32)
    (oldPtr oldLength : UInt32)
    (hstart : start ≤ length)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size) :
    pointsTo_u32 resultPtr oldPtr ∗
      pointsTo_u32 (resultPtr + 4) oldLength ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 start, .i32 dataPtr,
            .i32 length, .i32 sourceLoc],
          [.i32 0, .i32 0], []⟩,
        func9, 0, [], [], []⟩ : Expr Unit) @ s; E
      [{ values,
        ⌜values = []⌝ ∗
        pointsTo_u32 (resultPtr + 0)
          (dataPtr + (start <<< (3 % 32))) ∗
        pointsTo_u32 (resultPtr + 4) (length - start) }] := by
  obtain ⟨h00, h01, h02, h03⟩ :=
    slotFacts resultPtr 0 hroom (by decide)
  obtain ⟨h40, h41, h42, h43⟩ :=
    slotFacts resultPtr 4 hroom (by decide)
  iintro ⟨Hptr, Hlength⟩
  simp only [func9]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have hnot : ¬start > length := by
    rw [gt_iff_lt, UInt32.lt_iff_toNat_lt]
    rw [UInt32.le_iff_toNat_le] at hstart
    omega
  iapply twp_gtU (result := 0) (by simp [hnot])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldLength h40 h41 h42 h43 $$ Hlength
  iintro Hlength
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hptr' : pointsTo_u32 (resultPtr + 0) oldPtr $$ [Hptr]
  · rw [UInt32.add_zero]
    iexact Hptr
  iapply twp_store32 oldPtr h00 h01 h02 h03 $$ Hptr'
  iintro Hptr
  iapply twp_returnFromFunction
  iapply twp.value rfl
  isplitr
  · ipureintro
    rfl
  isplitl [Hptr]
  · rw [UInt32.add_comm dataPtr]
    iexact Hptr
  · iexact Hlength

end Project.Mergesort.SliceProof
