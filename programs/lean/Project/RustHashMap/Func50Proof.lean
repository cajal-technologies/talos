import Project.RustHashMap.DropErrorContracts
import Project.RustHashMap.FrameCells
import CodeLib.SepLogic.SmallStepTotalLiftingBytesTerminal

/-!
# Proof of the kind byte of the decode-error subtree

Local `func50`, absolute index 53, returns the `ErrorKind` byte of a
sixteen-byte error, at WAT lines 9708 to 9744.

The body computes `local 1 := sp - 16` and never writes the stack
pointer, so the sixteen bytes are borrowed from
`StackBelow sp redZoneDepth below`, written, and given back as `below'`.

Word 0 selects the arm.  The value `0x80000000` marks a simple error, and
the body then copies the byte at offset 4.  Every other value marks an
error that owns a buffer, and the body copies the byte at offset 12.
Both arms put the byte at `frame + 15` and read it back from there, so
the two arms join at one `load8_u`.

The returned byte is abstract, because the contract quantifies it.  The
proof therefore names the byte that it cuts out of the error and never
computes it.
-/

namespace Project.RustHashMap.Func50Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- The mask of the flag keeps a set flag. -/
private theorem and_one_one : (1 : UInt32) &&& 1 = 1 := by decide

/-- The mask of the flag keeps a clear flag. -/
private theorem and_zero_one : (0 : UInt32) &&& 1 = 0 := by decide

private theorem func50_index :
    Project.RustHashMap.«module».funcs[50]? =
      some Project.RustHashMap.func50Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The read of the kind byte gives the region and the error back. -/
theorem func50_correct [WasmSmallStepGS hlc Universal.State] :
    Func50Spec (hlc := hlc) := by
  unfold Func50Spec CallContract callExpr
  intro sp errPtr word0 word1 word2 word3 below callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Herr, %hfacts, Hcont⟩
  obtain ⟨hspLow, herrNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 53
      Project.RustHashMap.func50Def (by decide) func50_index with Hmodule
  simp [Project.RustHashMap.func50Def, Project.RustHashMap.func50,
    Function.toLocals, Function.numParams]
  -- arithmetic on the red zone and on the error
  have hred : redZoneDepth = 16 := rfl
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hspNat : (16 : Nat) ≤ sp.toNat := by rw [hred] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr
        (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat redZoneDepth = sp - 16 := rfl
  have herrLen :
      (WordCodec.u32le.serialize [word0, word1, word2, word3]).length = 16 := by
    simp
  have hf15 : sp - 16 + UInt32.ofNat 15 = sp - 16 + 15 := rfl
  have hf15Nat : (sp - 16 + (15 : UInt32)).toNat = (sp - 16).toNat + 15 :=
    Slices.byteOffset_toNat (sp - 16) 15 (by omega)
  have hs15 : (sp - 16 + (15 : UInt32)).toNat
      = (sp - 16).toNat + (15 : UInt32).toNat := by rw [hf15Nat]; rfl
  have herr4 : errPtr + UInt32.ofNat 4 = errPtr + 4 := rfl
  have herr5 : errPtr + (4 : UInt32) + UInt32.ofNat 1 = errPtr + 5 :=
    frame_offset errPtr 4 1 5 rfl
  have herr12 : errPtr + UInt32.ofNat 12 = errPtr + 12 := rfl
  have herr13 : errPtr + (12 : UInt32) + UInt32.ofNat 1 = errPtr + 13 :=
    frame_offset errPtr 12 1 13 rfl
  have herr4Nat : (errPtr + (4 : UInt32)).toNat = errPtr.toNat + 4 :=
    Slices.byteOffset_toNat errPtr 4 (by omega)
  have herr12Nat : (errPtr + (12 : UInt32)).toNat = errPtr.toNat + 12 :=
    Slices.byteOffset_toNat errPtr 12 (by omega)
  have hs4 : (errPtr + (4 : UInt32)).toNat
      = errPtr.toNat + (4 : UInt32).toNat := by rw [herr4Nat]; rfl
  have hs12 : (errPtr + (12 : UInt32)).toNat
      = errPtr.toNat + (12 : UInt32).toNat := by rw [herr12Nat]; rfl
  have herrCells : errPtr.toNat
      + 4 * ([word0, word1, word2, word3] : List UInt32).length
        < UInt32.size := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨he0, he0_1, he0_2, he0_3⟩ := offset_facts errPtr 0 0 rfl (by omega)
  -- the error, as one slice again
  ihave Herr : Slices.ByteSlice 0 errPtr
      (WordCodec.u32le.serialize [word0, word1, word2, word3]) $$ [Herr]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Herr
  -- the red zone, with its last byte cut out
  ihave ⟨%hbelowLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) redZoneDepth below hbase16 $$ Hbelow
  have hbelowLen : below.length = 16 := by rw [hbelowLength, hred]
  have hlow15Length : (below.take 15).length = 15 := by
    rw [List.length_take]; omega
  have hlastLength : (below.drop 15).length = 1 := by
    rw [List.length_drop]; omega
  ihave ⟨Hlow15, Hlast⟩ := ByteSlice_cut (sp - 16) below 15 (by omega) $$ Hframe
  isimp only [hf15] at Hlast
  obtain ⟨oldByte, hlastShape⟩ := List.length_eq_one_iff.mp hlastLength
  isimp only [hlastShape] at Hlast
  ihave ⟨%hlastBound, Hlastbyte⟩ :=
    (Slices.ByteSlice_singleton 0 (sp - 16 + 15) oldByte).mp $$ Hlast
  -- `local 1 := sp - 16`, which the body never commits
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet
  -- `local 2 := ([error] == 0x80000000)`
  ihave Herrcells :=
    cells_of_ByteSlice errPtr [word0, word1, word2, word3] $$ Herr
  wasm_twp_pures [twp_localGet]
  ihave ⟨Hw0, Hw0close⟩ :=
    cell_load errPtr 0 [word0, word1, word2, word3] 0 word0 (by simp) rfl rfl $$
      Herrcells
  wasm_twp_rebind twp_load32 (address := errPtr) (offset := 0) word0
    he0 he0_1 he0_2 he0_3 with Hw0
  ihave Herrcells := Hw0close $$ Hw0
  ihave Herr :=
    ByteSlice_of_cells errPtr [word0, word1, word2, word3] herrCells $$ Herrcells
  wasm_twp_pures [twp_const]
  by_cases hsimple : word0 = 2147483648
  · -- the simple error: the kind byte sits at offset 4
    iapply twp_eq (result := 1) (by rw [if_pos hsimple])
    wasm_twp_localSet
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_and]
      using [and_one_one]
    iapply twp_select (selected := .i32 0)
      (by rw [if_pos (by decide : (1 : UInt32) ≠ 0)])
    wasm_twp_pures [twp_const twp_and] using [and_zero_one]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- the byte at offset 4 of the error
    have haLen :
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).take 4).length
          = 4 := by rw [List.length_take]; omega
    have hbLen :
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).drop 4).length
          = 12 := by rw [List.length_drop]; omega
    ihave ⟨Ha, Hb⟩ :=
      ByteSlice_cut errPtr
        (WordCodec.u32le.serialize [word0, word1, word2, word3]) 4
        (by omega) $$ Herr
    isimp only [herr4] at Hb
    have hcLen :
        (((WordCodec.u32le.serialize [word0, word1, word2, word3]).drop
          4).take 1).length = 1 := by rw [List.length_take]; omega
    ihave ⟨Hc, Hd⟩ :=
      ByteSlice_cut (errPtr + 4)
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).drop 4) 1
        (by omega) $$ Hb
    isimp only [herr5] at Hd
    obtain ⟨kindByte, hcShape⟩ := List.length_eq_one_iff.mp hcLen
    isimp only [hcShape] at Hc
    have hrejoin :
        (WordCodec.u32le.serialize [word0, word1, word2, word3]).take 4
          ++ ([kindByte]
            ++ ((WordCodec.u32le.serialize
              [word0, word1, word2, word3]).drop 4).drop 1)
          = WordCodec.u32le.serialize [word0, word1, word2, word3] := by
      rw [← hcShape, List.take_append_drop, List.take_append_drop]
    ihave ⟨%hcBound, Hkb⟩ :=
      (Slices.ByteSlice_singleton 0 (errPtr + 4) kindByte).mp $$ Hc
    -- `[frame + 15] := [error + 4]`
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load8U_gen (address := errPtr) (offset := 4) kindByte
      hs4 with Hkb
    wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 15) oldByte
      hs15 with Hlastbyte
    isimp only [UInt8.toUInt8_toUInt32] at Hlastbyte
    wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
    -- the tail reads the byte back
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load8U_gen (address := sp - 16) (offset := 15) kindByte
      hs15 with Hlastbyte
    wasm_twp_return_from_call Hmodule [List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append]
    -- the red zone, as bytes again
    ihave Hlast :=
      (Slices.ByteSlice_singleton 0 (sp - 16 + 15) kindByte).mpr $$ [Hlastbyte]
    · isplitl_pureexact hlastBound
      iexact Hlastbyte
    ihave Hframe :=
      ByteSlice_glue (sp - 16) (below.take 15) [kindByte] 15 hlow15Length $$
        [Hlow15 Hlast]
    · isplitl_exact Hlow15
      · irw_exact [hf15] with Hlast
    ihave Hbelow :=
      StackBelow_intro sp (sp - 16) redZoneDepth (below.take 15 ++ [kindByte])
        (by simp [hlow15Length, hred]) hbase16 $$ Hframe
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    -- the error, unchanged
    ihave Hc :=
      (Slices.ByteSlice_singleton 0 (errPtr + 4) kindByte).mpr $$ [Hkb]
    · isplitl_pureexact hcBound
      iexact Hkb
    ihave Hb :=
      ByteSlice_glue (errPtr + 4) [kindByte]
        (((WordCodec.u32le.serialize
          [word0, word1, word2, word3]).drop 4).drop 1) 1 rfl $$ [Hc Hd]
    · isplitl_exact Hc
      · irw_exact [herr5] with Hd
    ihave Herr :=
      ByteSlice_glue errPtr
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).take 4)
        ([kindByte]
          ++ ((WordCodec.u32le.serialize
            [word0, word1, word2, word3]).drop 4).drop 1) 4 haLen $$ [Ha Hb]
    · isplitl_exact Ha
      · irw_exact [herr4] with Hb
    isimp only [hrejoin] at Herr
    wasm_serialize_norm at Herr
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.cons_append,
      List.nil_append] at Hcont
    ihave Hcont := Hcont $$ %kindByte %(below.take 15 ++ [kindByte])
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Herr
    · isplitl_exact Hmodule
      · iexact Henv
  · -- the error owns a buffer: the kind byte sits at offset 12
    iapply twp_eq (result := 0) (by rw [if_neg hsimple])
    wasm_twp_localSet
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_and]
      using [and_zero_one]
    iapply twp_select (selected := .i32 1)
      (by rw [if_neg (by decide : ¬ (0 : UInt32) ≠ 0)])
    wasm_twp_pures [twp_const twp_and] using [and_one_one]
    iapply twp_eqz (result := 0) (by decide)
    iapply twp_brIfZero
    -- the byte at offset 12 of the error
    have haLen :
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).take 12).length
          = 12 := by rw [List.length_take]; omega
    have hbLen :
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).drop 12).length
          = 4 := by rw [List.length_drop]; omega
    ihave ⟨Ha, Hb⟩ :=
      ByteSlice_cut errPtr
        (WordCodec.u32le.serialize [word0, word1, word2, word3]) 12
        (by omega) $$ Herr
    isimp only [herr12] at Hb
    have hcLen :
        (((WordCodec.u32le.serialize [word0, word1, word2, word3]).drop
          12).take 1).length = 1 := by rw [List.length_take]; omega
    ihave ⟨Hc, Hd⟩ :=
      ByteSlice_cut (errPtr + 12)
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).drop 12) 1
        (by omega) $$ Hb
    isimp only [herr13] at Hd
    obtain ⟨kindByte, hcShape⟩ := List.length_eq_one_iff.mp hcLen
    isimp only [hcShape] at Hc
    have hrejoin :
        (WordCodec.u32le.serialize [word0, word1, word2, word3]).take 12
          ++ ([kindByte]
            ++ ((WordCodec.u32le.serialize
              [word0, word1, word2, word3]).drop 12).drop 1)
          = WordCodec.u32le.serialize [word0, word1, word2, word3] := by
      rw [← hcShape, List.take_append_drop, List.take_append_drop]
    ihave ⟨%hcBound, Hkb⟩ :=
      (Slices.ByteSlice_singleton 0 (errPtr + 12) kindByte).mp $$ Hc
    -- `[frame + 15] := [error + 12]`
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load8U_gen (address := errPtr) (offset := 12) kindByte
      hs12 with Hkb
    wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 15) oldByte
      hs15 with Hlastbyte
    isimp only [UInt8.toUInt8_toUInt32] at Hlastbyte
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- the tail reads the byte back
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load8U_gen (address := sp - 16) (offset := 15) kindByte
      hs15 with Hlastbyte
    wasm_twp_return_from_call Hmodule [List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append]
    -- the red zone, as bytes again
    ihave Hlast :=
      (Slices.ByteSlice_singleton 0 (sp - 16 + 15) kindByte).mpr $$ [Hlastbyte]
    · isplitl_pureexact hlastBound
      iexact Hlastbyte
    ihave Hframe :=
      ByteSlice_glue (sp - 16) (below.take 15) [kindByte] 15 hlow15Length $$
        [Hlow15 Hlast]
    · isplitl_exact Hlow15
      · irw_exact [hf15] with Hlast
    ihave Hbelow :=
      StackBelow_intro sp (sp - 16) redZoneDepth (below.take 15 ++ [kindByte])
        (by simp [hlow15Length, hred]) hbase16 $$ Hframe
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    -- the error, unchanged
    ihave Hc :=
      (Slices.ByteSlice_singleton 0 (errPtr + 12) kindByte).mpr $$ [Hkb]
    · isplitl_pureexact hcBound
      iexact Hkb
    ihave Hb :=
      ByteSlice_glue (errPtr + 12) [kindByte]
        (((WordCodec.u32le.serialize
          [word0, word1, word2, word3]).drop 12).drop 1) 1 rfl $$ [Hc Hd]
    · isplitl_exact Hc
      · irw_exact [herr13] with Hd
    ihave Herr :=
      ByteSlice_glue errPtr
        ((WordCodec.u32le.serialize [word0, word1, word2, word3]).take 12)
        ([kindByte]
          ++ ((WordCodec.u32le.serialize
            [word0, word1, word2, word3]).drop 12).drop 1) 12 haLen $$ [Ha Hb]
    · isplitl_exact Ha
      · irw_exact [herr12] with Hb
    isimp only [hrejoin] at Herr
    wasm_serialize_norm at Herr
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.cons_append,
      List.nil_append] at Hcont
    ihave Hcont := Hcont $$ %kindByte %(below.take 15 ++ [kindByte])
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Herr
    · isplitl_exact Hmodule
      · iexact Henv

end Project.RustHashMap.Func50Proof
