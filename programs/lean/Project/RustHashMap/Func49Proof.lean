import Project.RustHashMap.Func35Proof
import Project.RustHashMap.Func50Proof
import Project.RustHashMap.Func51Proof
import Project.RustHashMap.Func52Proof

/-!
# Proof of the decode-error conversion

Local `func49`, absolute index 52, turns the `io::Error` of the borsh
decoder into the error that the output slot of the decoder takes, at WAT
lines 9645 to 9705.

The body keeps a committed sixteen-byte frame.  It reads the `ErrorKind`
byte of the error with absolute `func 53`, puts the byte at `frame + 14`,
and compares it with the static byte at 1049136 with absolute `func 54`.

The two arms are the opposite way round from the first reading of the
code.  `br_if` leaves the inner block when the comparison returns a
non-zero value, which is when the two bytes are EQUAL.

* The bytes are equal.  The body builds a second `io::Error` into the
  output slot with absolute `func 55`, from the 26-byte message at
  1049137, and then drops the first error with absolute `func 38`.  WAT
  lines 9686 to 9700.
* The bytes differ.  The body clears `frame + 15`, copies the sixteen
  bytes of the error into the output slot with two `i64` block moves, and
  leaves the error alone.  WAT lines 9673 to 9684.

The flag at `frame + 15` carries the choice to the second block, which
runs the drop only when the flag is still 1.

Word 0 of the output is never `okTag`.  On the copy arm it is word 0 of
the input, which the caller promises is not `okTag`.  On the other arm it
is the capacity of a 26-byte `String`, and `Func52Spec` promises that the
capacity is not `okTag`.

The theorem is unconditional, because all four callees are proved.
-/

namespace Project.RustHashMap.Func49Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.ErrorNewContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- The mask of the flag keeps a set flag. -/
private theorem and_one_one : (1 : UInt32) &&& 1 = 1 := by decide

/-- The mask of the flag keeps a clear flag. -/
private theorem and_zero_one : (0 : UInt32) &&& 1 = 0 := by decide

/-- The mask of the loaded flag keeps a set flag. -/
private theorem byte_and_one_one : (1 : UInt8).toUInt32 &&& 1 = 1 := by decide

/-- The mask of the loaded flag keeps a clear flag. -/
private theorem byte_and_zero_one : (0 : UInt8).toUInt32 &&& 1 = 0 := by decide

private theorem func49_index :
    Project.RustHashMap.«module».funcs[49]? =
      some Project.RustHashMap.func49Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The conversion writes the output slot, gives the storage of the error
back, and never writes the success tag. -/
theorem func49_correct [WasmSmallStepGS hlc Universal.State] :
    Func49Spec (hlc := hlc) := by
  unfold Func49Spec CallContract callExpr
  intro sp out errPtr errWord0 errWord1 errWord2 errWord3 heapId outBefore
    below dataBytes storedCursor frontier history input output raised
    callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Herr, Hdata, Hbump, Hstreams, %hfacts,
    Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, herrNowrap, herrWord0,
    hdataLength⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 52
      Project.RustHashMap.func49Def (by decide) func49_index with Hmodule
  simp [Project.RustHashMap.func49Def, Project.RustHashMap.func49,
    Function.toLocals, Function.numParams]
  -- arithmetic, named while the context is still small
  have hdepth49 : func49Depth = 176 := rfl
  have hdepthE : errorNewDepth = 160 := rfl
  have hred : redZoneDepth = 16 := rfl
  have hdropD : dropDepth = 32 := rfl
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hspNat : (176 : Nat) ≤ sp.toNat := by
    rw [hdepth49] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr
        (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := rfl
  have hcut : func49Depth - 16 = errorNewDepth := rfl
  have hcutRed : errorNewDepth - redZoneDepth = 144 := rfl
  have hcutDrop : errorNewDepth - dropDepth = 128 := rfl
  have hzero8 : (0 : UInt32).toUInt8 = 0 := rfl
  have hone8 : (1 : UInt32).toUInt8 = 1 := rfl
  have h26 : (26 : UInt32).toNat = 26 := rfl
  have hdataLen : dataBytes.length = 920 := by rw [hdataLength]; rfl
  have hf14 : sp - 16 + UInt32.ofNat 14 = sp - 16 + 14 := rfl
  have hf15 : sp - 16 + (14 : UInt32) + UInt32.ofNat 1 = sp - 16 + 15 :=
    frame_offset (sp - 16) 14 1 15 rfl
  have hf14Nat : (sp - 16 + (14 : UInt32)).toNat = (sp - 16).toNat + 14 :=
    Slices.byteOffset_toNat (sp - 16) 14 (by omega)
  have hf15Nat : (sp - 16 + (15 : UInt32)).toNat = (sp - 16).toNat + 15 :=
    Slices.byteOffset_toNat (sp - 16) 15 (by omega)
  have hs14 : (sp - 16 + (14 : UInt32)).toNat
      = (sp - 16).toNat + (14 : UInt32).toNat := by rw [hf14Nat]; rfl
  have hs15 : (sp - 16 + (15 : UInt32)).toNat
      = (sp - 16).toNat + (15 : UInt32).toNat := by rw [hf15Nat]; rfl
  have herr8 : errPtr + UInt32.ofNat 8 = errPtr + 8 := rfl
  have herrZero : errPtr + (0 : UInt32) = errPtr := by simp
  have herr8Nat : (errPtr + (8 : UInt32)).toNat = errPtr.toNat + 8 :=
    Slices.byteOffset_toNat errPtr 8 (by omega)
  have hout8 : out + UInt32.ofNat 8 = out + 8 := rfl
  have houtZero : out + (0 : UInt32) = out := by simp
  have hout8Nat : (out + (8 : UInt32)).toNat = out.toNat + 8 :=
    Slices.byteOffset_toNat out 8 (by omega)
  have houtLow8 : (outBefore.take 8).length = 8 := by
    rw [List.length_take]; omega
  have houtHigh8 : (outBefore.drop 8).length = 8 := by
    rw [List.length_drop]; omega
  have hlow8Length :
      (WordCodec.u32le.serialize [errWord0, errWord1]).length = 8 := by simp
  have hhigh8Length :
      (WordCodec.u32le.serialize [errWord2, errWord3]).length = 8 := by simp
  have htriLength :
      (WordCodec.u32le.serialize [errWord0, errWord1, errWord2]).length
        = 12 := by simp
  have hafterLength :
      (WordCodec.u32le.serialize [errWord0, errWord1, errWord2]
        ++ WordCodec.u32le.serialize [errWord3]).length = 16 := by simp
  have hboundE0 : errPtr.toNat + 0 + 8 ≤ UInt32.size := by omega
  have hboundE8 : errPtr.toNat + 8 + 8 ≤ UInt32.size := by omega
  have hboundO0 : out.toNat + 0 + 8 ≤ UInt32.size := by omega
  have hboundO8 : out.toNat + 8 + 8 ≤ UInt32.size := by omega
  have hwordE0 : errPtr.toNat + 8 < UInt32.size := by omega
  have hwordE8 : (errPtr + 8).toNat + 8 < UInt32.size := by
    rw [herr8Nat]; omega
  have hwordO0 : out.toNat + 8 < UInt32.size := by omega
  have hwordO8 : (out + 8).toNat + 8 < UInt32.size := by
    rw [hout8Nat]; omega
  have hea0 := offset_facts64 errPtr 0 0 rfl hboundE0
  have hea8 := offset_facts64 errPtr 8 8 rfl hboundE8
  have hoa0 := offset_facts64 out 0 0 rfl hboundO0
  have hoa8 := offset_facts64 out 8 8 rfl hboundO8
  -- the error, as one slice again
  ihave Herr : Slices.ByteSlice 0 errPtr
      (WordCodec.u32le.serialize [errWord0, errWord1, errWord2, errWord3]) $$
      [Herr]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Herr
  -- the static byte at 1049136 and the static message at 1049137
  have hseg560 : entryStackTop + UInt32.ofNat 560 = 1049136 := by decide
  have hseg561 : (1049136 : UInt32) + UInt32.ofNat 1 = 1049137 := by decide
  have hseg587 : (1049137 : UInt32) + UInt32.ofNat 26 = 1049163 := by decide
  have htagLength : ((dataBytes.drop 560).take 1).length = 1 := by
    rw [List.length_take, List.length_drop]; omega
  have hmsgLength :
      (((dataBytes.drop 560).drop 1).take 26).length = (26 : UInt32).toNat := by
    rw [List.length_take, List.length_drop, List.length_drop]; omega
  ihave ⟨Hpre, Hrest⟩ :=
    ByteSlice_cut entryStackTop dataBytes 560 (by omega) $$ Hdata
  isimp only [hseg560] at Hrest
  ihave ⟨Htag, Hrest2⟩ :=
    ByteSlice_cut 1049136 (dataBytes.drop 560) 1
      (by rw [List.length_drop]; omega) $$ Hrest
  isimp only [hseg561] at Hrest2
  ihave ⟨Hmsg, Hpost⟩ :=
    ByteSlice_cut 1049137 ((dataBytes.drop 560).drop 1) 26
      (by rw [List.length_drop, List.length_drop]; omega) $$ Hrest2
  isimp only [hseg587] at Hpost
  obtain ⟨tagByte, htagShape⟩ := List.length_eq_one_iff.mp htagLength
  isimp only [htagShape] at Htag
  have hdatajoin :
      dataBytes.take 560 ++ ([tagByte]
        ++ (((dataBytes.drop 560).drop 1).take 26
          ++ ((dataBytes.drop 560).drop 1).drop 26))
        = dataBytes := by
    rw [← htagShape, List.take_append_drop, List.take_append_drop,
      List.take_append_drop]
  -- the stack splits into the region of the callees and the own frame
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp func49Depth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop errorNewDepth) hbase16 $$ Hframe
  have hdeadLength : ((below.drop errorNewDepth).take 14).length = 14 := by
    rw [List.length_take]; omega
  have h14Length :
      (((below.drop errorNewDepth).drop 14).take 1).length = 1 := by
    rw [List.length_take, List.length_drop]; omega
  have h15Length :
      (((below.drop errorNewDepth).drop 14).drop 1).length = 1 := by
    rw [List.length_drop, List.length_drop]; omega
  ihave ⟨Hdead, Hlast2⟩ :=
    ByteSlice_cut (sp - 16) (below.drop errorNewDepth) 14 (by omega) $$ Hframe
  isimp only [hf14] at Hlast2
  ihave ⟨Hb14, Hb15⟩ :=
    ByteSlice_cut (sp - 16 + 14) ((below.drop errorNewDepth).drop 14) 1
      (by rw [List.length_drop]; omega) $$ Hlast2
  isimp only [hf15] at Hb15
  obtain ⟨old14, h14Shape⟩ := List.length_eq_one_iff.mp h14Length
  obtain ⟨old15, h15Shape⟩ := List.length_eq_one_iff.mp h15Length
  isimp only [h14Shape] at Hb14
  isimp only [h15Shape] at Hb15
  ihave ⟨%h14Bound, Hbyte14⟩ :=
    (Slices.ByteSlice_singleton 0 (sp - 16 + 14) old14).mp $$ Hb14
  ihave ⟨%h15Bound, Hbyte15⟩ :=
    (Slices.ByteSlice_singleton 0 (sp - 16 + 15) old15).mp $$ Hb15
  have hframejoin :
      (below.drop errorNewDepth).take 14 ++ ([old14] ++ [old15])
        = below.drop errorNewDepth := by
    rw [← h14Shape, ← h15Shape, List.take_append_drop, List.take_append_drop]
  -- `local 2 := sp - 16`, and the body commits it
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  -- `[frame + 15] := 0` and then `:= 1`
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 15) old15
    hs15 with Hbyte15
  isimp only [hzero8] at Hbyte15
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 15) 0
    hs15 with Hbyte15
  isimp only [hone8] at Hbyte15
  -- the red zone of the kind-byte read
  ihave ⟨Hdeep, Hredzone⟩ :=
    frame_split (sp - 16) errorNewDepth redZoneDepth (below.take errorNewDepth)
      (by decide) $$ Hlower
  isimp only [hcutRed] at Hredzone
  ihave Hsp : StackPointer (sp - 16) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  -- `call 53`: the kind byte of the error
  wasm_twp_pures [twp_localGet twp_localGet]
  iclose_map_runtime Hruntime with Hmodule Henv
  have Hkind : Func50Spec (hlc := hlc) :=
    Project.RustHashMap.Func50Proof.func50_correct
  unfold Func50Spec CallContract callExpr at Hkind
  simp only [List.cons_append, List.nil_append] at Hkind
  iapply Hkind (sp := sp - 16) (errPtr := errPtr) (word0 := errWord0)
    (word1 := errWord1) (word2 := errWord2) (word3 := errWord3)
    (below := (below.take errorNewDepth).drop 144)
    (callerLocals :=
      { params := [.i32 out, .i32 errPtr], locals := [.i32 (sp - 16)],
        values := [] })
    (stack := [.i32 (sp - 16)])
  isplitl_exacts [Hruntime Hsp Hredzone Herr]
  isplitl_pureexact ⟨by omega, by omega⟩
  iintro %kindByte %redAfter Hruntime Hsp Hredzone Herr
  isimp only [ResumeWP, resumeExpr, List.cons_append, List.nil_append]
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  -- `[frame + 14] := kind byte`
  wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 14) old14
    hs14 with Hbyte14
  isimp only [UInt8.toUInt8_toUInt32] at Hbyte14
  -- give the red zone back to the deep region
  ihave ⟨Hdeep, %hdeepLength⟩ :=
    StackBelow_length (sp - 16 - UInt32.ofNat redZoneDepth)
      (errorNewDepth - redZoneDepth)
      ((below.take errorNewDepth).take (errorNewDepth - redZoneDepth)) $$ Hdeep
  ihave Hlower :=
    frame_join (sp - 16) errorNewDepth redZoneDepth
      ((below.take errorNewDepth).take (errorNewDepth - redZoneDepth))
      redAfter hdeepLength (by decide) $$ [Hdeep Hredzone]
  · isplitl_exact Hdeep
    · iexact Hredzone
  -- the two blocks of the comparison
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (14 : UInt32) + (sp - 16) = sp - 16 + 14 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_const]
  ihave Hb14 :=
    (Slices.ByteSlice_singleton 0 (sp - 16 + 14) kindByte).mpr $$ [Hbyte14]
  · isplitl_pureexact h14Bound
    iexact Hbyte14
  -- `call 54`: compare the kind byte with the static byte
  iclose_map_runtime Hruntime with Hmodule Henv
  have Hcmp : Func51Spec (hlc := hlc) :=
    Project.RustHashMap.Func51Proof.func51_correct
  unfold Func51Spec CallContract callExpr at Hcmp
  simp only [List.cons_append, List.nil_append] at Hcmp
  iapply Hcmp (ptrA := sp - 16 + 14) (ptrB := 1049136) (byteA := kindByte)
    (byteB := tagByte)
    (callerLocals :=
      { params := [.i32 out, .i32 errPtr], locals := [.i32 (sp - 16)],
        values := [] })
    (stack := [])
  isplitl_exacts [Hruntime Hb14 Htag]
  iintro Hruntime Hb14 Htag
  isimp only [ResumeWP, resumeExpr, List.append_nil, List.nil_append]
  by_cases hsame : kindByte = tagByte
  · -- the bytes are equal: build a new error and drop the old one
    rw [if_pos hsame]
    wasm_twp_pures [twp_const twp_and] using [and_one_one]
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_pures [twp_localGet twp_const twp_const twp_const]
    have Hnew : Func52Spec (hlc := hlc) :=
      Project.RustHashMap.Func52Proof.func52_correct
    unfold Func52Spec CallContract callExpr at Hnew
    simp only [List.cons_append, List.nil_append] at Hnew
    iapply Hnew (sp := sp - 16) (out := out) (kind := 12) (msgPtr := 1049137)
      (msgLen := 26) (heapId := heapId) (outBefore := outBefore)
      (below := (below.take errorNewDepth).take (errorNewDepth - redZoneDepth)
        ++ redAfter)
      (msgBytes := ((dataBytes.drop 560).drop 1).take 26)
      (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        { params := [.i32 out, .i32 errPtr], locals := [.i32 (sp - 16)],
          values := [] })
      (stack := [])
    isplitl_exacts [Hruntime Hsp Hlower Hout Hmsg Hbump Hstreams]
    isplitl_pureexact
      ⟨houtLength, by omega, by omega, by decide, by decide, hmsgLength⟩
    isplit
    · iintro %word0 %word1 %word2 %word3 %below' %storedCursor' %frontier'
        %history'
      iintro Hruntime Hsp Hlower Hout Hmsg Hbump Hstreams %hword0
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
      -- the flag is still 1, so the second block runs the drop
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load8U_gen (address := sp - 16) (offset := 15) 1
        hs15 with Hbyte15
      wasm_twp_pures [twp_const twp_and] using [byte_and_one_one]
      iapply twp_eqz (result := 0) (by decide)
      iapply twp_brIfZero
      -- the drop takes the first twelve bytes of the error
      ihave ⟨Herrlow, Herrhigh⟩ :=
        (Slices.ByteSlice_append 0 errPtr
          (WordCodec.u32le.serialize [errWord0, errWord1, errWord2])
          (WordCodec.u32le.serialize [errWord3])).mp $$ [Herr]
      · wasm_serialize_norm at Herr
        isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
          List.append_nil, List.append_assoc]
        iexact Herr
      isimp only [htriLength] at Herrhigh
      ihave ⟨Hdeep, Hdroptop⟩ :=
        frame_split (sp - 16) errorNewDepth dropDepth below' (by decide) $$
          Hlower
      isimp only [hcutDrop] at Hdroptop
      wasm_twp_pures [twp_localGet]
      iclose_map_runtime Hruntime with Hmodule Henv
      have Hdrop : Func35Spec (hlc := hlc) :=
        Project.RustHashMap.Func35Proof.func35_correct
      unfold Func35Spec CallContract callExpr at Hdrop
      simp only [List.cons_append, List.nil_append] at Hdrop
      iapply Hdrop (sp := sp - 16) (record := errPtr) (capacity := errWord0)
        (ptr := errWord1) (length := errWord2)
        (below := below'.drop 128)
        (callerLocals :=
          { params := [.i32 out, .i32 errPtr], locals := [.i32 (sp - 16)],
            values := [] })
        (stack := [])
      isplitl_exacts [Hruntime Hsp Hdroptop Herrlow]
      isplitl_pureexact ⟨by omega, by omega⟩
      iintro %dropAfter Hruntime Hsp Hdroptop Herrlow
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
      -- restore the stack pointer and return
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      isimp only [StackPointer] at Hsp
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [show (16 : UInt32) + (sp - 16) = sp by
        rw [UInt32.add_comm, UInt32.sub_add_cancel]]
      wasm_twp_rebind twp_globalSet with Hsp
      wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
      -- the error storage, as one slice again
      ihave Herr :=
        ByteSlice_glue errPtr
          (WordCodec.u32le.serialize [errWord0, errWord1, errWord2])
          (WordCodec.u32le.serialize [errWord3]) 12 htriLength $$
          [Herrlow Herrhigh]
      · isplitl_exact Herrlow
        · iexact Herrhigh
      -- the stack, as one region again
      ihave ⟨Hdeep, %hdeepLength2⟩ :=
        StackBelow_length (sp - 16 - UInt32.ofNat dropDepth)
          (errorNewDepth - dropDepth)
          (below'.take (errorNewDepth - dropDepth)) $$ Hdeep
      ihave Hlower :=
        frame_join (sp - 16) errorNewDepth dropDepth
          (below'.take (errorNewDepth - dropDepth)) dropAfter hdeepLength2
          (by decide) $$ [Hdeep Hdroptop]
      · isplitl_exact Hdeep
        · iexact Hdroptop
      ihave Hb15 :=
        (Slices.ByteSlice_singleton 0 (sp - 16 + 15) 1).mpr $$ [Hbyte15]
      · isplitl_pureexact h15Bound
        iexact Hbyte15
      ihave Hlast2 :=
        ByteSlice_glue (sp - 16 + 14) [kindByte] [1] 1 rfl $$ [Hb14 Hb15]
      · isplitl_exact Hb14
        · irw_exact [hf15] with Hb15
      ihave Hframe :=
        ByteSlice_glue (sp - 16) ((below.drop errorNewDepth).take 14)
          ([kindByte] ++ [1]) 14 hdeadLength $$ [Hdead Hlast2]
      · isplitl_exact Hdead
        · irw_exact [hf14] with Hlast2
      ihave Htop16 :=
        StackBelow_intro sp (sp - 16) 16
          ((below.drop errorNewDepth).take 14 ++ ([kindByte] ++ [1]))
          (by rw [List.length_append, hdeadLength]; rfl) hbase16 $$ Hframe
      ihave ⟨Hlower, %hlowerLength⟩ :=
        StackBelow_length (sp - 16) errorNewDepth
          (below'.take (errorNewDepth - dropDepth) ++ dropAfter) $$ Hlower
      isimp only [← hbase16] at Hlower
      ihave Hbelow :=
        frame_join sp func49Depth 16
          (below'.take (errorNewDepth - dropDepth) ++ dropAfter)
          ((below.drop errorNewDepth).take 14 ++ ([kindByte] ++ [1]))
          (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop16]
      · isplitl [Hlower]
        · rw [hcut]
          iexact Hlower
        iexact Htop16
      ihave Hsp : StackPointer sp $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      -- the data segment, as one slice again
      ihave Htag :=
        (Slices.ByteSlice_singleton 0 1049136 tagByte).mpr $$ [Htag]
      · icases (Slices.ByteSlice_singleton 0 1049136 tagByte).mp $$ [Htag]
          with ⟨%hb, Hpt⟩
        · iexact Htag
        isplitl_pureexact hb
        iexact Hpt
      ihave Hrest2 :=
        ByteSlice_glue 1049137 (((dataBytes.drop 560).drop 1).take 26)
          (((dataBytes.drop 560).drop 1).drop 26) 26 (by omega) $$
          [Hmsg Hpost]
      · isplitl_exact Hmsg
        · irw_exact [hseg587] with Hpost
      ihave Hrest :=
        ByteSlice_glue 1049136 [tagByte]
          (((dataBytes.drop 560).drop 1).take 26
            ++ ((dataBytes.drop 560).drop 1).drop 26) 1 rfl $$ [Htag Hrest2]
      · isplitl_exact Htag
        · irw_exact [hseg561] with Hrest2
      ihave Hdata :=
        ByteSlice_glue entryStackTop (dataBytes.take 560)
          ([tagByte]
            ++ (((dataBytes.drop 560).drop 1).take 26
              ++ ((dataBytes.drop 560).drop 1).drop 26)) 560
          (by rw [List.length_take]; omega) $$ [Hpre Hrest]
      · isplitl_exact Hpre
        · irw_exact [hseg560] with Hrest
      isimp only [hdatajoin] at Hdata
      iclose_map_runtime Hruntime with Hmodule Henv
      ihave Hnormal := BI.and_elim_l $$ Hcont
      isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
      ihave Hnormal := Hnormal $$ %word0 %word1 %word2 %word3
        %(WordCodec.u32le.serialize [errWord0, errWord1, errWord2]
          ++ WordCodec.u32le.serialize [errWord3])
        %((below'.take (errorNewDepth - dropDepth) ++ dropAfter)
          ++ ((below.drop errorNewDepth).take 14 ++ ([kindByte] ++ [1])))
        %storedCursor' %frontier' %history'
      wasm_serialize_norm at Hout
      iapply Hnormal $$ Hruntime Hsp Hbelow Hout Herr Hdata Hbump Hstreams
        %⟨hword0, hafterLength⟩
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams
  · -- the bytes differ: copy the error into the output slot
    rw [if_neg hsame]
    wasm_twp_pures [twp_const twp_and] using [and_zero_one]
    iapply twp_brIfZero
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    -- `[frame + 15] := 0`
    wasm_twp_pures [twp_localGet twp_const]
    wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 15) 1
      hs15 with Hbyte15
    isimp only [hzero8] at Hbyte15
    -- the two block moves
    ihave ⟨Herrlow, Herrhigh⟩ :=
      (Slices.ByteSlice_append 0 errPtr
        (WordCodec.u32le.serialize [errWord0, errWord1])
        (WordCodec.u32le.serialize [errWord2, errWord3])).mp $$ [Herr]
    · wasm_serialize_norm at Herr
      isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
        List.append_nil, List.append_assoc]
      iexact Herr
    isimp only [hlow8Length, herr8] at Herrhigh
    ihave ⟨Houtlow, Houthigh⟩ := ByteSlice_cut out outBefore 8 (by omega) $$ Hout
    isimp only [hout8] at Houthigh
    ihave Herrhighword :=
      ByteSlice_as_word (errPtr + 8) (errPtr + 8)
        (WordCodec.u32le.serialize [errWord2, errWord3]) rfl hhigh8Length $$
        Herrhigh
    ihave Houthighword :=
      ByteSlice_as_word (out + 8) (out + 8) (outBefore.drop 8) rfl
        houtHigh8 $$ Houthigh
    wasm_twp_block_move
      (errPtr, 8, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [errWord2, errWord3]), hea8)
      (out, 8, Wasm.RustStd.HashMap.Table.groupWord (outBefore.drop 8), hoa8)
      with Herrhighword Houthighword
    ihave Herrlowword :=
      ByteSlice_as_word errPtr (errPtr + 0)
        (WordCodec.u32le.serialize [errWord0, errWord1]) herrZero
        hlow8Length $$ Herrlow
    ihave Houtlowword :=
      ByteSlice_as_word out (out + 0) (outBefore.take 8) houtZero
        houtLow8 $$ Houtlow
    wasm_twp_block_move
      (errPtr, 0, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [errWord0, errWord1]), hea0)
      (out, 0, Wasm.RustStd.HashMap.Table.groupWord (outBefore.take 8), hoa0)
      with Herrlowword Houtlowword
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- the flag is 0, so the second block runs no drop
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load8U_gen (address := sp - 16) (offset := 15) 0
      hs15 with Hbyte15
    wasm_twp_pures [twp_const twp_and] using [byte_and_zero_one]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- restore the stack pointer and return
    isimp only [StackPointer] at Hsp
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- the output slot and the error, as byte slices again
    ihave Houtlow :=
      ByteSlice_of_word out (out + 0)
        (WordCodec.u32le.serialize [errWord0, errWord1]) houtZero hlow8Length
        hwordO0 $$ Houtlowword
    ihave Houthigh :=
      ByteSlice_of_word (out + 8) (out + 8)
        (WordCodec.u32le.serialize [errWord2, errWord3]) rfl hhigh8Length
        hwordO8 $$ Houthighword
    ihave Hout :=
      ByteSlice_glue out (WordCodec.u32le.serialize [errWord0, errWord1])
        (WordCodec.u32le.serialize [errWord2, errWord3]) 8 hlow8Length $$
        [Houtlow Houthigh]
    · isplitl_exact Houtlow
      · irw_exact [hout8] with Houthigh
    ihave Herrlow :=
      ByteSlice_of_word errPtr (errPtr + 0)
        (WordCodec.u32le.serialize [errWord0, errWord1]) herrZero hlow8Length
        hwordE0 $$ Herrlowword
    ihave Herrhigh :=
      ByteSlice_of_word (errPtr + 8) (errPtr + 8)
        (WordCodec.u32le.serialize [errWord2, errWord3]) rfl hhigh8Length
        hwordE8 $$ Herrhighword
    ihave Herr :=
      ByteSlice_glue errPtr (WordCodec.u32le.serialize [errWord0, errWord1])
        (WordCodec.u32le.serialize [errWord2, errWord3]) 8 hlow8Length $$
        [Herrlow Herrhigh]
    · isplitl_exact Herrlow
      · irw_exact [herr8] with Herrhigh
    -- the frame and the stack, as one region again
    ihave Hb15 :=
      (Slices.ByteSlice_singleton 0 (sp - 16 + 15) 0).mpr $$ [Hbyte15]
    · isplitl_pureexact h15Bound
      iexact Hbyte15
    ihave Hlast2 :=
      ByteSlice_glue (sp - 16 + 14) [kindByte] [0] 1 rfl $$ [Hb14 Hb15]
    · isplitl_exact Hb14
      · irw_exact [hf15] with Hb15
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop errorNewDepth).take 14)
        ([kindByte] ++ [0]) 14 hdeadLength $$ [Hdead Hlast2]
    · isplitl_exact Hdead
      · irw_exact [hf14] with Hlast2
    ihave Htop16 :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop errorNewDepth).take 14 ++ ([kindByte] ++ [0]))
        (by rw [List.length_append, hdeadLength]; rfl) hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) errorNewDepth
        ((below.take errorNewDepth).take (errorNewDepth - redZoneDepth)
          ++ redAfter) $$ Hlower
    isimp only [← hbase16] at Hlower
    ihave Hbelow :=
      frame_join sp func49Depth 16
        ((below.take errorNewDepth).take (errorNewDepth - redZoneDepth)
          ++ redAfter)
        ((below.drop errorNewDepth).take 14 ++ ([kindByte] ++ [0]))
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop16]
    · isplitl [Hlower]
      · rw [hcut]
        iexact Hlower
      iexact Htop16
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    -- the data segment, as one slice again
    ihave Hrest2 :=
      ByteSlice_glue 1049137 (((dataBytes.drop 560).drop 1).take 26)
        (((dataBytes.drop 560).drop 1).drop 26) 26 (by omega) $$ [Hmsg Hpost]
    · isplitl_exact Hmsg
      · irw_exact [hseg587] with Hpost
    ihave Hrest :=
      ByteSlice_glue 1049136 [tagByte]
        (((dataBytes.drop 560).drop 1).take 26
          ++ ((dataBytes.drop 560).drop 1).drop 26) 1 rfl $$ [Htag Hrest2]
    · isplitl_exact Htag
      · irw_exact [hseg561] with Hrest2
    ihave Hdata :=
      ByteSlice_glue entryStackTop (dataBytes.take 560)
        ([tagByte]
          ++ (((dataBytes.drop 560).drop 1).take 26
            ++ ((dataBytes.drop 560).drop 1).drop 26)) 560
        (by rw [List.length_take]; omega) $$ [Hpre Hrest]
    · isplitl_exact Hpre
      · irw_exact [hseg560] with Hrest
    isimp only [hdatajoin] at Hdata
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
    ihave Hnormal := Hnormal $$ %errWord0 %errWord1 %errWord2 %errWord3
      %(WordCodec.u32le.serialize [errWord0, errWord1]
        ++ WordCodec.u32le.serialize [errWord2, errWord3])
      %(((below.take errorNewDepth).take (errorNewDepth - redZoneDepth)
        ++ redAfter)
        ++ ((below.drop errorNewDepth).take 14 ++ ([kindByte] ++ [0])))
      %storedCursor %frontier %history
    wasm_serialize_norm at Hout
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Herr Hdata Hbump Hstreams
      %⟨herrWord0, by simp⟩

end Project.RustHashMap.Func49Proof
