import Project.RustHashMap.Func43Proof
import Project.RustHashMap.Func44Proof

/-!
# Proof of the buffer free of the decode-error subtree

Local `func42` (absolute index 45) frees the message buffer of the error.
The arguments in source order are the buffer record, the alignment and the
element size, and the only caller fixes the last two at 1.

The body takes a sixteen-byte frame at WAT lines 9211 to 9216 and asks
absolute `func 46` for the layout into the top twelve bytes of that frame.
It then reads the middle word of the layout.  A zero word means an empty
buffer and the body returns.  A word that is not zero sends the three
layout words to absolute `func 47`, which frees nothing.

`Func43Spec` leaves the layout abstract, so both arms of the `select` at
WAT lines 9233 to 9238 are live.

The theorem is unconditional, because `func43_correct` and
`func44_correct` are.
-/

namespace Project.RustHashMap.Func42Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func42_index :
    Project.RustHashMap.«module».funcs[42]? =
      some Project.RustHashMap.func42Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The free gives the stack region and the record back to the caller. -/
theorem func42_correct [WasmSmallStepGS hlc Universal.State] :
    Func42Spec (hlc := hlc) := by
  unfold Func42Spec CallContract callExpr
  intro sp record capacity ptr below callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 45
      Project.RustHashMap.func42Def (by decide) func42_index with Hmodule
  simp [Project.RustHashMap.func42Def, Project.RustHashMap.func42,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  -- the address facts of the frame
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hrz : redZoneDepth = 16 := rfl
  have hdd : dropDepth = 32 := rfl
  have hspNat : (32 : Nat) ≤ sp.toNat := hspLow
  have h4nat : (4 : UInt32).toNat = 4 := rfl
  have h8nat : (8 : UInt32).toNat = 8 := rfl
  have h12nat : (12 : UInt32).toNat = 12 := rfl
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := by rfl
  have hcut : dropDepth - 16 = redZoneDepth := rfl
  obtain ⟨hf4, hf4_1, hf4_2, hf4_3⟩ :=
    offset_facts (sp - 16) 4 4 (by decide) (by omega)
  obtain ⟨hf8, hf8_1, hf8_2, hf8_3⟩ :=
    offset_facts (sp - 16) 8 8 (by decide) (by omega)
  obtain ⟨hf12, hf12_1, hf12_2, hf12_3⟩ :=
    offset_facts (sp - 16) 12 12 (by decide) (by omega)
  have haddr8 : sp - 16 + 4 + 4 = sp - 16 + 8 := by
    rw [UInt32.add_assoc, show (4 : UInt32) + 4 = 8 from by decide]
  have haddr12 : sp - 16 + 8 + 4 = sp - 16 + 12 := by
    rw [UInt32.add_assoc, show (8 : UInt32) + 4 = 12 from by decide]
  have hslotAddr : sp - 16 + UInt32.ofNat 4 = sp - 16 + 4 := rfl
  -- the frame, committed
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 4 (sp - 16)]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  -- the frame keeps the layout slot; the red zone below it goes to the callee
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp dropDepth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop redZoneDepth) hbase16 $$ Hframe
  ihave ⟨Hhead, Hslot⟩ :=
    ByteSlice_cut (sp - 16) (below.drop redZoneDepth) 4 (by omega) $$ Hframe
  isimp only [hslotAddr] at Hslot
  ihave Hsp : StackPointer (sp - 16) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  have Hlayout : Func43Spec (hlc := hlc) :=
    Project.RustHashMap.Func43Proof.func43_correct
  unfold Func43Spec CallContract callExpr at Hlayout
  simp only [List.cons_append, List.nil_append] at Hlayout
  iapply Hlayout (sp := sp - 16) (out := sp - 16 + 4) (record := record)
    (capacity := capacity) (ptr := ptr)
    (outBefore := (below.drop redZoneDepth).drop 4)
    (below := below.take redZoneDepth)
    (callerLocals :=
      { params := [.i32 record, .i32 1, .i32 1]
        locals := [.i32 (sp - 16), ValueType.i32.zero, ValueType.i32.zero,
          ValueType.i32.zero, ValueType.i32.zero, ValueType.i32.zero]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exacts [Hsp Hlower Hslot Hrecord]
  isplitl_pureexact
    ⟨by rw [List.length_drop, hframeLength], by omega, by omega,
      hrecordNowrap⟩
  iintro %outAfter %lower' Hruntime Hsp Hlower Hslot Hrecord %hafterLength
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [StackPointer] at Hsp
  -- the three layout words
  ihave ⟨%hcellsO, Hslotarray⟩ :=
    ByteSlice_as_cells (sp - 16 + 4) outAfter 3 (by omega) $$ Hslot
  obtain ⟨w0, w1, w2, hshapeO⟩ := three_words _ hcellsO
  isimp only [hshapeO, arrayAt, haddr8, haddr12] at Hslotarray
  icases Hslotarray with ⟨Hw0, Hw1, Hw2, _HnilO⟩
  -- `local 4 := [frame + 8]`, `local 5 := 0`
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 8) w1
    hf8 hf8_1 hf8_2 hf8_3 with Hw1
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_block twp_block twp_const twp_localGet twp_localGet]
  by_cases hw1 : w1 = 0
  · -- the empty buffer: the body frees nothing
    iapply twp_select (selected := Value.i32 0) (by simp [hw1])
    wasm_twp_pures [twp_const twp_and]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
    -- the epilogue restores the stack pointer and rebuilds the region
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    ihave Hslotarray : arrayAt 0 (sp - 16 + 4) [w0, w1, w2] $$ [Hw0 Hw1 Hw2]
    · isimp only [arrayAt, haddr8, haddr12]
      iframe Hw0 Hw1 Hw2
    ihave Hslot :=
      ByteSlice_of_cells (sp - 16 + 4) [w0, w1, w2] (by
        simp only [List.length_cons, List.length_nil]
        omega) $$ Hslotarray
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop redZoneDepth).take 4)
        (WordCodec.u32le.serialize [w0, w1, w2]) 4
        (by simp [hframeLength]) $$ [Hhead Hslot]
    · isplitl_exact Hhead
      · irw_exact [hslotAddr] with Hslot
    ihave Htop :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop redZoneDepth).take 4
          ++ WordCodec.u32le.serialize [w0, w1, w2])
        (by simp [hframeLength]) hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) redZoneDepth lower' $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp dropDepth 16 lower'
        ((below.drop redZoneDepth).take 4
          ++ WordCodec.u32le.serialize [w0, w1, w2])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    wasm_serialize_norm at Hrecord
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    ihave Hcont := Hcont
      $$ %(lower' ++ ((below.drop redZoneDepth).take 4
        ++ WordCodec.u32le.serialize [w0, w1, w2]))
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
    · isplitl_exact Hmodule
      · iexact Henv
  · -- the live buffer: the body sends the layout to the free
    iapply twp_select (selected := Value.i32 1) (by simp [hw1])
    wasm_twp_pures [twp_const twp_and]
    iapply twp_eqz (result := 0) (by decide)
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 4) w0
      hf4 hf4_1 hf4_2 hf4_3 with Hw0
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 8) w1
      hf8 hf8_1 hf8_2 hf8_3 with Hw1
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12) w2
      hf12 hf12_1 hf12_2 hf12_3 with Hw2
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet
      twp_localGet]
    iclose_map_runtime Hruntime with Hmodule Henv
    have Hfree : Func44Spec (hlc := hlc) :=
      Project.RustHashMap.Func44Proof.func44_correct
    unfold Func44Spec CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree (unused := 8 + record) (ptr := w0) (alignment := w1)
      (size := w2)
      (callerLocals :=
        { params := [.i32 record, .i32 1, .i32 1]
          locals := [.i32 (sp - 16), .i32 w1, .i32 0, .i32 w0, .i32 w1,
            .i32 w2]
          values := [] })
      (stack := [])
    isplitl_exact Hruntime
    iintro Hruntime
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    -- the epilogue restores the stack pointer and rebuilds the region
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    ihave Hslotarray : arrayAt 0 (sp - 16 + 4) [w0, w1, w2] $$ [Hw0 Hw1 Hw2]
    · isimp only [arrayAt, haddr8, haddr12]
      iframe Hw0 Hw1 Hw2
    ihave Hslot :=
      ByteSlice_of_cells (sp - 16 + 4) [w0, w1, w2] (by
        simp only [List.length_cons, List.length_nil]
        omega) $$ Hslotarray
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop redZoneDepth).take 4)
        (WordCodec.u32le.serialize [w0, w1, w2]) 4
        (by simp [hframeLength]) $$ [Hhead Hslot]
    · isplitl_exact Hhead
      · irw_exact [hslotAddr] with Hslot
    ihave Htop :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop redZoneDepth).take 4
          ++ WordCodec.u32le.serialize [w0, w1, w2])
        (by simp [hframeLength]) hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) redZoneDepth lower' $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp dropDepth 16 lower'
        ((below.drop redZoneDepth).take 4
          ++ WordCodec.u32le.serialize [w0, w1, w2])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    wasm_serialize_norm at Hrecord
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    ihave Hcont := Hcont
      $$ %(lower' ++ ((below.drop redZoneDepth).take 4
        ++ WordCodec.u32le.serialize [w0, w1, w2]))
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
    · isplitl_exact Hmodule
      · iexact Henv
end Project.RustHashMap.Func42Proof
