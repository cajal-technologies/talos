import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func54Proof
import CodeLib.RustStd.HashMap.TableMem

/-!
# Proof of the forwarder above the `String` builder

Local `func40` (absolute index 43) keeps a 16-byte frame.  It calls
`func 57` with the frame slot at `frame + 4` as the twelve-byte output
slot, and then moves the twelve result bytes to the output slot of its
own caller.

The move is two instructions.  The third word goes through `i32.load`
and `i32.store`.  The first two words go through `i64.load offset=4` and
`i64.store`, and the proof treats that pair as an opaque eight-byte block
move: the eight bytes become one owned `u64` through
`Project.RustHashMap.FrameCells.ByteSlice_as_word`, and the value of that
word never enters a goal.

The first four bytes of the frame are dead.  The body writes them never
and reads them never.

The theorem is unconditional, because
`Project.RustHashMap.Func54Proof.func54_correct` is.
-/

namespace Project.RustHashMap.Func40Proof

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
open scoped Wasm.SmallStep.Outcome

private theorem func40_index :
    Project.RustHashMap.«module».funcs[40]? =
      some Project.RustHashMap.func40Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func40_correct [WasmSmallStepGS hlc Universal.State] :
    Func40Spec (hlc := hlc) := by
  unfold Func40Spec CallContract callExpr
  intro sp out msgPtr msgLen heapId outBefore below msgBytes storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmsg, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hmsgPos, hmsgLe, hmsgLength⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 43
      Project.RustHashMap.func40Def (by decide) func40_index with Hmodule
  simp [Project.RustHashMap.func40Def, Project.RustHashMap.func40,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  -- arithmetic on the frame base
  have hdepth40 : func40Depth = 144 := rfl
  have hdepth54 : func54Depth = 128 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (144 : Nat) ≤ sp.toNat := by rw [hdepth40] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := by rfl
  have hcut : func40Depth - 16 = func54Depth := rfl
  have h4lit : sp - 16 + UInt32.ofNat 4 = sp - 16 + 4 := rfl
  have hslotNat : (sp - 16 + (4 : UInt32)).toNat = (sp - 16).toNat + 4 :=
    Slices.byteOffset_toNat (sp - 16) 4 (by omega)
  -- the frame splits into the region the callee wants and the own 16 bytes
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp func40Depth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop func54Depth) hbase16 $$ Hframe
  ihave ⟨Hdead, Hslot⟩ :=
    ByteSlice_cut (sp - 16) (below.drop func54Depth) 4 (by omega) $$ Hframe
  isimp only [h4lit] at Hslot
  -- the call
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (4 : UInt32) + (sp - 16) = sp - 16 + 4 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_localGet twp_localGet]
  have Hleaf : Func54Spec (hlc := hlc) :=
    Project.RustHashMap.Func54Proof.func54_correct
  unfold Func54Spec CallContract callExpr at Hleaf
  simp only [List.cons_append, List.nil_append] at Hleaf
  iapply Hleaf (sp := sp - 16) (out := sp - 16 + 4) (msgPtr := msgPtr)
    (msgLen := msgLen) (heapId := heapId)
    (outBefore := (below.drop func54Depth).drop 4)
    (below := below.take func54Depth) (msgBytes := msgBytes)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 msgPtr, .i32 msgLen]
        locals := [.i32 (sp - 16)]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl [Hsp]
  · unfold StackPointer
    iexact Hsp
  isplitl_exacts [Hlower Hslot Hmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨by rw [List.length_drop, hframeLength], by omega, by omega, hmsgPos,
      hmsgLe, hmsgLength⟩
  isplit
  · iintro %ptr %blockId %lower' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hlower Hslot Hmsg Hbump Hblock Hstreams
    -- `Hslot` is the twelve result bytes at `frame + 4`
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    isimp only [StackPointer] at Hsp
    -- the two views of the result: eight bytes as a word, four as a cell
    have hlen8 : (WordCodec.u32le.serialize [msgLen, ptr]).length = 8 := by simp
    have hsplit3 : WordCodec.u32le.serialize [msgLen, ptr, msgLen]
        = WordCodec.u32le.serialize [msgLen, ptr]
          ++ WordCodec.u32le.serialize [msgLen] :=
      WordCodec.serialize_append WordCodec.u32le [msgLen, ptr] [msgLen]
    have haddr12 : sp - 16 + (4 : UInt32) + UInt32.ofNat 8 = sp - 16 + 12 :=
      frame_offset (sp - 16) 4 8 12 rfl
    ihave ⟨Hframelow, Hframehigh⟩ :=
      (Slices.ByteSlice_append 0 (sp - 16 + 4)
        (WordCodec.u32le.serialize [msgLen, ptr])
        (WordCodec.u32le.serialize [msgLen])).mp $$ [Hslot]
    · irw_exact [← hsplit3] with Hslot
    isimp only [hlen8, haddr12] at Hframehigh
    -- the address facts
    have hfa4 := offset_facts64 (sp - 16) 4 4 rfl (by omega)
    obtain ⟨hf12, hf12_1, hf12_2, hf12_3⟩ :=
      offset_facts (sp - 16) 12 12 rfl (by omega)
    have hoa0 := offset_facts64 out 0 0 rfl (by omega)
    obtain ⟨hout8, hout8_1, hout8_2, hout8_3⟩ :=
      offset_facts out 8 8 rfl (by omega)
    -- `[out + 8] := [frame + 12]`
    ihave Hframecells :=
      cells_of_ByteSlice (sp - 16 + 12) [msgLen] $$ Hframehigh
    isimp only [arrayAt] at Hframecells
    icases Hframecells with ⟨Hframecell, _Hframenil⟩
    have h8out : out + UInt32.ofNat 8 = out + 8 := rfl
    ihave ⟨Houtlow, Houthigh⟩ :=
      ByteSlice_cut out outBefore 8 (by omega) $$ Hout
    isimp only [h8out] at Houthigh
    ihave ⟨%houtHighCells, Houtharray⟩ :=
      ByteSlice_as_cells (out + 8) (outBefore.drop 8) 1
        (by rw [List.length_drop, houtLength]) $$ Houthigh
    obtain ⟨outWord3, houtHighShape⟩ := List.length_eq_one_iff.mp houtHighCells
    isimp only [houtHighShape, arrayAt] at Houtharray
    icases Houtharray with ⟨Houthighcell, _Houthighnil⟩
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12) msgLen
      hf12 hf12_1 hf12_2 hf12_3 with Hframecell
    wasm_twp_rebind twp_store32 (address := out) (offset := 8) outWord3
      hout8 hout8_1 hout8_2 hout8_3 with Houthighcell
    -- `[out + 0 .. 8] := [frame + 4 .. 12]`, an opaque block move
    have houtZero : out + (0 : UInt32) = out := by
      simp
    have houtLow8 : (outBefore.take 8).length = 8 := by
      simp [houtLength]
    ihave Hframeword :=
      ByteSlice_as_word (sp - 16 + 4) (sp - 16 + 4)
        (WordCodec.u32le.serialize [msgLen, ptr]) rfl hlen8 $$ Hframelow
    ihave Houtword :=
      ByteSlice_as_word out (out + 0) (outBefore.take 8) houtZero
        houtLow8 $$ Houtlow
    wasm_twp_block_move
      (sp - 16, 4, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [msgLen, ptr]), hfa4)
      (out, 0, Wasm.RustStd.HashMap.Table.groupWord (outBefore.take 8), hoa0)
      with Hframeword Houtword
    -- restore the stack pointer and return
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- put the caller's output slot back together
    ihave Houtlow :=
      ByteSlice_of_word out (out + 0)
        (WordCodec.u32le.serialize [msgLen, ptr]) houtZero hlen8
        (by omega) $$ Houtword
    ihave Houthigharray : arrayAt 0 (out + 8) [msgLen] $$ [Houthighcell]
    · isimp only [arrayAt]
      iframe Houthighcell
    ihave Houthigh :=
      ByteSlice_of_cells (out + 8) [msgLen]
        (by simp only [List.length_cons, List.length_nil,
              show (out + (8 : UInt32)).toNat = out.toNat + 8 from
                Slices.byteOffset_toNat out 8 (by omega)]
            omega) $$ Houthigharray
    ihave Hout :=
      ByteSlice_glue out (WordCodec.u32le.serialize [msgLen, ptr])
        (WordCodec.u32le.serialize [msgLen]) 8 hlen8 $$
        [Houtlow Houthigh]
    · isplitl_exact Houtlow
      · irw_exact [h8out] with Houthigh
    wasm_serialize_norm at Hout
    -- put the frame back together
    ihave Hframelow :=
      ByteSlice_of_word (sp - 16 + 4) (sp - 16 + 4)
        (WordCodec.u32le.serialize [msgLen, ptr]) rfl hlen8
        (by omega) $$ Hframeword
    ihave Hframehigharray : arrayAt 0 (sp - 16 + 12) [msgLen] $$ [Hframecell]
    · isimp only [arrayAt]
      iframe Hframecell
    ihave Hframehigh :=
      ByteSlice_of_cells (sp - 16 + 12) [msgLen]
        (by simp only [List.length_cons, List.length_nil,
              show (sp - 16 + (12 : UInt32)).toNat = (sp - 16).toNat + 12 from
                Slices.byteOffset_toNat (sp - 16) 12 (by omega)]
            omega) $$ Hframehigharray
    ihave Hslot :=
      ByteSlice_glue (sp - 16 + 4) (WordCodec.u32le.serialize [msgLen, ptr])
        (WordCodec.u32le.serialize [msgLen]) 8 hlen8 $$
        [Hframelow Hframehigh]
    · isplitl_exact Hframelow
      · irw_exact [haddr12] with Hframehigh
    isimp only [← hsplit3] at Hslot
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop func54Depth).take 4)
        (WordCodec.u32le.serialize [msgLen, ptr, msgLen]) 4
        (by simp [hframeLength]) $$ [Hdead Hslot]
    · isplitl_exact Hdead
      · irw_exact [h4lit] with Hslot
    ihave Htop :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop func54Depth).take 4
          ++ WordCodec.u32le.serialize [msgLen, ptr, msgLen])
        (by rw [List.length_append, List.length_take, hframeLength]; simp) hbase16 $$
        Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) func54Depth lower' $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp func40Depth 16 lower'
        ((below.drop func54Depth).take 4
          ++ WordCodec.u32le.serialize [msgLen, ptr, msgLen])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %ptr %blockId
      %(lower' ++ ((below.drop func54Depth).take 4
        ++ WordCodec.u32le.serialize [msgLen, ptr, msgLen]))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hmsg Hbump Hblock Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Func40Proof
