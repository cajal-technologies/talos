import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func41Proof

/-!
# Proof of the forwarder above the allocate leaf

Local `func47` (absolute index 50) keeps a 16-byte frame, calls
`func 44` with the top half of that frame as the output slot, and copies
the two result words into the output slot of its own caller.  It has no
branch, so the proof is one call and two word copies.

The theorem is unconditional, because
`Project.RustHashMap.Func41Proof.func41_correct` is.
-/

namespace Project.RustHashMap.Func47Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.ErrorNewContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

private theorem func47_index :
    Project.RustHashMap.«module».funcs[47]? =
      some Project.RustHashMap.func47Def := by rfl

theorem func47_correct [WasmSmallStepGS hlc Universal.State] :
    Func47Spec (hlc := hlc) := by
  unfold Func47Spec CallContract callExpr
  intro sp out unused size heapId outBefore below storedCursor frontier
    history input output raised callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hsizePos, hsizeLe⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 50
      Project.RustHashMap.func47Def (by decide) func47_index with Hmodule
  simp [Project.RustHashMap.func47Def, Project.RustHashMap.func47,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet
    twp_localGet]
  -- The frame is the top 16 bytes; the callee gets the 32 below it.
  have hdepth47 : func47Depth = 48 := rfl
  have hdepth41 : func41Depth = 32 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (48 : Nat) ≤ sp.toNat := by rw [hdepth47] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := by rfl
  have hcut : func47Depth - 16 = func41Depth := rfl
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp func47Depth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop func41Depth) hbase16 $$ Hframe
  ihave ⟨Hhead, Hslot⟩ :=
    ByteSlice_cut (sp - 16) (below.drop func41Depth) 8 (by omega) $$ Hframe
  have hslotAddr : sp - 16 + UInt32.ofNat 8 = 8 + (sp - 16) := by
    rw [UInt32.add_comm]
    rfl
  isimp only [hslotAddr] at Hslot
  have Hleaf : Func41Spec (hlc := hlc) :=
    Project.RustHashMap.Func41Proof.func41_correct
  unfold Func41Spec CallContract callExpr at Hleaf
  simp only [List.cons_append, List.nil_append] at Hleaf
  iapply Hleaf (sp := sp - 16) (out := 8 + (sp - 16)) (size := size)
    (heapId := heapId)
    (outBefore := (below.drop func41Depth).drop 8)
    (below := below.take func41Depth)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 unused, .i32 1, .i32 size]
        locals := [.i32 (sp - 16), .i32 0, ValueType.i32.zero]
        values := [] })
    (stack := [])
  have hslotNat : (8 + (sp - 16)).toNat = sp.toNat - 8 := by
    rw [UInt32.add_comm, show (8 : UInt32) = UInt32.ofNat 8 from rfl,
      Slices.byteOffset_toNat (sp - 16) 8 (by omega)]
    omega
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl [Hsp]
  · unfold StackPointer
    iexact Hsp
  isplitl_exacts [Hlower Hslot Hbump Hstreams]
  isplitl_pureexact
    ⟨by rw [List.length_drop, hframeLength], by omega, by omega, hsizePos,
      hsizeLe⟩
  isplit
  · iintro %ptr %blockId %contents %lower' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hlower Hslot Hbump Hblock Hstreams
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    isimp only [StackPointer] at Hsp
    have hslotAddr' : (8 : UInt32) + (sp - 16) = sp - 16 + 8 := by
      rw [UInt32.add_comm]
    have hslotNat' : (sp - 16 + 8).toNat = sp.toNat - 8 := by
      rw [← hslotAddr']; exact hslotNat
    have haddr12 : sp - 16 + 8 + 4 = sp - 16 + 12 := by
      rw [UInt32.add_assoc, show (8 : UInt32) + 4 = 12 from by decide]
    isimp only [hslotAddr'] at Hslot
    ihave Hslotcells :=
      cells_of_ByteSlice (sp - 16 + 8) [ptr, size] $$ Hslot
    isimp only [arrayAt, haddr12] at Hslotcells
    icases Hslotcells with ⟨Hptr, Hsize, _Hnil⟩
    obtain ⟨h8, h8_1, h8_2, h8_3⟩ :=
      offset_facts (sp - 16) 8 8 (by decide) (by omega)
    obtain ⟨h12, h12_1, h12_2, h12_3⟩ :=
      offset_facts (sp - 16) 12 12 (by decide) (by omega)
    obtain ⟨hout0, hout0_1, hout0_2, hout0_3⟩ :=
      offset_facts out 0 0 (by decide) (by omega)
    obtain ⟨hout4, hout4_1, hout4_2, hout4_3⟩ :=
      offset_facts out 4 4 (by decide) (by omega)
    -- `local 6 := [frame + 8]`
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 8)
      ptr h8 h8_1 h8_2 h8_3 with Hptr
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    -- `[out + 4] := [frame + 12]`
    ihave ⟨%houtCells, Houtarray⟩ :=
      ByteSlice_as_cells out outBefore 2 (by omega) $$ Hout
    set outCells := Slices.decodeWords outBefore with houtDef
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12)
      size h12 h12_1 h12_2 h12_3 with Hsize
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 4 outCells 1 _ size (by omega) rfl (by decide) $$
        Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 4) _
      hout4 hout4_1 hout4_2 hout4_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    -- `[out] := local 6`
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 0 (outCells.set 1 size) 0 _ ptr
        (by simp [houtCells]) rfl (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 0) _
      hout0 hout0_1 hout0_2 hout0_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    -- restore the stack pointer and return
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- put the frame and the region back together
    ihave Hslotcells : arrayAt 0 (sp - 16 + 8) [ptr, size] $$ [Hptr Hsize]
    · isimp only [arrayAt, haddr12]
      iframe Hptr Hsize
    ihave Hslot :=
      ByteSlice_of_cells (sp - 16 + 8) [ptr, size]
        (by simp only [List.length_cons, List.length_nil, hslotNat']; omega) $$
        Hslotcells
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop func41Depth).take 8)
        (WordCodec.u32le.serialize [ptr, size]) 8
        (by rw [List.length_take, hframeLength]; omega) $$ [Hhead Hslot]
    · isplitl_exact Hhead
      · iexact Hslot
    ihave Htop :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop func41Depth).take 8 ++ WordCodec.u32le.serialize [ptr, size])
        (by simp [List.length_take, hframeLength]) hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) func41Depth lower' $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp func47Depth 16 lower'
        ((below.drop func41Depth).take 8 ++ WordCodec.u32le.serialize [ptr, size])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hout :=
      ByteSlice_of_cells out ((outCells.set 1 size).set 0 ptr)
        (by rw [set_two outCells ptr size houtCells]
            simpa using houtNowrap) $$ Houtarray
    isimp only [set_two outCells ptr size houtCells,
      WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil] at Hout
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %ptr %blockId %contents
      %(lower' ++ ((below.drop func41Depth).take 8
        ++ WordCodec.u32le.serialize [ptr, size]))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hbump Hblock Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams
