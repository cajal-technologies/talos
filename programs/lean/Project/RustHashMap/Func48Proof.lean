import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func45Proof

/-!
# Proof of the `RawVec` allocate of the `io::Error::new` chain

Local `func48` (absolute index 51) keeps a 16-byte frame.  It calls
`func 48` with the frame base as the twelve-byte output slot, reads the
flag, the count, and the pointer back, and writes the count and the
pointer into the output slot of its own caller.

Three arms of the body are dead.  The flag that `func 48` returns is 0,
so the `call 99` arm at WAT line 9611 never runs.  The element size that
the caller passes is 1, so the `-1` store at WAT line 9624 never runs.
The store at `frame + 12` that does run writes a word that no later
instruction reads.

The theorem is unconditional, because
`Project.RustHashMap.Func45Proof.func45_correct` is.
-/

namespace Project.RustHashMap.Func48Proof

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

private theorem func48_index :
    Project.RustHashMap.«module».funcs[48]? =
      some Project.RustHashMap.func48Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func48_correct [WasmSmallStepGS hlc Universal.State] :
    Func48Spec (hlc := hlc) := by
  unfold Func48Spec CallContract callExpr
  intro sp out count heapId outBefore below storedCursor frontier
    history input output raised callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hcountPos, hcountLe⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 51
      Project.RustHashMap.func48Def (by decide) func48_index with Hmodule
  simp [Project.RustHashMap.func48Def, Project.RustHashMap.func48,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_const twp_and
    twp_localGet twp_localGet]
  simp only [show (0 : UInt32) &&& 1 = 0 from by decide]
  -- The frame is the top 16 bytes; the callee gets the 96 below it.
  have hdepth48 : func48Depth = 112 := rfl
  have hdepth45 : func45Depth = 96 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (112 : Nat) ≤ sp.toNat := by rw [hdepth48] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := by rfl
  have hcut : func48Depth - 16 = func45Depth := rfl
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp func48Depth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop func45Depth) hbase16 $$ Hframe
  ihave ⟨Hslot, Htail⟩ :=
    ByteSlice_cut (sp - 16) (below.drop func45Depth) 12 (by omega) $$ Hframe
  have htail12 : sp - 16 + UInt32.ofNat 12 = sp - 16 + 12 := by rfl
  isimp only [htail12] at Htail
  have Hleaf : Func45Spec (hlc := hlc) :=
    Project.RustHashMap.Func45Proof.func45_correct
  unfold Func45Spec CallContract callExpr at Hleaf
  simp only [List.cons_append, List.nil_append] at Hleaf
  iapply Hleaf (sp := sp - 16) (out := sp - 16) (count := count)
    (heapId := heapId)
    (outBefore := (below.drop func45Depth).take 12)
    (below := below.take func45Depth)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 count, .i32 1, .i32 1]
        locals := [.i32 (sp - 16), ValueType.i32.zero, ValueType.i32.zero]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl [Hsp]
  · unfold StackPointer
    iexact Hsp
  isplitl_exacts [Hlower Hslot Hbump Hstreams]
  isplitl_pureexact
    ⟨by rw [List.length_take, hframeLength]; omega, by omega, by omega, hcountPos,
      hcountLe⟩
  isplit
  · iintro %ptr %blockId %contents %lower' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hlower Hslot Hbump Hblock Hstreams
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    isimp only [StackPointer] at Hsp
    obtain ⟨h0, h0_1, h0_2, h0_3⟩ :=
      offset_facts (sp - 16) 0 0 (by decide) (by omega)
    obtain ⟨h4, h4_1, h4_2, h4_3⟩ :=
      offset_facts (sp - 16) 4 4 (by decide) (by omega)
    obtain ⟨h8, h8_1, h8_2, h8_3⟩ :=
      offset_facts (sp - 16) 8 8 (by decide) (by omega)
    obtain ⟨h12, h12_1, h12_2, h12_3⟩ :=
      offset_facts (sp - 16) 12 12 (by decide) (by omega)
    obtain ⟨hout0, hout0_1, hout0_2, hout0_3⟩ :=
      offset_facts out 0 0 (by decide) (by omega)
    obtain ⟨hout4, hout4_1, hout4_2, hout4_3⟩ :=
      offset_facts out 4 4 (by decide) (by omega)
    ihave Hslotcells := cells_of_ByteSlice (sp - 16) [0, count, ptr] $$ Hslot
    -- The flag word is 0, so the `call 99` arm is dead.
    wasm_twp_pures [twp_block twp_localGet]
    ihave ⟨Hcell, Hclose⟩ :=
      cell_load (sp - 16) 0 [0, count, ptr] 0 0 (by simp) rfl (by decide) $$
        Hslotcells
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 0) 0
      h0 h0_1 h0_2 h0_3 with Hcell
    ihave Hslotcells := Hclose $$ Hcell
    wasm_twp_pures [twp_const twp_and]
    simp only [show (0 : UInt32) &&& 1 = 0 from by decide]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- `local 5 := [frame + 4]` and `local 6 := [frame + 8]`
    wasm_twp_pures [twp_localGet]
    ihave ⟨Hcell, Hclose⟩ :=
      cell_load (sp - 16) 4 [0, count, ptr] 1 count (by simp) rfl (by decide) $$
        Hslotcells
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 4) count
      h4 h4_1 h4_2 h4_3 with Hcell
    ihave Hslotcells := Hclose $$ Hcell
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    ihave ⟨Hcell, Hclose⟩ :=
      cell_load (sp - 16) 8 [0, count, ptr] 2 ptr (by simp) rfl (by decide) $$
        Hslotcells
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 8) ptr
      h8 h8_1 h8_2 h8_3 with Hcell
    ihave Hslotcells := Hclose $$ Hcell
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    -- The element size is 1, so the `-1` store is dead.
    wasm_twp_pures [twp_block twp_block twp_localGet]
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- `[frame + 12] := local 5`, a word that nothing reads again
    ihave ⟨%htailCells, Htailarray⟩ :=
      ByteSlice_as_cells (sp - 16 + 12) ((below.drop func45Depth).drop 12) 1
        (by rw [List.length_drop, hframeLength]) $$ Htail
    obtain ⟨tailWord, htailShape⟩ := List.length_eq_one_iff.mp htailCells
    isimp only [htailShape, arrayAt] at Htailarray
    icases Htailarray with ⟨Htailcell, _Htailnil⟩
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 12) tailWord
      h12 h12_1 h12_2 h12_3 with Htailcell
    wasm_twp_pures [twp_exitControl]
    -- `[out + 4] := local 6` and `[out] := local 5`
    ihave ⟨%houtCells, Houtarray⟩ :=
      ByteSlice_as_cells out outBefore 2 (by omega) $$ Hout
    set outCells := Slices.decodeWords outBefore with houtDef
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 4 outCells 1 _ ptr (by omega) rfl (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 4) _
      hout4 hout4_1 hout4_2 hout4_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 0 (outCells.set 1 ptr) 0 _ count (by simp [houtCells]) rfl
        (by decide) $$ Houtarray
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
    ihave Hslotbytes :=
      ByteSlice_of_cells (sp - 16) [0, count, ptr]
        (by simp only [List.length_cons, List.length_nil, hframeNat]
            omega) $$ Hslotcells
    ihave Htailcells : arrayAt 0 (sp - 16 + 12) [count] $$ [Htailcell]
    · isimp only [arrayAt]
      iframe Htailcell
    ihave Htailbytes :=
      ByteSlice_of_cells (sp - 16 + 12) [count]
        (by simp only [List.length_cons, List.length_nil,
              show (sp - 16 + 12).toNat = sp.toNat - 4 from by
                rw [show (12 : UInt32) = UInt32.ofNat 12 from rfl,
                  Slices.byteOffset_toNat (sp - 16) 12 (by omega)]
                omega]
            omega) $$ Htailcells
    ihave Hframe :=
      ByteSlice_glue (sp - 16) (WordCodec.u32le.serialize [0, count, ptr])
        (WordCodec.u32le.serialize [count]) 12 (by simp) $$
        [Hslotbytes Htailbytes]
    · isplitl_exact Hslotbytes
      · irw_exact [htail12] with Htailbytes
    ihave Htop :=
      StackBelow_intro sp (sp - 16) 16
        (WordCodec.u32le.serialize [0, count, ptr]
          ++ WordCodec.u32le.serialize [count])
        (by simp) hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) func45Depth lower' $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp func48Depth 16 lower'
        (WordCodec.u32le.serialize [0, count, ptr]
          ++ WordCodec.u32le.serialize [count])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hout :=
      ByteSlice_of_cells out ((outCells.set 1 ptr).set 0 count)
        (by rw [set_two outCells count ptr houtCells]
            simpa using houtNowrap) $$ Houtarray
    isimp only [set_two outCells count ptr houtCells,
      WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil] at Hout
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %ptr %blockId %contents
      %(lower' ++ (WordCodec.u32le.serialize [0, count, ptr]
        ++ WordCodec.u32le.serialize [count]))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hbump Hblock Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Func48Proof
