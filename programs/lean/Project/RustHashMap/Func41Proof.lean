import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func30Proof
import Project.RustHashMap.Func55Proof

/-!
# Proof of the allocate leaf of the `borsh::io::Error::new` chain

This file proves local `func41` (absolute index 44) from the two leaves
that the chain rests on: `Project.RustHashMap.Func30Proof.func30_correct`
for the empty marker at absolute 33, and
`Project.RustHashMap.Func55Proof.func55_correct` for the bump allocator at
absolute 58.  The theorem is therefore unconditional.
-/

namespace Project.RustHashMap.Func41Proof

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

/-- Read the non-null fact of a live block without giving up ownership.
The null arm of the body at WAT line 9150 is dead because of it. -/
private theorem LiveBlock_ptr_ne_zero [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (blockId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8) :
    LiveBlock heapId blockId ptr layout bytes ⊢
      iprop(LiveBlock heapId blockId ptr layout bytes ∗ ⌜ptr ≠ 0⌝) := by
  iintro Hblock
  ihave ⟨Htoken, Hbytes, %hfacts⟩ :=
    (LiveBlock_open heapId blockId ptr layout bytes).mp $$ Hblock
  isplitl [Htoken Hbytes]
  · iapply (LiveBlock_open heapId blockId ptr layout bytes).mpr
    isplitl_exacts [Htoken Hbytes]
    ipureexact hfacts
  · ipureexact hfacts.2.1

private theorem func41_index :
    Project.RustHashMap.«module».funcs[41]? =
      some Project.RustHashMap.func41Def := by rfl

theorem func41_correct [WasmSmallStepGS hlc Universal.State] :
    Func41Spec (hlc := hlc) := by
  unfold Func41Spec CallContract callExpr
  intro sp out size heapId outBefore below storedCursor frontier history
    input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hsizePos, hsizeLe⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 44
      Project.RustHashMap.func41Def (by decide) func41_index with Hmodule
  simp [Project.RustHashMap.func41Def, Project.RustHashMap.func41,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  have hdepth32 : func41Depth = 32 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (32 : Nat) ≤ sp.toNat := by
    have hdepth : func41Depth = 32 := rfl
    rw [hdepth] at hspLow
    exact hspLow
  have hbaseNat : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le sp 32
      (UInt32.le_iff_toNat_le.mpr (by simpa using hspNat))]
    rfl
  have hbase : sp - UInt32.ofNat func41Depth = sp - 32 := by
    rw [show UInt32.ofNat func41Depth = 32 from by decide]
  obtain ⟨h8, h8_1, h8_2, h8_3⟩ :=
    offset_facts (sp - 32) 8 8 (by decide) (by omega)
  obtain ⟨h12, h12_1, h12_2, h12_3⟩ :=
    offset_facts (sp - 32) 12 12 (by decide) (by omega)
  obtain ⟨h16, h16_1, h16_2, h16_3⟩ :=
    offset_facts (sp - 32) 16 16 (by decide) (by omega)
  obtain ⟨h20, h20_1, h20_2, h20_3⟩ :=
    offset_facts (sp - 32) 20 20 (by decide) (by omega)
  obtain ⟨h24, h24_1, h24_2, h24_3⟩ :=
    offset_facts (sp - 32) 24 24 (by decide) (by omega)
  obtain ⟨h28, h28_1, h28_2, h28_3⟩ :=
    offset_facts (sp - 32) 28 28 (by decide) (by omega)
  obtain ⟨hout0, hout0_1, hout0_2, hout0_3⟩ :=
    offset_facts out 0 0 (by decide) (by omega)
  obtain ⟨hout4, hout4_1, hout4_2, hout4_3⟩ :=
    offset_facts out 4 4 (by decide) (by omega)
  ihave ⟨%hcells, Harray⟩ :=
    StackBelow_as_cells sp (sp - 32) func41Depth 8 below (by decide) hbase $$
      Hbelow
  set cells := Slices.decodeWords below with hcellsDef
  have hsizeNonzero : size ≠ 0 := by
    intro hzero
    rw [hzero] at hsizePos
    simp at hsizePos
  wasm_twp_pures [twp_block twp_block twp_block twp_block twp_block twp_block
    twp_localGet]
  iapply twp_brIf hsizeNonzero (by rfl)
  simp only [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_brIfZero]
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have Hmark : Func30Spec (hlc := hlc) :=
    Project.RustHashMap.Func30Proof.func30_correct
  unfold Func30Spec CallContract callExpr at Hmark
  simp only [List.nil_append] at Hmark
  iapply Hmark
    (callerLocals :=
      { params := [.i32 out, .i32 1, .i32 size, .i32 0]
        locals := [.i32 (sp - 32), ValueType.i32.zero, ValueType.i32.zero,
          ValueType.i32.zero, ValueType.i32.zero]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  · unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iintro Hruntime
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    have Halloc : Func55Spec (hlc := hlc) :=
      Project.RustHashMap.Func55Proof.func55_correct
    unfold Func55Spec CallContract callExpr at Halloc
    simp only [List.cons_append, List.nil_append] at Halloc
    iapply Halloc (size := size) (alignment := 1)
      (layout := messageLayout size) (heapId := heapId)
      (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        { params := [.i32 out, .i32 1, .i32 size, .i32 0]
          locals := [.i32 (sp - 32), ValueType.i32.zero, ValueType.i32.zero,
            ValueType.i32.zero, ValueType.i32.zero]
          values := [] })
      (stack := [.i32 (sp - 32)])
    isplitl [Hmodule Henv]
    · unfold RuntimeContext
      iframe Hmodule Henv
    isplitl_exacts [Hbump Hstreams]
    isplitl_pureexact
      ⟨⟨rfl, rfl⟩, messageLayout_valid size hsizePos hsizeLe, Or.inl rfl⟩
    unfold AllocContinuation
    cases hdecision : classifyBump frontier (messageLayout size) with
    | oom =>
        iintro Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        ihave Hoom := Hoom $$ %input
        iapply Hoom $$ Hstreams
    | success allocBase finish =>
        isplit
        · iintro %allocBytes Hruntime Hbump Hblock Hstreams
          iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          simp only [List.cons_append, List.nil_append]
          ihave ⟨Hblock, %hptrNonzero⟩ :=
            LiveBlock_ptr_ne_zero heapId history.nextId allocBase
              (messageLayout size) allocBytes $$ Hblock
          ihave ⟨Hcell, Hclose⟩ :=
            cell_focus (sp - 32) 16 cells 4 _ allocBase
              (by omega) rfl (by decide) $$ Harray
          wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 16) _
            h16 h16_1 h16_2 h16_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          iapply twp_br (by rfl)
          simp only [List.take_zero, List.nil_append]
          wasm_twp_pures [twp_block twp_localGet]
          set cellsA := cells.set 4 allocBase with hA
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 16 cellsA 4 allocBase
              (by simp [hA, hcells]) (by simp [hA]) (by decide) $$ Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 16)
            allocBase h16 h16_1 h16_2 h16_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          iapply twp_brIf hptrNonzero (by rfl)
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          -- `[frame + 28] := [frame + 16]`
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 16 cellsA 4 allocBase
              (by simp [hA, hcells]) (by simp [hA]) (by decide) $$ Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 16)
            allocBase h16 h16_1 h16_2 h16_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          ihave ⟨Hcell, Hclose⟩ :=
            cell_focus (sp - 32) 28 cellsA 7 _ allocBase
              (by simp [hA, hcells]) rfl (by decide) $$ Harray
          wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 28) _
            h28 h28_1 h28_2 h28_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          set cellsB := cellsA.set 7 allocBase with hB
          -- `[frame + 24] := [frame + 28]`
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 28 cellsB 7 allocBase
              (by simp [hB, hA, hcells]) (by simp [hB, hA]) (by decide) $$
              Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 28)
            allocBase h28 h28_1 h28_2 h28_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          ihave ⟨Hcell, Hclose⟩ :=
            cell_focus (sp - 32) 24 cellsB 6 _ allocBase
              (by simp [hB, hA, hcells]) rfl (by decide) $$ Harray
          wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 24) _
            h24 h24_1 h24_2 h24_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          set cellsC := cellsB.set 6 allocBase with hC
          -- `[frame + 20] := [frame + 24]`
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 24 cellsC 6 allocBase
              (by simp [hC, hB, hA, hcells]) (by simp [hC, hB, hA])
              (by decide) $$ Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 24)
            allocBase h24 h24_1 h24_2 h24_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          ihave ⟨Hcell, Hclose⟩ :=
            cell_focus (sp - 32) 20 cellsC 5 _ allocBase
              (by simp [hC, hB, hA, hcells]) rfl (by decide) $$ Harray
          wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 20) _
            h20 h20_1 h20_2 h20_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          set cellsD := cellsC.set 5 allocBase with hD
          -- `local 7 := [frame + 20]`, then `[frame + 8] := local 7`
          wasm_twp_pures [twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 20 cellsD 5 allocBase
              (by simp [hD, hC, hB, hA, hcells])
              (by simp [hD, hC, hB, hA]) (by decide) $$ Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 20)
            allocBase h20 h20_1 h20_2 h20_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_focus (sp - 32) 8 cellsD 2 _ allocBase
              (by simp [hD, hC, hB, hA, hcells]) rfl (by decide) $$ Harray
          wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 8) _
            h8 h8_1 h8_2 h8_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          set cellsE := cellsD.set 2 allocBase with hE
          -- `[frame + 12] := size`
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_focus (sp - 32) 12 cellsE 3 _ size
              (by simp [hE, hD, hC, hB, hA, hcells]) rfl (by decide) $$ Harray
          wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 12) _
            h12 h12_1 h12_2 h12_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          set cellsF := cellsE.set 3 size with hF
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append]
          -- `local 8 := [frame + 8]`
          wasm_twp_pures [twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 8 cellsF 2 allocBase
              (by simp [hF, hE, hD, hC, hB, hA, hcells])
              (by simp [hF, hE, hD, hC, hB, hA]) (by decide) $$ Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 8)
            allocBase h8 h8_1 h8_2 h8_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          -- `[out + 4] := [frame + 12]`
          ihave ⟨%houtCells, Houtarray⟩ :=
            ByteSlice_as_cells out outBefore 2 (by omega) $$ Hout
          set outCells := Slices.decodeWords outBefore with houtDef
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Hcell, Hclose⟩ :=
            cell_load (sp - 32) 12 cellsF 3 size
              (by simp [hF, hE, hD, hC, hB, hA, hcells])
              (by simp [hF, hE, hD, hC, hB, hA]) (by decide) $$ Harray
          wasm_twp_rebind twp_load32 (address := sp - 32) (offset := 12)
            size h12 h12_1 h12_2 h12_3 with Hcell
          ihave Harray := Hclose $$ Hcell
          ihave ⟨Houtcell, Houtclose⟩ :=
            cell_focus out 4 outCells 1 _ size (by omega) rfl (by decide) $$
              Houtarray
          wasm_twp_rebind twp_store32 (address := out) (offset := 4) _
            hout4 hout4_1 hout4_2 hout4_3 with Houtcell
          ihave Houtarray := Houtclose $$ Houtcell
          -- `[out] := local 8`
          wasm_twp_pures [twp_localGet twp_localGet]
          ihave ⟨Houtcell, Houtclose⟩ :=
            cell_focus out 0 (outCells.set 1 size) 0 _ allocBase
              (by simp [houtCells]) rfl (by decide) $$ Houtarray
          wasm_twp_rebind twp_store32 (address := out) (offset := 0) _
            hout0 hout0_1 hout0_2 hout0_3 with Houtcell
          ihave Houtarray := Houtclose $$ Houtcell
          -- restore the stack pointer and return
          wasm_twp_pures [twp_localGet twp_const twp_add]
          rw [show (32 : UInt32) + (sp - 32) = sp by
            rw [UInt32.add_comm, UInt32.sub_add_cancel]]
          wasm_twp_rebind twp_globalSet with Hsp
          wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
          ihave Hbelow := StackBelow_of_cells sp (sp - 32) func41Depth 8 cellsF
            (by decide) (by simp [hF, hE, hD, hC, hB, hA, hcells]) hbase
            (by omega) $$ Harray
          ihave Hout :=
            ByteSlice_of_cells out ((outCells.set 1 size).set 0 allocBase)
              (by rw [set_two outCells allocBase size houtCells]
                  simpa using houtNowrap) $$ Houtarray
          isimp only [set_two outCells allocBase size houtCells,
            WordCodec.serialize_cons, WordCodec.serialize_nil,
            List.append_nil] at Hout
          ihave Hsp : StackPointer sp $$ [Hsp]
          · unfold StackPointer
            iexact Hsp
          iclose_map_runtime Hruntime with Hmodule Henv
          ihave Hnormal := BI.and_elim_l $$ Hcont
          ihave Hnormal := Hnormal $$ %allocBase %(history.nextId) %allocBytes
            %(WordCodec.u32le.serialize cellsF) %finish %(finish.toNat)
            %(history.allocate allocBase (messageLayout size))
          iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hbump Hblock Hstreams
        · iintro Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          ihave Hoom := Hoom $$ %input
          iapply Hoom $$ Hstreams

end Project.RustHashMap.Func41Proof
