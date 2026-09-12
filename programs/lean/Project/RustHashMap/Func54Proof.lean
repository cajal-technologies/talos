import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func48Proof

/-!
# Proof of the `String` builder of the `io::Error::new` chain

Local `func54` (absolute index 57) keeps a 16-byte frame.  It asks the
`RawVec` allocate below it for `msgLen` bytes, writes the record
`(capacity, pointer, length)` with the length 0, copies the message into
the new block with `memory.copy`, and then overwrites the length with
`msgLen`.

The copy reads the message bytes, so the contract takes them and gives
them back unchanged.  The block that the contract returns holds the
message.

The theorem is unconditional, because
`Project.RustHashMap.Func48Proof.func48_correct` is.
-/

namespace Project.RustHashMap.Func54Proof

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

/-- Open a live block for one refill of a known size.
`LiveBlock_bytesFocus` drops the length of the old bytes, and the
`memory.copy` rule asks for it. -/
private theorem LiveBlock_refill [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat) (ptr : UInt32)
    (layout : AllocLayout) (oldBytes newBytes : List UInt8)
    (hnew : newBytes.length = layout.size) :
    LiveBlock heapId allocationId ptr layout oldBytes ⊢
      iprop(⌜oldBytes.length = layout.size⌝ ∗
        Slices.ByteSlice 0 ptr oldBytes ∗
        (Slices.ByteSlice 0 ptr newBytes -∗
          LiveBlock heapId allocationId ptr layout newBytes)) := by
  unfold LiveBlock
  iintro ⟨Htoken, Hbytes, %hfacts⟩
  isplitl_pureexact hfacts.1
  · isplitl_exact Hbytes
    · iintro HnewBytes
      iframe Htoken HnewBytes
      ipureexact ⟨hnew, hfacts.2.1, hfacts.2.2⟩

private theorem func54_index :
    Project.RustHashMap.«module».funcs[54]? =
      some Project.RustHashMap.func54Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func54_correct [WasmSmallStepGS hlc Universal.State] :
    Func54Spec (hlc := hlc) := by
  unfold Func54Spec CallContract callExpr
  intro sp out msgPtr msgLen heapId outBefore below msgBytes storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmsg, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hlenPos, hlenLe, hmsgLength⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 57
      Project.RustHashMap.func54Def (by decide) func54_index with Hmodule
  simp [Project.RustHashMap.func54Def, Project.RustHashMap.func54,
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
  -- The frame is the top 16 bytes; the callee gets the 112 below it.
  have hdepth54 : func54Depth = 128 := rfl
  have hdepth48 : func48Depth = 112 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (128 : Nat) ≤ sp.toNat := by rw [hdepth54] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := by rfl
  have hcut : func54Depth - 16 = func48Depth := rfl
  have hlenNonzero : ¬ msgLen = 0 := by
    intro hzero
    rw [hzero] at hlenPos
    simp at hlenPos
  have hlenGt : (0 : UInt32) < msgLen :=
    UInt32.lt_iff_toNat_lt.mpr (by simpa using hlenPos)
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp func54Depth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop func48Depth) hbase16 $$ Hframe
  ihave ⟨Hhead, Hslot⟩ :=
    ByteSlice_cut (sp - 16) (below.drop func48Depth) 8 (by omega) $$ Hframe
  have hslotAddr : sp - 16 + UInt32.ofNat 8 = 8 + (sp - 16) := by
    rw [UInt32.add_comm]
    rfl
  isimp only [hslotAddr] at Hslot
  have hslotNat : (8 + (sp - 16)).toNat = sp.toNat - 8 := by
    rw [UInt32.add_comm, show (8 : UInt32) = UInt32.ofNat 8 from rfl,
      Slices.byteOffset_toNat (sp - 16) 8 (by omega)]
    omega
  have Hleaf : Func48Spec (hlc := hlc) :=
    Project.RustHashMap.Func48Proof.func48_correct
  unfold Func48Spec CallContract callExpr at Hleaf
  simp only [List.cons_append, List.nil_append] at Hleaf
  iapply Hleaf (sp := sp - 16) (out := 8 + (sp - 16)) (count := msgLen)
    (heapId := heapId)
    (outBefore := (below.drop func48Depth).drop 8)
    (below := below.take func48Depth)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 msgPtr, .i32 msgLen]
        locals := [.i32 (sp - 16), .i32 1, ValueType.i32.zero,
          ValueType.i32.zero, ValueType.i32.zero]
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
    ⟨by rw [List.length_drop, hframeLength], by omega, by omega, hlenPos,
      hlenLe⟩
  isplit
  · iintro %ptr %blockId %contents %lower' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hlower Hslot Hbump Hblock Hstreams
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    isimp only [StackPointer] at Hsp
    have hslotAddr' : (8 : UInt32) + (sp - 16) = sp - 16 + 8 := by
      rw [UInt32.add_comm]
    have haddr12 : sp - 16 + 8 + 4 = sp - 16 + 12 := by
      rw [UInt32.add_assoc, show (8 : UInt32) + 4 = 12 from by decide]
    isimp only [hslotAddr'] at Hslot
    ihave Hslotcells := cells_of_ByteSlice (sp - 16 + 8) [msgLen, ptr] $$ Hslot
    isimp only [arrayAt, haddr12] at Hslotcells
    icases Hslotcells with ⟨Hcap, Hptr, _Hslotnil⟩
    obtain ⟨h8, h8_1, h8_2, h8_3⟩ :=
      offset_facts (sp - 16) 8 8 (by decide) (by omega)
    obtain ⟨h12, h12_1, h12_2, h12_3⟩ :=
      offset_facts (sp - 16) 12 12 (by decide) (by omega)
    obtain ⟨hout0, hout0_1, hout0_2, hout0_3⟩ :=
      offset_facts out 0 0 (by decide) (by omega)
    obtain ⟨hout4, hout4_1, hout4_2, hout4_3⟩ :=
      offset_facts out 4 4 (by decide) (by omega)
    obtain ⟨hout8, hout8_1, hout8_2, hout8_3⟩ :=
      offset_facts out 8 8 (by decide) (by omega)
    -- `local 5 := [frame + 12]`
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12)
      ptr h12 h12_1 h12_2 h12_3 with Hptr
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    -- the record `(capacity, pointer, length)` with the length 0
    ihave ⟨%houtCells, Houtarray⟩ :=
      ByteSlice_as_cells out outBefore 3 (by omega) $$ Hout
    set outCells := Slices.decodeWords outBefore with houtDef
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 8)
      msgLen h8 h8_1 h8_2 h8_3 with Hcap
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 0 outCells 0 _ msgLen (by omega) rfl (by decide) $$
        Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 0) _
      hout0 hout0_1 hout0_2 hout0_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 4 (outCells.set 0 msgLen) 1 _ ptr (by simp [houtCells]) rfl
        (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 4) _
      hout4 hout4_1 hout4_2 hout4_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_pures [twp_localGet twp_const]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 8 ((outCells.set 0 msgLen).set 1 ptr) 2 _ 0
        (by simp [houtCells]) rfl (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 8) _
      hout8 hout8_1 hout8_2 hout8_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    -- the message is not empty, so both guards fall through
    wasm_twp_pures [twp_block twp_localGet twp_const]
    iapply twp_gtU (result := 1) (by rw [if_pos hlenGt])
    wasm_twp_pures [twp_const twp_and]
    simp only [show (1 : UInt32) &&& 1 = 1 from by decide]
    iapply twp_eqz (result := 0) (by decide)
    iapply twp_brIfZero
    simp only [List.drop_zero]
    -- `local 6 := [out + 4]` and `local 7 := msgLen`
    wasm_twp_pures [twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_load out 4 (((outCells.set 0 msgLen).set 1 ptr).set 2 0) 1 ptr
        (by simp [houtCells]) (by simp) (by decide) $$ Houtarray
    wasm_twp_rebind twp_load32 (address := out) (offset := 4) ptr
      hout4 hout4_1 hout4_2 hout4_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_shl]
    simp only [show msgLen <<< ((0 : UInt32) % 32) = msgLen from by simp]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_block twp_localGet]
    iapply twp_eqz (result := 0) (by rw [if_neg hlenNonzero])
    iapply twp_brIfZero
    simp only [List.drop_zero]
    -- the copy
    have hmsgSize : msgBytes.length = (messageLayout msgLen).size := hmsgLength
    ihave ⟨%hcontentsSize, Hdst, Hreseal⟩ :=
      LiveBlock_refill heapId blockId ptr (messageLayout msgLen) contents
        msgBytes hmsgSize $$ Hblock
    have hcontentsLen : contents.length = msgLen.toNat := hcontentsSize
    isimp only [Slices.ByteSlice] at Hmsg Hdst
    icases Hmsg with ⟨%hmsgNowrap, Hmsg⟩
    icases Hdst with ⟨%hdstNowrap, Hdst⟩
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    iapply twp_memoryCopy32 contents msgBytes hcontentsLen hmsgLength hlenPos
      (by omega) (by omega) $$ Hmsg Hdst
    iintro Hmsg Hdst
    ihave Hmsg : Slices.ByteSlice 0 msgPtr msgBytes $$ [Hmsg]
    · isimp only [Slices.ByteSlice]
      isplitl_pureexact hmsgNowrap
      · iexact Hmsg
    ihave Hdst : Slices.ByteSlice 0 ptr msgBytes $$ [Hdst]
    · isimp only [Slices.ByteSlice]
      isplitl_pureexact (by omega)
      · iexact Hdst
    ihave Hblock := Hreseal $$ Hdst
    wasm_twp_pures [twp_exitControl]
    -- the length becomes `msgLen`
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 8 (((outCells.set 0 msgLen).set 1 ptr).set 2 0) 2 _ msgLen
        (by simp [houtCells]) rfl (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 8) _
      hout8 hout8_1 hout8_2 hout8_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_pures [twp_exitControl]
    -- restore the stack pointer and return
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- put the frame and the region back together
    ihave Hslotcells : arrayAt 0 (sp - 16 + 8) [msgLen, ptr] $$ [Hcap Hptr]
    · isimp only [arrayAt, haddr12]
      iframe Hcap Hptr
    ihave Hslot :=
      ByteSlice_of_cells (sp - 16 + 8) [msgLen, ptr]
        (by simp only [List.length_cons, List.length_nil,
              show (sp - 16 + 8).toNat = sp.toNat - 8 from by
                rw [← hslotAddr']; exact hslotNat]
            omega) $$ Hslotcells
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop func48Depth).take 8)
        (WordCodec.u32le.serialize [msgLen, ptr]) 8
        (by rw [List.length_take, hframeLength]; omega) $$ [Hhead Hslot]
    · isplitl_exact Hhead
      · irw_exact [hslotAddr, hslotAddr'] with Hslot
    ihave Htop :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop func48Depth).take 8
          ++ WordCodec.u32le.serialize [msgLen, ptr])
        (by simp [List.length_take, hframeLength]) hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) func48Depth lower' $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp func54Depth 16 lower'
        ((below.drop func48Depth).take 8
          ++ WordCodec.u32le.serialize [msgLen, ptr])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hout :=
      ByteSlice_of_cells out
        ((((outCells.set 0 msgLen).set 1 ptr).set 2 0).set 2 msgLen)
        (by rw [set_three_twice outCells msgLen ptr msgLen houtCells]
            simpa using houtNowrap) $$ Houtarray
    isimp only [set_three_twice outCells msgLen ptr msgLen houtCells,
      WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil] at Hout
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %ptr %blockId
      %(lower' ++ ((below.drop func48Depth).take 8
        ++ WordCodec.u32le.serialize [msgLen, ptr]))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hmsg Hbump Hblock Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Func54Proof
