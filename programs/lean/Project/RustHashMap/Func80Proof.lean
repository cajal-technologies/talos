import Project.RustHashMap.CollectBodyContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func30Proof
import Project.RustHashMap.Func55Proof
import Project.RustHashMap.Func57Proof

/-!
# Proof of the seed source of `collect_entries`

This file proves local `func80`, absolute index 83, WAT lines 10611 to
10651.  It is the function that `RandomState::new` calls for a fresh pair
of SipHash seeds.

The body takes a 16-byte frame, writes a zero byte at `frame + 15`, calls
the empty marker `func 33`, allocates one byte with `func 58`, writes the
address of the frame byte and the address of the allocation into the
16-byte output slot as two `u64` words, and frees the allocation again
with `func 60`, whose body is empty.

So neither seed is random.  Both are addresses of the run, and the
contract returns them existentially, which is all any caller needs.

The null arm at WAT 10628 to 10631 is dead.  `func 58` raises the terminal
`talos.oom` host trap instead of returning 0, and `LiveBlock` carries the
non-null fact of the pointer it did return.
-/

namespace Project.RustHashMap.Func80Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The layout of the one-byte allocation at WAT 10623 to 10625. -/
def seedLayout : AllocLayout := { size := 1, alignment := 1 }

theorem seedLayout_valid : seedLayout.Valid := by
  simp only [AllocLayout.Valid, seedLayout]
  exact ⟨by decide, by decide, ⟨0, by decide⟩, by decide, by decide,
    by decide, by decide⟩

/-- Read the non-null fact of a live block without giving up ownership. -/
theorem LiveBlock_ptr_ne_zero [WasmSmallStepGS hlc Universal.State]
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

private theorem func80_index :
    Project.RustHashMap.«module».funcs[80]? =
      some Project.RustHashMap.func80Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func80_correct [WasmSmallStepGS hlc Universal.State] :
    Func80Spec (hlc := hlc) := by
  unfold Func80Spec CallContract callExpr
  intro sp out outBefore below heapId storedCursor frontier history
    input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 83
      Project.RustHashMap.func80Def (by decide) func80_index with Hmodule
  simp [Project.RustHashMap.func80Def, Project.RustHashMap.func80,
    Function.toLocals, Function.numParams]
  -- arithmetic on the frame base and on the output slot
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hdepth : seedSourceDepth = 32 := rfl
  have hcut : seedSourceDepth - 16 = 16 := rfl
  have hspNat : (32 : Nat) ≤ sp.toNat := by rw [hdepth] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr
        (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := rfl
  have hf15 : sp - 16 + UInt32.ofNat 15 = sp - 16 + 15 := rfl
  have hf15Nat : (sp - 16 + (15 : UInt32)).toNat = (sp - 16).toNat + 15 :=
    Slices.byteOffset_toNat (sp - 16) 15 (by omega)
  have hs15 : (sp - 16 + (15 : UInt32)).toNat
      = (sp - 16).toNat + (15 : UInt32).toNat := by rw [hf15Nat]; rfl
  have hsingle15 : (sp - 16 + (15 : UInt32)).toNat + 1 < UInt32.size := by
    rw [hf15Nat]; omega
  have hlit8 : out + UInt32.ofNat 8 = out + 8 := rfl
  have hoa0 := offset_facts64 out 0 0 rfl (by omega)
  have hoa8 := offset_facts64 out 8 8 rfl (by omega)
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  -- the own frame, cut off the region that the caller lends
  ihave ⟨Hbelow, %hbelowLength⟩ :=
    StackBelow_length sp seedSourceDepth below $$ Hbelow
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp seedSourceDepth 16 below (by decide) $$ Hbelow
  isimp only [hcut] at Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop 16) hbase16 $$ Hframe
  ihave ⟨Hhead, Hbyte⟩ :=
    ByteSlice_cut (sp - 16) (below.drop 16) 15 (by omega) $$ Hframe
  isimp only [hf15] at Hbyte
  have hheadLength : ((below.drop 16).take 15).length = 15 := by
    rw [List.length_take, hframeLength]
    omega
  have hbyteLength : ((below.drop 16).drop 15).length = 1 := by
    rw [List.length_drop, hframeLength]
  obtain ⟨oldSeedByte, hseedShape⟩ := List.length_eq_one_iff.mp hbyteLength
  isimp only [hseedShape] at Hbyte
  ihave ⟨%_hseedBound, Hseedbyte⟩ :=
    (Slices.ByteSlice_singleton 0 (sp - 16 + 15) oldSeedByte).mp $$ Hbyte
  -- `[frame + 15] := 0`
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind twp_store8_gen (address := sp - 16) (offset := 15)
    oldSeedByte hs15 with Hseedbyte
  -- `call 33`, the empty marker
  have Hmark : Func30Spec (hlc := hlc) :=
    Project.RustHashMap.Func30Proof.func30_correct
  unfold Func30Spec CallContract callExpr at Hmark
  simp only [List.nil_append] at Hmark
  iapply Hmark
    (callerLocals :=
      { params := [.i32 out]
        locals := [.i32 (sp - 16), ValueType.i32.zero]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  · unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iintro Hruntime
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    -- the block around `call 58`
    wasm_twp_pures [twp_block twp_const twp_const]
    have Halloc : Func55Spec (hlc := hlc) :=
      Project.RustHashMap.Func55Proof.func55_correct
    unfold Func55Spec CallContract callExpr at Halloc
    simp only [List.cons_append, List.nil_append] at Halloc
    iapply Halloc (size := 1) (alignment := 1) (layout := seedLayout)
      (heapId := heapId) (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        { params := [.i32 out]
          locals := [.i32 (sp - 16), ValueType.i32.zero]
          values := [] })
      (stack := [])
    isplitl [Hmodule Henv]
    · unfold RuntimeContext
      iframe Hmodule Henv
    isplitl_exacts [Hbump Hstreams]
    isplitl_pureexact ⟨⟨rfl, rfl⟩, seedLayout_valid, Or.inl rfl⟩
    unfold AllocContinuation
    cases hdecision : classifyBump frontier seedLayout with
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
              seedLayout allocBytes $$ Hblock
          wasm_twp_localTee [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          iapply twp_brIf hptrNonzero (by rfl)
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          -- `[out] := frame + 15` as a `u64`
          ihave ⟨Hlow, Hhigh⟩ := ByteSlice_cut out outBefore 8 (by omega) $$ Hout
          isimp only [hlit8] at Hhigh
          have hlowLength : (outBefore.take 8).length = 8 := by
            rw [List.length_take, houtLength]
            omega
          have hhighLength : (outBefore.drop 8).length = 8 := by
            rw [List.length_drop, houtLength]
          ihave Hlowword :=
            ByteSlice_as_word out (out + 0) (outBefore.take 8)
              (by rw [UInt32.add_zero]) hlowLength $$ Hlow
          ihave Hhighword :=
            ByteSlice_as_word (out + 8) (out + 8) (outBefore.drop 8) rfl
              hhighLength $$ Hhigh
          wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add
            twp_extendUI32]
          wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out)
            (offset := 0)
            (Wasm.RustStd.HashMap.Table.groupWord (outBefore.take 8))
            hoa0.1 hoa0.2.1 hoa0.2.2.1 hoa0.2.2.2.1 hoa0.2.2.2.2.1
            hoa0.2.2.2.2.2.1 hoa0.2.2.2.2.2.2.1 hoa0.2.2.2.2.2.2.2
            with Hlowword
          -- `[out + 8] := ptr` as a `u64`
          wasm_twp_pures [twp_localGet twp_localGet twp_extendUI32]
          wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out)
            (offset := 8)
            (Wasm.RustStd.HashMap.Table.groupWord (outBefore.drop 8))
            hoa8.1 hoa8.2.1 hoa8.2.2.1 hoa8.2.2.2.1 hoa8.2.2.2.2.1
            hoa8.2.2.2.2.2.1 hoa8.2.2.2.2.2.2.1 hoa8.2.2.2.2.2.2.2
            with Hhighword
          -- `call 60`, the free, whose body is empty
          wasm_twp_pures [twp_localGet twp_const twp_const]
          have Hfree : Func57Spec (hlc := hlc) :=
            Project.RustHashMap.Func57Proof.func57_correct
          unfold Func57Spec CallContract callExpr at Hfree
          simp only [List.cons_append, List.nil_append] at Hfree
          iapply Hfree (ptr := allocBase) (size := 1) (alignment := 1)
            (layout := seedLayout) (heapId := heapId)
            (allocationId := history.nextId) (bytes := allocBytes)
            (storedCursor := finish) (frontier := finish.toNat)
            (history := history.allocate allocBase seedLayout)
            (callerLocals :=
              { params := [.i32 out]
                locals := [.i32 (sp - 16), .i32 allocBase]
                values := [] })
            (stack := [])
          isplitl [Hmodule Henv]
          · unfold RuntimeContext
            iframe Hmodule Henv
          isplitl_exacts [Hbump Hblock]
          isplitl_pureexact ⟨rfl, rfl, Or.inl rfl⟩
          iintro Hruntime Hbump
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
          -- restore the stack pointer and return
          wasm_twp_pures [twp_localGet twp_const twp_add]
          rw [show (16 : UInt32) + (sp - 16) = sp by
            rw [UInt32.add_comm, UInt32.sub_add_cancel]]
          wasm_twp_rebind twp_globalSet with Hsp
          wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
          simp only [List.take_zero, List.nil_append]
          -- rebuild the frame and the region
          ihave Hbyte :=
            (Slices.ByteSlice_singleton 0 (sp - 16 + 15)
              ((0 : UInt32).toUInt8)).mpr $$ [Hseedbyte]
          · isplitl_pureexact hsingle15
            iexact Hseedbyte
          ihave Hframe :=
            ByteSlice_glue (sp - 16) ((below.drop 16).take 15)
              [(0 : UInt32).toUInt8] 15 hheadLength $$ [Hhead Hbyte]
          · isplitl_exact Hhead
            · irw_exact [hf15] with Hbyte
          ihave Hframe :=
            StackBelow_intro sp (sp - 16) 16
              ((below.drop 16).take 15 ++ [(0 : UInt32).toUInt8])
              (by simp [hheadLength]) hbase16 $$ Hframe
          ihave Hbelow :=
            frame_join sp seedSourceDepth 16
              (below.take (seedSourceDepth - 16))
              ((below.drop 16).take 15 ++ [(0 : UInt32).toUInt8])
              (by rw [List.length_take, hbelowLength]; omega) (by decide) $$
              [Hlower Hframe]
          · isplitl_exact Hlower
            · iexact Hframe
          ihave Hsp : StackPointer sp $$ [Hsp]
          · unfold StackPointer
            iexact Hsp
          isimp only [UInt32.add_zero] at Hlowword
          iclose_map_runtime Hruntime with Hmodule Henv
          ihave Hnormal := BI.and_elim_l $$ Hcont
          ihave Hnormal := Hnormal
            $$ %(UInt64.ofNat ((15 : UInt32) + (sp - 16)).toNat)
            %(UInt64.ofNat allocBase.toNat)
            %(below.take (seedSourceDepth - 16)
              ++ ((below.drop 16).take 15 ++ [(0 : UInt32).toUInt8]))
            %finish %finish.toNat
            %((history.allocate allocBase seedLayout).retire history.nextId
              allocBase seedLayout)
          iapply Hnormal $$ Hruntime Hsp Hbelow Hlowword Hhighword Hbump
            Hstreams
        · iintro Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          ihave Hoom := Hoom $$ %input
          iapply Hoom $$ Hstreams

end Project.RustHashMap.Func80Proof
