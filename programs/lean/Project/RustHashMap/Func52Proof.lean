import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func39Proof
import Project.RustHashMap.Func53Proof

/-!
# Proof of the head of the `io::Error::new` chain

Local `func52` (absolute index 55) is `io::Error::new`.  It keeps a
16-byte frame and makes two calls.  The first, `func 42`, builds the
message `String` into the twelve bytes at `frame + 4`.  The second,
`func 56`, packs those twelve bytes and the `ErrorKind` byte into the
sixteen-byte slot of its own caller.

The frame is committed: the body writes the stack pointer at WAT lines
9765 and 9766 and restores it at WAT lines 9781 to 9783.  So the callee
of the first call sees `sp - 16`, and `errorNewDepth = 16 + func39Depth`
gives it exactly the room that `Func39Spec` asks for.  The second call
wants only `func53Depth` bytes, and the proof splits them off the top of
what comes back.

Word 0 of the result is the capacity of the message `String`, which is
`msgLen` here.  `Func52Spec` promises that word 0 is not `okTag`, and the
length bound of the precondition gives it: `msgLen` is at most
`0x7fffffff` and `okTag` is `0x80000001`.

The `LiveBlock` that `Func39Spec` returns is dropped.  `Func52Spec` does
not promise it, because its caller frees the message through the noop
deallocator and never reads it again.

The theorem is unconditional, because both leaves are.
-/

namespace Project.RustHashMap.Func52Proof

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

private theorem func52_index :
    Project.RustHashMap.«module».funcs[52]? =
      some Project.RustHashMap.func52Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func52_correct [WasmSmallStepGS hlc Universal.State] :
    Func52Spec (hlc := hlc) := by
  unfold Func52Spec CallContract callExpr
  intro sp out kind msgPtr msgLen heapId outBefore below msgBytes storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmsg, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hmsgPos, hmsgLe, hmsgLength⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 55
      Project.RustHashMap.func52Def (by decide) func52_index with Hmodule
  simp [Project.RustHashMap.func52Def, Project.RustHashMap.func52,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  -- arithmetic on the frame base
  have hdepthE : errorNewDepth = 160 := rfl
  have hdepth39 : func39Depth = 144 := rfl
  have hdepth53 : func53Depth = 32 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (160 : Nat) ≤ sp.toNat := by
    rw [hdepthE] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := by rfl
  have hcut : errorNewDepth - 16 = func39Depth := rfl
  have hcut53 : func39Depth - func53Depth = 112 := rfl
  have h4lit : sp - 16 + UInt32.ofNat 4 = sp - 16 + 4 := rfl
  have hslotNat : (sp - 16 + (4 : UInt32)).toNat = (sp - 16).toNat + 4 :=
    Slices.byteOffset_toNat (sp - 16) 4 (by omega)
  have hword0 : msgLen ≠ okTag := by
    intro hEq
    rw [hEq] at hmsgLe
    exact absurd hmsgLe (by decide)
  -- the stack splits into the region the first callee wants and the own 16 bytes
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp errorNewDepth 16 below (by decide) $$ Hbelow
  isimp only [hcut, hbase16] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop func39Depth) hbase16 $$ Hframe
  ihave ⟨Hdead, Hslot⟩ :=
    ByteSlice_cut (sp - 16) (below.drop func39Depth) 4 (by omega) $$ Hframe
  isimp only [h4lit] at Hslot
  -- the first call: build the message `String` at `frame + 4`
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (4 : UInt32) + (sp - 16) = sp - 16 + 4 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_localGet twp_localGet twp_const]
  have Hbuild : Func39Spec (hlc := hlc) :=
    Project.RustHashMap.Func39Proof.func39_correct
  unfold Func39Spec CallContract callExpr at Hbuild
  simp only [List.cons_append, List.nil_append] at Hbuild
  iapply Hbuild (sp := sp - 16) (out := sp - 16 + 4) (msgPtr := msgPtr)
    (msgLen := msgLen) (unused := 1049164) (heapId := heapId)
    (outBefore := (below.drop func39Depth).drop 4)
    (below := below.take func39Depth) (msgBytes := msgBytes)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 kind, .i32 msgPtr, .i32 msgLen]
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
  · iintro %ptr %blockId %below' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hlower Hslot Hmsg Hbump Hblock Hstreams
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    -- the second call wants only `func53Depth` bytes of what came back
    ihave ⟨Hdeep, Htop⟩ :=
      frame_split (sp - 16) func39Depth func53Depth below' (by decide) $$ Hlower
    isimp only [hcut53] at Htop
    set deepBytes := below'.take (func39Depth - func53Depth) with hdeepBytes
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const twp_add]
    rw [show (4 : UInt32) + (sp - 16) = sp - 16 + 4 from UInt32.add_comm _ _]
    have Hpack : Func53Spec (hlc := hlc) :=
      Project.RustHashMap.Func53Proof.func53_correct
    unfold Func53Spec CallContract callExpr at Hpack
    simp only [List.cons_append, List.nil_append] at Hpack
    iapply Hpack (sp := sp - 16) (out := out) (kind := kind)
      (record := sp - 16 + 4) (word0 := msgLen) (word1 := ptr)
      (word2 := msgLen) (outBefore := outBefore)
      (below := below'.drop 112)
      (callerLocals :=
        { params := [.i32 out, .i32 kind, .i32 msgPtr, .i32 msgLen]
          locals := [.i32 (sp - 16)]
          values := [] })
      (stack := [])
    isplitl [Hmodule Henv]
    · unfold RuntimeContext
      iframe Hmodule Henv
    isplitl [Hsp]
    · unfold StackPointer
      iexact Hsp
    isplitl_exacts [Htop Hout Hslot]
    isplitl_pureexact ⟨houtLength, by omega, by omega, by omega⟩
    iintro %word3 %below53'
    iintro Hruntime Hsp Htop Hout Hslot
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    -- restore the stack pointer and return
    isimp only [StackPointer] at Hsp
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- put the stack back together
    ihave ⟨Hdeep, %hdeepLength⟩ :=
      StackBelow_length (sp - 16 - UInt32.ofNat func53Depth)
        (func39Depth - func53Depth)
        deepBytes $$ Hdeep
    ihave Hlower :=
      frame_join (sp - 16) func39Depth func53Depth
        deepBytes below53'
        hdeepLength (by decide) $$ [Hdeep Htop]
    · isplitl_exact Hdeep
      · iexact Htop
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.drop func39Depth).take 4)
        (WordCodec.u32le.serialize [msgLen, ptr, msgLen]) 4
        (by simp [hframeLength]) $$ [Hdead Hslot]
    · isplitl_exact Hdead
      · irw_exact [h4lit] with Hslot
    ihave Htop16 :=
      StackBelow_intro sp (sp - 16) 16
        ((below.drop func39Depth).take 4
          ++ WordCodec.u32le.serialize [msgLen, ptr, msgLen])
        (by rw [List.length_append, List.length_take, hframeLength]; simp)
        hbase16 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 16) func39Depth (deepBytes ++ below53')
        $$ Hlower
    isimp only [← hbase16, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp errorNewDepth 16 (deepBytes ++ below53')
        ((below.drop func39Depth).take 4
          ++ WordCodec.u32le.serialize [msgLen, ptr, msgLen])
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop16]
    · isplitl_exact Hlower
      · iexact Htop16
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil, List.append_assoc] at Hout
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %msgLen %ptr %msgLen %word3
      %((deepBytes ++ below53')
        ++ ((below.drop func39Depth).take 4
          ++ WordCodec.u32le.serialize [msgLen, ptr, msgLen]))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hmsg Hbump Hstreams %hword0
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Func52Proof
