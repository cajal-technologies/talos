import Project.RustHashMap.DecoderHeader
import Project.RustHashMap.DecoderHeaderRead
import Project.RustHashMap.DecoderPrologue

/-!
# The header stage of the decoder

`Project.RustHashMap.Decoder.headerStage` is the header block and the
empty vector that follows it.  The header block is the short-input arm
and the read that follows it.

The stage has three exits:

1. fewer than four bytes left, which writes a decode error into the
   output slot and leaves the body;
2. a declared count of zero, which writes the empty vector and leaves the
   body;
3. a count that is not zero, which goes on to the allocation.

The out-of-memory trap of the error build is the fourth arm.

Two of the exits branch out of the block that holds the body of the
decoder.  That block belongs to the caller, so the caller gives both
targets, `hexit` for the body block and `hafter` for the header stage
itself.  Both are stated at depth zero, and `branchTarget_succ` lifts
them to the depth that each branch needs.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- A branch of depth `n + 1` steps over the frame on top. -/
private theorem branchTarget_succ (arity depth : Nat) (frame : ControlFrame)
    (controls : List ControlFrame) (values : List Value) :
    branchTarget? arity (depth + 1) (frame :: controls) values
      = branchTarget? arity depth controls values := rfl

/-- The continuation of the header stage.  The first arm is the
short-input error, the second the empty vector, the third the count that
is not zero, and the fourth the out-of-memory trap of the error build. -/
def HeaderCont [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame : UInt32) (heapId : GName)
    (frameBytes outBefore below dataBytes bytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    (arity : Nat) (remainder : List Value)
    (exitCode : Program) (exitControls : List ControlFrame)
    (exitValues : List Value)
    (afterCode : Program) (afterControls : List ControlFrame)
    (afterValues : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
      ∀ word3 : UInt32,
      ∀ frameAfter : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame func49Depth below' -∗
      Slices.ByteSlice 0 frame frameAfter -∗
      Slices.ByteSlice 0 out
        (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
      pointsTo_u32 0 hdr ptr -∗
      pointsTo_u32 0 (hdr + 4) len -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜word0 ≠ okTag ∧ frameAfter.length = 64⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 word0, .i32 word1, l5, l6, l7, l8, l9, l10,
                l11, l12],
            exitValues⟩,
            exitCode, arity, remainder, exitControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
  ((RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame func49Depth below -∗
      Slices.ByteSlice 0 frame frameBytes -∗
      Slices.ByteSlice 0 out
        (WordCodec.u32le.serialize [okTag, 0, 4, 0]) -∗
      pointsTo_u32 0 hdr (ptr + 4) -∗
      pointsTo_u32 0 (hdr + 4) (len - 4) -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output raised -∗
      ⌜headerWord bytes = 0 ∧ 4 ≤ bytes.length⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 ptr, l4, .i32 (len - 4), .i32 (ptr + 4),
                .i32 0, l8, l9, l10, l11, l12],
            exitValues⟩,
            exitCode, arity, remainder, exitControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
    ((RuntimeContext -∗ StackPointer frame -∗
        StackBelow frame func49Depth below -∗
        Slices.ByteSlice 0 frame frameBytes -∗
        Slices.ByteSlice 0 out outBefore -∗
        pointsTo_u32 0 hdr (ptr + 4) -∗
        pointsTo_u32 0 (hdr + 4) (len - 4) -∗
        Slices.ByteSlice 0 ptr bytes -∗
        Slices.ByteSlice 0 entryStackTop dataBytes -∗
        BumpHeap heapId storedCursor frontier history -∗
        Streams input output raised -∗
        ⌜headerWord bytes ≠ 0 ∧ 4 ≤ bytes.length⌝ -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 ptr, l4, .i32 (len - 4), .i32 (ptr + 4),
                  .i32 (headerWord bytes), l8, l9, l10, l11, l12],
              afterValues⟩,
              afterCode, arity, remainder, afterControls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }]) ∧
      (∀ remaining' : List UInt8,
        Streams remaining' output true -∗
          Φ (.trapped (.host OOM.trapMessage))))))

set_option maxHeartbeats 2000000 in
/-- The header stage reads the length word and the declared pair count. -/
theorem twp_header_stage [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame : UInt32) (heapId : GName)
    (frameBytes outBefore below dataBytes bytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    (headerFrame : ControlFrame) (outerControls : List ControlFrame)
    (arity : Nat) (remainder : List Value)
    (exitCode : Program) (exitControls : List ControlFrame)
    (exitValues : List Value)
    (afterCode : Program) (afterControls : List ControlFrame)
    (afterValues : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hframeLength : frameBytes.length = 64)
    (houtLength : outBefore.length = 16)
    (hbytesLength : bytes.length = len.toNat)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hexit : branchTarget? arity 0 outerControls [] =
      some (exitCode, exitControls, exitValues))
    (hafter : branchTarget? arity 0 (headerFrame :: outerControls) [] =
      some (afterCode, afterControls, afterValues)) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame func49Depth below ∗
      Slices.ByteSlice 0 frame frameBytes ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 hdr ptr ∗
      pointsTo_u32 0 (hdr + 4) len ∗
      Slices.ByteSlice 0 ptr bytes ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      HeaderCont out hdr ptr len frame heapId frameBytes outBefore below
        dataBytes bytes storedCursor frontier history input output raised
        l4 l5 l6 l7 l8 l9 l10 l11 l12 arity remainder exitCode exitControls
        exitValues afterCode afterControls afterValues calls s E Φ) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12], []⟩,
            headerStage, arity, remainder,
            headerFrame :: outerControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hframe, Hout, Hptr, Hlen, Hbytes, Hdata,
    Hbump, Hstreams, Hcont⟩
  isimp only [HeaderCont] at Hcont
  simp only [headerStage]
  iapply twp_block
  simp only [headerPhase]
  iapply twp_block
  simp only [List.drop_zero]
  rw [headerError_shape]
  have hexit1 : branchTarget? arity 1 (headerFrame :: outerControls) [] =
      some (exitCode, exitControls, exitValues) := hexit
  by_cases hlong : (3 : UInt32) < len
  · -- four bytes or more: the guard leaves the error block
    obtain ⟨hh4, hh4a, hh4b, hh4c⟩ := offset_facts hdr 4 4 rfl (by omega)
    have hfour : 4 ≤ bytes.length := by
      have h := UInt32.lt_iff_toNat_lt.mp hlong
      have h3 : (3 : UInt32).toNat = 3 := rfl
      omega
    simp only [headerBuild, List.cons_append, List.nil_append]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := hdr) (offset := 4) len
      hh4 hh4a hh4b hh4c with Hlen
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    iapply twp_gtU (result := 1) (by rw [if_pos hlong])
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    rw [headerRead_shape]
    iapply twp_header_advance out hdr frame ptr len bytes l4 l5 l6 l7 l8 l9
      l10 l11 l12 hlong hbytesLength hhdrNowrap
    isplitl_exacts [Hptr Hlen Hbytes]
    iintro Hptr Hlen Hbytes
    by_cases hzero : headerWord bytes = 0
    · -- the count is zero, so the vector is empty
      rw [hzero]
      iapply twp_brIfZero
      wasm_twp_pures [twp_exitControl]
        using [List.take_zero, List.nil_append]
      rw [emptyResult_shape]
      iapply twp_empty_result out hdr outBefore (.i32 frame) (.i32 ptr) l4
        (.i32 (len - 4)) (.i32 (ptr + 4)) (.i32 0) l8 l9 l10 l11 l12
        houtLength houtNowrap
      isplitl_exact Hout
      iintro Hout
      iapply twp_br hexit1
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hempty := BI.and_elim_l $$ Htail
      iapply Hempty $$ Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hbytes Hdata
        Hbump Hstreams %⟨trivial, hfour⟩
    · -- the count is not zero, so the allocation follows
      iapply twp_brIf hzero
        ((branchTarget_succ arity 0 _ (headerFrame :: outerControls) []).trans
          hafter)
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Htail := BI.and_elim_r $$ Htail
      ihave Hnonzero := BI.and_elim_l $$ Htail
      iapply Hnonzero $$ Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hbytes
        Hdata Hbump Hstreams %⟨hzero, hfour⟩
  · -- fewer than four bytes: the error arm
    iapply twp_header_error out hdr frame len heapId frameBytes outBefore
      below dataBytes storedCursor frontier history input output raised
      l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 hlong hframeLength houtLength
      hdataLength hframeLow hframeNowrap houtNowrap hhdrNowrap
    isplitl_exacts [Hruntime Hsp Hbelow Hframe Hout Hlen Hdata Hbump
      Hstreams]
    isplit
    · iintro %word0 %word1 %word2 %word3 %frameAfter %below' %storedCursor'
        %frontier' %history' Hruntime Hsp Hbelow Hframe Hout Hlen Hdata
        Hbump Hstreams %hfacts
      iapply twp_br
        ((branchTarget_succ arity 2 _ _ []).trans
          ((branchTarget_succ arity 1 _ _ []).trans hexit1))
      ihave Herror := BI.and_elim_l $$ Hcont
      ihave Herror := Herror $$ %word0 %word1 %word2 %word3 %frameAfter
        %below' %storedCursor' %frontier' %history'
      iapply Herror $$ Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hbytes Hdata
        Hbump Hstreams %hfacts
    · iintro %remaining' Hstreams
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Htail := BI.and_elim_r $$ Htail
      ihave Hoom := BI.and_elim_r $$ Htail
      iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.Decoder
