import Project.RustHashMap.DecoderAllocStage
import Project.RustHashMap.DecoderErrorReturn
import Project.RustHashMap.Func30Proof

/-!
# The allocation phase of the decoder

The phase is the part of the body of the decoder that follows the header
stage.  It is the empty marker call of absolute `func 33`, the block that
holds the allocation stage, and the error return that follows it.

The phase has two exits, and both are at the continuation of the block
that holds the body of the decoder:

1. the accepting exit, which the accepting return of the loop branches
   to;
2. the error exit, which the error return reaches when it falls out of
   the allocation block.

The out-of-memory trap of the allocation is the third arm.

The frame comes in as 64 bytes and goes out as 64 bytes.  The allocation
stage wants the three vector words as cells, so the proof cuts the frame
into the pad, the three words, and the 48-byte scratch slot, and joins it
again on each exit.
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
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-! ## The frame, in pieces -/

/-- The 64 frame bytes, as the pad, the three vector words, and the
scratch slot. -/
private theorem frame_pieces64 (bytes : List UInt8)
    (hlength : bytes.length = 64) :
    ∃ pad mid scratch : List UInt8,
      bytes = pad ++ (mid ++ scratch) ∧
      pad.length = 4 ∧ mid.length = 12 ∧ scratch.length = 48 := by
  refine ⟨bytes.take 4, (bytes.drop 4).take 12, (bytes.drop 4).drop 12,
    by simp only [List.take_append_drop], ?_, ?_, ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

/-- The frame splits into the pad, the three vector words, and the
scratch slot. -/
private theorem frame_split64 [WasmHeapGS Universal.State]
    (frame w4 w8 w12 : UInt32) (pad scratch : List UInt8)
    (hpadLength : pad.length = 4) :
    Slices.ByteSlice 0 frame
        (pad ++ (WordCodec.u32le.serialize [w4, w8, w12] ++ scratch)) ⊢
      iprop(Slices.ByteSlice 0 frame pad ∗
        pointsTo_u32 0 (frame + 4) w4 ∗
        pointsTo_u32 0 (frame + 8) w8 ∗
        pointsTo_u32 0 (frame + 12) w12 ∗
        Slices.ByteSlice 0 (frame + 16) scratch) := by
  iintro Hframe
  have ha4 : frame + UInt32.ofNat 4 = frame + 4 := rfl
  have ha16 : frame + (4 : UInt32) + UInt32.ofNat 12 = frame + 16 :=
    frame_offset frame 4 12 16 rfl
  have hser : (WordCodec.u32le.serialize [w4, w8, w12]).length = 12 := by
    simp only [WordCodec.u32le_serialize_length, List.length_cons,
      List.length_nil]
  ihave ⟨Hpad, Hrest⟩ :=
    (Slices.ByteSlice_append 0 frame pad
      (WordCodec.u32le.serialize [w4, w8, w12] ++ scratch)).mp $$ Hframe
  isimp only [hpadLength, ha4] at Hrest
  ihave ⟨Hmid, Hscratch⟩ :=
    (Slices.ByteSlice_append 0 (frame + 4)
      (WordCodec.u32le.serialize [w4, w8, w12]) scratch).mp $$ Hrest
  isimp only [hser, ha16] at Hscratch
  ihave ⟨H4, H8, H12⟩ := frame_words_split frame w4 w8 w12 $$ Hmid
  iframe Hpad H4 H8 H12 Hscratch

/-- The pad, the three vector words, and the scratch slot join into the
frame again. -/
private theorem frame_join64 [WasmHeapGS Universal.State]
    (frame w4 w8 w12 : UInt32) (pad scratch : List UInt8)
    (hpadLength : pad.length = 4)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(Slices.ByteSlice 0 frame pad ∗
      pointsTo_u32 0 (frame + 4) w4 ∗
      pointsTo_u32 0 (frame + 8) w8 ∗
      pointsTo_u32 0 (frame + 12) w12 ∗
      Slices.ByteSlice 0 (frame + 16) scratch) ⊢
      Slices.ByteSlice 0 frame
        (pad ++ (WordCodec.u32le.serialize [w4, w8, w12] ++ scratch)) := by
  iintro ⟨Hpad, H4, H8, H12, Hscratch⟩
  have ha4 : frame + UInt32.ofNat 4 = frame + 4 := rfl
  have ha16 : frame + (4 : UInt32) + UInt32.ofNat 12 = frame + 16 :=
    frame_offset frame 4 12 16 rfl
  have hser : (WordCodec.u32le.serialize [w4, w8, w12]).length = 12 := by
    simp only [WordCodec.u32le_serialize_length, List.length_cons,
      List.length_nil]
  ihave Hmid := frame_words_join frame w4 w8 w12 hframeNowrap $$ [H4 H8 H12]
  · iframe H4 H8 H12
  ihave Hrest :=
    (Slices.ByteSlice_append 0 (frame + 4)
      (WordCodec.u32le.serialize [w4, w8, w12]) scratch).mpr $$
      [Hmid Hscratch]
  · isplitl_exact Hmid
    · isimp only [hser, ha16]
      iexact Hscratch
  iapply (Slices.ByteSlice_append 0 frame pad
    (WordCodec.u32le.serialize [w4, w8, w12] ++ scratch)).mpr
  isplitl_exact Hpad
  · isimp only [hpadLength, ha4]
    iexact Hrest

/-- The frame that the allocation block pushes. -/
private theorem allocFrame_shape :
    ({ kind := .block, paramArity := 0, resultArity := 0,
        body := allocStage, continuation := errorReturn,
        belowStack := ([] : List Value) } : ControlFrame)
      = allocFrame allocStage errorReturn [] := rfl

/-! ## The contract -/

/-- The continuation of the allocation phase.  The first arm is the
accepting exit, where the output slot holds the tag and the three vector
words.  The second arm is the error exit, and it carries the fact that
the input is too short for the pairs that the header announces.  Both are
at the continuation of the block that holds the body of the decoder.  The
third arm is the out-of-memory trap of the allocation. -/
def PhaseCont [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (afterBlock : Program) (controls : List ControlFrame)
    (belowStack : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ capacity : UInt32, ∀ buffer : UInt32, ∀ allocationId : Nat,
      ∀ blockBytes : List UInt8, ∀ frameAfter : List UInt8,
      ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      ∀ l10' : Value, ∀ l11' : Value, ∀ l12' : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame func49Depth below' -∗
      Slices.ByteSlice 0 frame frameAfter -∗
      Slices.ByteSlice 0 out
        (WordCodec.u32le.serialize [okTag, capacity, buffer, count]) -∗
      pointsTo_u32 0 hdr (ptr + UInt32.ofNat (4 + 8 * count.toNat)) -∗
      pointsTo_u32 0 (hdr + 4) (len - UInt32.ofNat (4 + 8 * count.toNat)) -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      LiveBlock heapId allocationId buffer (pairBlock capacity.toNat)
        blockBytes -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜count.toNat ≤ capacity.toNat ∧
        4 + 8 * count.toNat ≤ bytes.length ∧
        blockBytes.take (8 * count.toNat) = payload bytes count.toNat ∧
        frameAfter.length = 64⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 count, .i32 (frame + 52),
                .i32 (len - UInt32.ofNat (4 + 8 * count.toNat)),
                .i32 (ptr + UInt32.ofNat (4 + 8 * count.toNat)), .i32 count,
                .i32 buffer, .i32 (UInt32.ofNat (8 * count.toNat + 4)),
                l10', l11', l12'],
            belowStack⟩,
            afterBlock, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
  ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32, ∀ word3 : UInt32,
      ∀ hdrPtr : UInt32, ∀ hdrLen : UInt32, ∀ capacity : UInt32,
      ∀ buffer : UInt32, ∀ frameAfter : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      ∀ l4' : Value, ∀ l5' : Value, ∀ l6' : Value, ∀ l7' : Value,
      ∀ l9' : Value, ∀ l10' : Value, ∀ l12' : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame func49Depth below' -∗
      Slices.ByteSlice 0 frame frameAfter -∗
      Slices.ByteSlice 0 out
        (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
      pointsTo_u32 0 hdr hdrPtr -∗
      pointsTo_u32 0 (hdr + 4) hdrLen -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜word0 ≠ okTag ∧ frameAfter.length = 64 ∧
        bytes.length < 4 + 8 * count.toNat⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 capacity, l4', l5', l6', l7', .i32 buffer,
                l9', l10', .i32 word0, l12'],
            belowStack⟩,
            afterBlock, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
    (∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage)))))

set_option maxHeartbeats 2000000 in
/-- The allocation phase runs the marker call, the allocation stage, and
the error return. -/
theorem twp_alloc_phase [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore frameBytes dataBytes below : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (aux10 aux11 aux12 : UInt32)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (l4 l8 l9 : Value)
    (arity : Nat) (remainder : List Value)
    (blockBody afterBlock : Program) (controls : List ControlFrame)
    (belowStack : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hcount : count ≠ 0)
    (hlen : bytes.length = len.toNat)
    (hfour : 4 ≤ bytes.length)
    (hframeLength : frameBytes.length = 64)
    (houtLength : outBefore.length = 16)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hptrNowrap : ptr.toNat + bytes.length < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame func49Depth below ∗
      Slices.ByteSlice 0 frame frameBytes ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 hdr (ptr + 4) ∗
      pointsTo_u32 0 (hdr + 4) (len - 4) ∗
      Slices.ByteSlice 0 ptr bytes ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      PhaseCont out hdr ptr len frame count heapId bytes dataBytes input
        output raised arity remainder afterBlock controls belowStack calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 ptr, l4, .i32 (len - 4), .i32 (ptr + 4),
                .i32 count, l8, l9, .i32 aux10, .i32 aux11, .i32 aux12], []⟩,
            .call 33 :: .block 0 0 allocStage :: errorReturn, arity,
            remainder,
            { kind := .block, paramArity := 0, resultArity := 0,
              body := blockBody, continuation := afterBlock,
              belowStack := belowStack } :: controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hframe, Hout, Hhdr, Hlen, Hbytes, Hdata,
    Hbump, Hstreams, Hcont⟩
  have hdepth : decoderDepth - 64 = func49Depth := rfl
  -- the frame, as the pad, the three vector words, and the scratch slot
  obtain ⟨pad, mid, scratch, hshape, hpadLen, hmidLen, hscratchLen⟩ :=
    frame_pieces64 frameBytes hframeLength
  have hmid3 : mid.length = 4 * 3 := by rw [hmidLen]
  obtain ⟨hser, hcount3⟩ :=
    Slices.u32le_serialize_decodeWords_of_length mid 3 hmid3
  obtain ⟨w4, w8, w12, hwords⟩ := three_words (Slices.decodeWords mid) hcount3
  have hmidEq : mid = WordCodec.u32le.serialize [w4, w8, w12] := by
    rw [← hwords, hser]
  rw [hmidEq] at hshape
  isimp only [hshape] at Hframe
  ihave ⟨Hpad, H4, H8, H12, Hscratch⟩ :=
    frame_split64 frame w4 w8 w12 pad scratch hpadLen $$ Hframe
  isimp only [← hdepth] at Hbelow
  -- the empty marker call of absolute `func 33`
  have Hmark : Project.RustHashMap.VecGrow.Func30Spec (hlc := hlc) :=
    Project.RustHashMap.Func30Proof.func30_correct
  unfold Project.RustHashMap.VecGrow.Func30Spec CallContract callExpr at Hmark
  simp only [List.nil_append] at Hmark
  iapply Hmark
    (callerLocals :=
      ⟨[.i32 out, .i32 hdr],
        [.i32 frame, .i32 ptr, l4, .i32 (len - 4), .i32 (ptr + 4),
          .i32 count, l8, l9, .i32 aux10, .i32 aux11, .i32 aux12], []⟩)
    (stack := [])
  isplitl_exact Hruntime
  · iintro Hruntime
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iapply twp_block
    simp only [List.drop_zero]
    rw [allocFrame_shape]
    iapply twp_alloc_stage out hdr ptr len frame count heapId bytes outBefore
      pad scratch dataBytes below input output raised w4 w8 w12 aux10 aux11
      aux12 storedCursor frontier history (.i32 ptr) l4 l8 l9 arity remainder
      afterBlock controls belowStack allocStage errorReturn []
      ({ kind := .block, paramArity := 0, resultArity := 0,
          body := blockBody, continuation := afterBlock,
          belowStack := belowStack } :: controls)
      calls s E Φ hcount hlen hfour houtLength houtNowrap hscratchLen
      hdataLength hframeLow hframeNowrap hhdrNowrap hptrNowrap (by rfl)
    isplitl_exacts [Hruntime Hsp Hbelow Hpad H4 H8 H12 Hscratch Hout Hhdr
      Hlen Hbytes Hdata Hbump Hstreams]
    isimp only [PhaseCont] at Hcont
    isimp only [AllocCont]
    isplit
    · -- the accepting exit
      iintro %capacity %buffer %allocationId %blockBytes %below'
        %storedCursor' %frontier' %history' %l10' %l11' %l12'
        Hruntime Hsp Hbelow Hpad H4 H8 H12 Hscratch Hout Hhdr Hlen Hbytes
        Hdata Hblock Hbump Hstreams %hfacts
      isimp only [hdepth] at Hbelow
      ihave Hframe := frame_join64 frame capacity buffer count pad scratch
        hpadLen hframeNowrap $$ [Hpad H4 H8 H12 Hscratch]
      · iframe Hpad H4 H8 H12 Hscratch
      obtain ⟨after, hafterEq, hafterLen⟩ :
          ∃ after : List UInt8,
            after = pad ++ (WordCodec.u32le.serialize
              [capacity, buffer, count] ++ scratch) ∧ after.length = 64 :=
        ⟨_, rfl, by simp [hpadLen, hscratchLen]⟩
      isimp only [← hafterEq] at Hframe
      ihave Hok := BI.and_elim_l $$ Hcont
      ihave Hok := Hok $$ %capacity %buffer %allocationId %blockBytes %after
        %below' %storedCursor' %frontier' %history' %l10' %l11' %l12'
      iapply Hok $$ Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hbytes Hdata
        Hblock Hbump Hstreams
        %⟨hfacts.1, hfacts.2.1, hfacts.2.2, hafterLen⟩
    · isplit
      · -- the error exit
        iintro %word0 %word1 %word2 %word3 %hdrPtr %hdrLen %capacity %buffer
          %length %scratchAfter %below' %storedCursor' %frontier' %history'
          %l3' %l5' %l6' %l9' %l10' %l12'
          Hruntime Hsp Hbelow Hpad H4 H8 H12 Hscratch Hout Hhdr Hlen Hbytes
          Hdata Hbump Hstreams %hfacts
        isimp only [hdepth] at Hbelow
        iapply twp_error_return out hdr frame capacity buffer word0 word0
          word1 word2 word3 outBefore scratchAfter l3'
          (.i32 (frame + 52)) l5' l6' (.i32 count) l9' l10' l12'
          blockBody afterBlock belowStack houtLength houtNowrap hframeNowrap
        isplitl_exacts [Hruntime Hout Hscratch H4]
        iintro Hruntime Hout Hscratch H4
        ihave Hframe := frame_join64 frame capacity buffer length pad
          (WordCodec.u32le.serialize [word0, word1, word2, word3] ++
            scratchAfter) hpadLen hframeNowrap $$ [Hpad H4 H8 H12 Hscratch]
        · iframe Hpad H4 H8 H12 Hscratch
        obtain ⟨after, hafterEq, hafterLen⟩ :
            ∃ after : List UInt8,
              after = pad ++ (WordCodec.u32le.serialize
                  [capacity, buffer, length] ++
                (WordCodec.u32le.serialize [word0, word1, word2, word3] ++
                  scratchAfter)) ∧ after.length = 64 :=
          ⟨_, rfl, by simp [hpadLen, hfacts.2.1]⟩
        isimp only [← hafterEq] at Hframe
        ihave Htail := BI.and_elim_r $$ Hcont
        ihave Herror := BI.and_elim_l $$ Htail
        ihave Herror := Herror $$ %word0 %word1 %word2 %word3 %hdrPtr %hdrLen
          %capacity %buffer %after %below' %storedCursor' %frontier'
          %history' %(.i32 (frame + 52)) %l5' %l6' %(.i32 count) %l9' %l10'
          %l12'
        iapply Herror $$ Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hbytes
          Hdata Hbump Hstreams %⟨hfacts.1, hafterLen, hfacts.2.2⟩
      · -- the out-of-memory trap
        iintro %remaining' Hstreams
        ihave Htail := BI.and_elim_r $$ Hcont
        ihave Hoom := BI.and_elim_r $$ Htail
        iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.Decoder
