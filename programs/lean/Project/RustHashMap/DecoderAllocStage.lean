import Project.RustHashMap.DecoderDecodeStage
import Project.RustHashMap.DecoderOkBranch

/-!
# The allocation stage of the decoder

`Project.RustHashMap.Decoder.allocStage` is the decode block and then the
dead allocation-failure arm.  The block frame of the decode block has
`deadAllocError` as its continuation, and nothing reaches it, because the
allocation either gives a buffer or traps.

The stage runs the decode stage and then closes the accepting arm of the
loop with the accepting return.  Two arms are left for the caller:

1. the accepting exit, after the return branched out of both blocks;
2. the error exit, at the continuation of the allocation block.

The out-of-memory trap of the allocation is the third arm.

The branch of the accepting return leaves two blocks, so its target is the
frame above the allocation block.  That frame belongs to the caller, and
the caller gives the target as `hokTarget`.
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
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-- The continuation of the allocation stage.  The first arm is the
accepting exit, where the output slot holds the tag and the three vector
words.  The second arm is the error exit, which both error paths of the
loop take.  The third arm is the out-of-memory trap of the allocation. -/
def AllocCont [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (okCode : Program) (okControls : List ControlFrame)
    (okValues : List Value)
    (errorCont : Program) (errorControls : List ControlFrame)
    (errorBelow : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ capacity : UInt32, ∀ buffer : UInt32, ∀ allocationId : Nat,
      ∀ blockBytes : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      ∀ l10' : Value, ∀ l11' : Value, ∀ l12' : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame (decoderDepth - 64) below' -∗
      Slices.ByteSlice 0 frame pad -∗
      pointsTo_u32 0 (frame + 4) capacity -∗
      pointsTo_u32 0 (frame + 8) buffer -∗
      pointsTo_u32 0 (frame + 12) count -∗
      Slices.ByteSlice 0 (frame + 16) scratch -∗
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
        blockBytes.take (8 * count.toNat) = payload bytes count.toNat⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 count, .i32 (frame + 52),
                .i32 (len - UInt32.ofNat (4 + 8 * count.toNat)),
                .i32 (ptr + UInt32.ofNat (4 + 8 * count.toNat)), .i32 count,
                .i32 buffer, .i32 (UInt32.ofNat (8 * count.toNat + 4)),
                l10', l11', l12'],
            okValues⟩,
            okCode, arity, remainder, okControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
  ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
      ∀ word3 : UInt32,
      ∀ hdrPtr : UInt32, ∀ hdrLen : UInt32, ∀ capacity : UInt32,
      ∀ buffer : UInt32, ∀ length : UInt32,
      ∀ scratchAfter : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      ∀ l3' : Value, ∀ l5' : Value, ∀ l6' : Value, ∀ l9' : Value,
      ∀ l10' : Value, ∀ l12' : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame (decoderDepth - 64) below' -∗
      Slices.ByteSlice 0 frame pad -∗
      pointsTo_u32 0 (frame + 4) capacity -∗
      pointsTo_u32 0 (frame + 8) buffer -∗
      pointsTo_u32 0 (frame + 12) length -∗
      Slices.ByteSlice 0 (frame + 16)
        (WordCodec.u32le.serialize [word0, word1, word2, word3] ++
          scratchAfter) -∗
      Slices.ByteSlice 0 out outBefore -∗
      pointsTo_u32 0 hdr hdrPtr -∗
      pointsTo_u32 0 (hdr + 4) hdrLen -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜word0 ≠ okTag ∧ scratchAfter.length = 32⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3', .i32 (frame + 52), l5', l6', .i32 count,
                .i32 buffer, l9', l10', .i32 word0, l12'],
            errorBelow⟩,
            errorCont, arity, remainder, errorControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
    (∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage)))))

set_option maxHeartbeats 2000000 in
/-- The allocation stage allocates the pair buffer, runs the loop, and
writes the output slot on the accepting path. -/
theorem twp_alloc_stage [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes below : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (word4 word8 word12 aux10 aux11 aux12 : UInt32)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (l3 l4 l8 l9 : Value)
    (arity : Nat) (remainder : List Value)
    (okCode : Program) (okControls : List ControlFrame)
    (okValues : List Value)
    (errorBody errorCont : Program) (errorBelow : List Value)
    (errorControls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hcount : count ≠ 0)
    (hlen : bytes.length = len.toNat)
    (hfour : 4 ≤ bytes.length)
    (houtLength : outBefore.length = 16)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hscratchLength : scratch.length = 48)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hptrNowrap : ptr.toNat + bytes.length < UInt32.size)
    (hokTarget : branchTarget? arity 0 errorControls [] =
      some (okCode, okControls, okValues)) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame (decoderDepth - 64) below ∗
      Slices.ByteSlice 0 frame pad ∗
      pointsTo_u32 0 (frame + 4) word4 ∗
      pointsTo_u32 0 (frame + 8) word8 ∗
      pointsTo_u32 0 (frame + 12) word12 ∗
      Slices.ByteSlice 0 (frame + 16) scratch ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 hdr (ptr + 4) ∗
      pointsTo_u32 0 (hdr + 4) (len - 4) ∗
      Slices.ByteSlice 0 ptr bytes ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      AllocCont out hdr ptr len frame count heapId bytes outBefore pad
        scratch dataBytes input output raised arity remainder okCode
        okControls okValues errorCont errorControls errorBelow calls s E
        Φ) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, .i32 (len - 4), .i32 (ptr + 4),
                .i32 count, l8, l9, .i32 aux10, .i32 aux11, .i32 aux12], []⟩,
            allocStage, arity, remainder,
            allocFrame errorBody errorCont errorBelow :: errorControls,
            calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hpad, Hcapacity, Hbuffer, Hlength, Hscratch,
    Hout, Hhdr, Hlen, Hinput, Hdata, Hbump, Hstreams, Hcont⟩
  simp only [allocStage]
  iapply twp_block
  iapply twp_decode_stage out hdr ptr len frame count heapId bytes outBefore
    pad scratch dataBytes below input output raised word4 word8 word12
    aux10 aux11 aux12 storedCursor frontier history l3 l4 l8 l9 arity
    remainder
    _ errorBody errorCont errorBelow
    errorControls calls s E Φ hcount hlen hfour hscratchLength hdataLength
    hframeLow hframeNowrap hhdrNowrap hptrNowrap
  isplitl_exacts [Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength Hscratch
    Hout Hhdr Hlen Hinput Hdata Hbump Hstreams]
  isimp only [AllocCont] at Hcont
  isimp only [LoopCont]
  isplit
  · iintro %capacity %buffer %allocationId %blockBytes %below'
      %storedCursor' %frontier' %history' %l10' %l11' %l12'
      Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength Hscratch Hout Hhdr
      Hlen Hinput Hdata Hblock Hbump Hstreams %hfacts
    iapply twp_ok_return out hdr frame capacity buffer count outBefore
      (.i32 count) (.i32 (frame + 52))
      (.i32 (len - UInt32.ofNat (4 + 8 * count.toNat)))
      (.i32 (ptr + UInt32.ofNat (4 + 8 * count.toNat))) (.i32 count)
      (.i32 buffer) (.i32 (UInt32.ofNat (8 * count.toNat + 4)))
      l10' l11' l12' okCode okControls okValues houtLength houtNowrap
      hframeNowrap hokTarget
    isplitl_exacts [Hout Hcapacity Hbuffer Hlength]
    iintro Hout Hcapacity Hbuffer Hlength
    ihave Hok := BI.and_elim_l $$ Hcont
    ihave Hok := Hok $$ %capacity %buffer %allocationId %blockBytes %below'
      %storedCursor' %frontier' %history' %l10' %l11' %l12'
    iapply Hok $$ Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength Hscratch
      Hout Hhdr Hlen Hinput Hdata Hblock Hbump Hstreams %hfacts
  · ihave Htail := BI.and_elim_r $$ Hcont
    iexact Htail

end Project.RustHashMap.Decoder
