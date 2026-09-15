import Project.RustHashMap.DecoderAllocPhase
import Project.RustHashMap.DecoderHeaderStage

/-!
# The body of the decoder

`Project.RustHashMap.Decoder.outerBody` is the whole body of the decoder
below the frame.  It is the header stage and the allocation phase.

The body has two exits, and both are at the continuation of the block
that holds it:

1. the accepting exit, which the empty vector and the accepting return of
   the loop both reach;
2. the rejecting exit, which the short-input error and the error return
   both reach.

The out-of-memory trap is the third arm.

The two stages report the same two exits in four arms, so this file
merges them.  The merge is what makes the continuation the shape of
`Project.RustHashMap.BodyContracts.Func1Spec`: the accepting exit owns
the pair buffer as one slice, and the rejecting exit carries
`¬ DecodeAccepts bytes`.
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

/-! ## Small facts -/

/-- A byte slice carries the fact that its range does not wrap. -/
private theorem ByteSlice_nowrap [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(⌜ptr.toNat + bytes.length < UInt32.size⌝ ∗
        Slices.ByteSlice 0 ptr bytes) := by
  unfold Slices.ByteSlice
  iintro ⟨%hbound, Hraw⟩
  isplitl_pureexact hbound
  isplitl_pureexact hbound
  iexact Hraw

/-- The empty slice costs nothing. -/
private theorem ByteSlice_nil [WasmHeapGS Universal.State] (ptr : UInt32) :
    (emp : HeapIProp) ⊢ Slices.ByteSlice 0 ptr [] := by
  unfold Slices.ByteSlice
  iintro Hemp
  isplit
  · ipureintro
    simpa using ptr.toNat_lt_size
  · iapply (pointsToBytes_nil 0 ptr).mpr
    iexact Hemp

/-- A count of zero advances the cursor by four bytes alone. -/
private theorem add_mul_zero (a : UInt32) : a + 8 * (0 : UInt32) = a := by
  have h : (8 : UInt32) * 0 = 0 := rfl
  rw [h, UInt32.add_zero]

/-- A count of zero takes four bytes off the length alone. -/
private theorem sub_mul_zero (a : UInt32) : a - 8 * (0 : UInt32) = a := by
  have h : (8 : UInt32) * 0 = 0 := rfl
  rw [h, UInt32.sub_zero]

/-- A word that is not zero has a count that is not zero. -/
private theorem nonzero_toNat (a : UInt32) (h : a ≠ 0) : a.toNat ≠ 0 := by
  intro hzero
  exact h (UInt32.toNat_inj.mp hzero)

/-- The pair block holds eight bytes for each pair. -/
private theorem pairBlock_size (capacity : Nat) :
    (pairBlock capacity).size = 8 * capacity := rfl

/-- A count of zero reads no payload. -/
private theorem payload_zero (bytes : List UInt8) :
    payload bytes (0 : UInt32).toNat = [] := by
  simp [payload]

/-! ## The cursor after the pairs -/

/-- Two subtractions are one subtraction of the sum, on a bit vector. -/
private theorem bitvec_sub_sum (a b c : BitVec 32) :
    a - (b + c) = a - b - c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- Two subtractions are one subtraction of the sum. -/
private theorem uint32_sub_sum (a b c : UInt32) :
    a - (b + c) = a - b - c := by
  apply UInt32.toBitVec_inj.mp
  rw [UInt32.toBitVec_sub, UInt32.toBitVec_sub, UInt32.toBitVec_sub,
    UInt32.toBitVec_add]
  exact bitvec_sub_sum _ _ _

/-- The header and the pairs together are four bytes and eight bytes for
each pair. -/
private theorem step_word (count : UInt32) :
    UInt32.ofNat (4 + 8 * count.toNat) = 4 + 8 * count := by
  simp [UInt32.ofNat_add, UInt32.ofNat_mul]

/-- The cursor after the pairs. -/
private theorem cursor_shift (ptr count : UInt32) :
    ptr + UInt32.ofNat (4 + 8 * count.toNat) = ptr + 4 + 8 * count := by
  rw [step_word, UInt32.add_assoc]

/-- The unread length after the pairs. -/
private theorem remaining_shift (len count : UInt32) :
    len - UInt32.ofNat (4 + 8 * count.toNat) = len - 4 - 8 * count := by
  rw [step_word, uint32_sub_sum]

/-! ## The continuation of the body -/

/-- The continuation of the body of the decoder.  The first arm is the
accepting exit, where the output slot holds the tag and the three vector
words and the caller owns the pair buffer.  The second arm is the
rejecting exit, and it carries the fact that the input does not hold
every pair that the header announces.  The third arm is the
out-of-memory trap.

Both arms leave locals 3 to 12 open, because the four exits of the two
stages do not agree on them.  The epilogue reads local 2 alone. -/
def BodyCont [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame : UInt32) (heapId : GName)
    (bytes dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (afterBlock : Program) (controls : List ControlFrame)
    (belowStack : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ capacity : UInt32, ∀ buffer : UInt32,
      ∀ payloadBytes : List UInt8, ∀ spareBytes : List UInt8,
      ∀ frameAfter : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory, ∀ r3 : Value, ∀ r4 : Value,
      ∀ r5 : Value, ∀ r6 : Value, ∀ r7 : Value, ∀ r8 : Value,
      ∀ r9 : Value, ∀ r10 : Value, ∀ r11 : Value, ∀ r12 : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame func49Depth below' -∗
      Slices.ByteSlice 0 frame frameAfter -∗
      Slices.ByteSlice 0 out
        (WordCodec.u32le.serialize
          [okTag, capacity, buffer, headerWord bytes]) -∗
      pointsTo_u32 0 hdr (ptr + 4 + 8 * headerWord bytes) -∗
      pointsTo_u32 0 (hdr + 4) (len - 4 - 8 * headerWord bytes) -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      Slices.ByteSlice 0 buffer (payloadBytes ++ spareBytes) -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜DecodeAccepts bytes ∧ frameAfter.length = 64 ∧
        payloadBytes = payload bytes (headerWord bytes).toNat ∧
        (headerWord bytes).toNat ≤ capacity.toNat ∧
        spareBytes.length =
          8 * (capacity.toNat - (headerWord bytes).toNat) ∧
        ((headerWord bytes).toNat = 0 → capacity = 0) ∧
        buffer.toNat % 4 = 0⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12],
            belowStack⟩,
            afterBlock, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
  ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
      ∀ word3 : UInt32, ∀ hdrPtr : UInt32, ∀ hdrLen : UInt32,
      ∀ frameAfter : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory, ∀ r3 : Value, ∀ r4 : Value,
      ∀ r5 : Value, ∀ r6 : Value, ∀ r7 : Value, ∀ r8 : Value,
      ∀ r9 : Value, ∀ r10 : Value, ∀ r11 : Value, ∀ r12 : Value,
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
      ⌜¬ DecodeAccepts bytes ∧ word0 ≠ okTag ∧
        frameAfter.length = 64⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12],
            belowStack⟩,
            afterBlock, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
    (∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage)))))

set_option maxHeartbeats 2000000 in
/-- The body of the decoder runs the header stage and the allocation
phase, and merges their four exits into two. -/
theorem twp_outer_body [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame : UInt32) (heapId : GName)
    (frameBytes outBefore below dataBytes bytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l3 l4 l5 l6 l7 l8 l9 : Value) (aux10 aux11 aux12 : UInt32)
    (arity : Nat) (remainder : List Value)
    (blockBody afterBlock : Program) (controls : List ControlFrame)
    (belowStack : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hframeLength : frameBytes.length = 64)
    (houtLength : outBefore.length = 16)
    (hbytesLength : bytes.length = len.toNat)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size) :
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
      BodyCont out hdr ptr len frame heapId bytes dataBytes input output
        raised arity remainder afterBlock controls belowStack calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, l8, l9, .i32 aux10,
                .i32 aux11, .i32 aux12], []⟩,
            outerBody, arity, remainder,
            { kind := .block, paramArity := 0, resultArity := 0,
              body := blockBody, continuation := afterBlock,
              belowStack := belowStack } :: controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hframe, Hout, Hptr, Hlen, Hbytes, Hdata,
    Hbump, Hstreams, Hcont⟩
  ihave ⟨%hptrNowrap, Hinput⟩ := ByteSlice_nowrap ptr bytes $$ Hbytes
  isimp only [BodyCont] at Hcont
  simp only [outerBody]
  iapply twp_block
  simp only [List.drop_zero]
  have hexit : branchTarget? arity 0
      ({ kind := .block, paramArity := 0, resultArity := 0,
          body := blockBody, continuation := afterBlock,
          belowStack := belowStack } :: controls) [] =
        some (afterBlock, controls, belowStack) := rfl
  have hafter : branchTarget? arity 0
      ({ kind := .block, paramArity := 0, resultArity := 0,
          body := headerStage,
          continuation := .call 33 :: .block 0 0 allocStage :: errorReturn,
          belowStack := ([] : List Value) } ::
        { kind := .block, paramArity := 0, resultArity := 0,
          body := blockBody, continuation := afterBlock,
          belowStack := belowStack } :: controls) [] =
        some (.call 33 :: .block 0 0 allocStage :: errorReturn,
          { kind := .block, paramArity := 0, resultArity := 0,
            body := blockBody, continuation := afterBlock,
            belowStack := belowStack } :: controls, ([] : List Value)) := rfl
  iapply twp_header_stage out hdr ptr len frame heapId frameBytes outBefore
    below dataBytes bytes storedCursor frontier history input output raised
    l3 l4 l5 l6 l7 l8 l9 (.i32 aux10) (.i32 aux11) (.i32 aux12) _
    ({ kind := .block, paramArity := 0, resultArity := 0,
        body := blockBody, continuation := afterBlock,
        belowStack := belowStack } :: controls)
    arity remainder afterBlock controls belowStack
    (.call 33 :: .block 0 0 allocStage :: errorReturn)
    ({ kind := .block, paramArity := 0, resultArity := 0,
        body := blockBody, continuation := afterBlock,
        belowStack := belowStack } :: controls) []
    calls s E Φ hframeLength houtLength hbytesLength hdataLength hframeLow
    hframeNowrap houtNowrap hhdrNowrap hexit hafter
  isplitl_exacts [Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput Hdata
    Hbump Hstreams]
  isimp only [HeaderCont]
  isplit
  · -- the short input: fewer than four bytes
    iintro %word0 %word1 %word2 %word3 %frameAfter %below' %storedCursor'
      %frontier' %history' Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput
      Hdata Hbump Hstreams %hfacts
    have hreject : ¬ DecodeAccepts bytes := by
      intro haccept
      have h4 := haccept.1
      have hshort := hfacts.2.2
      omega
    ihave Htail := BI.and_elim_r $$ Hcont
    ihave Hbad := BI.and_elim_l $$ Htail
    ihave Hbad := Hbad $$ %word0 %word1 %word2 %word3 %ptr %len %frameAfter
      %below' %storedCursor' %frontier' %history'
      %(.i32 word0) %(.i32 word1) %l5 %l6 %l7 %l8 %l9 %(.i32 aux10)
      %(.i32 aux11) %(.i32 aux12)
    iapply Hbad $$ Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput Hdata
      Hbump Hstreams %⟨hreject, hfacts.1, hfacts.2.1⟩
  · isplit
    · -- the empty vector
      iintro Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput Hdata Hbump
        Hstreams %hfacts
      ihave Hok := BI.and_elim_l $$ Hcont
      ihave Hbuf : Slices.ByteSlice 0 (4 : UInt32) [] $$ []
      · iapply ByteSlice_nil
        itrivial
      isimp only [hfacts.1, add_mul_zero, sub_mul_zero] at Hok
      ihave Hok := Hok $$ %(0 : UInt32) %(4 : UInt32) %([] : List UInt8)
        %([] : List UInt8) %frameBytes %below %storedCursor %frontier
        %history
        %(.i32 ptr) %l4 %(.i32 (len - 4)) %(.i32 (ptr + 4)) %(.i32 0)
        %l8 %l9 %(.i32 aux10) %(.i32 aux11) %(.i32 aux12)
      isimp only [List.nil_append] at Hok
      have haccept : DecodeAccepts bytes := by
        refine ⟨hfacts.2, ?_⟩
        rw [hfacts.1]
        simpa using hfacts.2
      iapply Hok $$ Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput Hdata
        Hbuf Hbump Hstreams
        %⟨haccept, hframeLength, (payload_zero bytes).symm,
          Nat.le_refl _, by simp, fun _ => trivial, by decide⟩
    · isplit
      · -- the count that is not zero: the allocation phase
        iintro Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput Hdata Hbump
          Hstreams %hfacts
        iapply twp_alloc_phase out hdr ptr len frame (headerWord bytes)
          heapId bytes outBefore frameBytes dataBytes below input output
          raised aux10 aux11 aux12 storedCursor frontier history l4 l8 l9
          arity remainder blockBody afterBlock controls belowStack calls
          s E Φ hfacts.1 hbytesLength hfacts.2 hframeLength houtLength
          hdataLength hframeLow hframeNowrap houtNowrap hhdrNowrap
          hptrNowrap
        isplitl_exacts [Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hinput
          Hdata Hbump Hstreams]
        isimp only [PhaseCont]
        have hnz : (headerWord bytes).toNat ≠ 0 :=
          nonzero_toNat _ hfacts.1
        isplit
        · -- the accepting exit of the loop
          iintro %capacity %buffer %allocationId %blockBytes %frameAfter
            %below' %storedCursor' %frontier' %history' %l10' %l11' %l12'
            Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hinput Hdata Hblock
            Hbump Hstreams %hfacts2
          ihave ⟨Htoken, Hbuf, %hblock⟩ :=
            (LiveBlock_open heapId allocationId buffer
              (pairBlock capacity.toNat) blockBytes).mp $$ Hblock
          have hblockLen : blockBytes.length = 8 * capacity.toNat := by
            rw [hblock.1, pairBlock_size]
          obtain ⟨payloadBytes, spareBytes, hjoin, hpayEq, hspareLen⟩ :
              ∃ p q : List UInt8, p ++ q = blockBytes ∧
                p = blockBytes.take (8 * (headerWord bytes).toNat) ∧
                q.length =
                  8 * (capacity.toNat - (headerWord bytes).toNat) :=
            ⟨_, _, List.take_append_drop _ _, rfl, by
              rw [List.length_drop, hblockLen]
              omega⟩
          isimp only [← hjoin] at Hbuf
          isimp only [cursor_shift] at Hhdr
          isimp only [remaining_shift] at Hlen
          have haccept : DecodeAccepts bytes := by
            refine ⟨?_, hfacts2.2.1⟩
            have h := hfacts2.2.1
            omega
          have hpayload :
              payloadBytes = payload bytes (headerWord bytes).toNat :=
            hpayEq.trans hfacts2.2.2.1
          ihave Hok := BI.and_elim_l $$ Hcont
          ihave Hok := Hok $$ %capacity %buffer %payloadBytes %spareBytes
            %frameAfter %below' %storedCursor' %frontier' %history'
            %(.i32 (headerWord bytes)) %(.i32 (frame + 52))
            %(.i32 (len -
              UInt32.ofNat (4 + 8 * (headerWord bytes).toNat)))
            %(.i32 (ptr +
              UInt32.ofNat (4 + 8 * (headerWord bytes).toNat)))
            %(.i32 (headerWord bytes)) %(.i32 buffer)
            %(.i32 (UInt32.ofNat (8 * (headerWord bytes).toNat + 4)))
            %l10' %l11' %l12'
          iapply Hok $$ Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hinput
            Hdata Hbuf Hbump Hstreams
            %⟨haccept, hfacts2.2.2.2, hpayload, hfacts2.1, hspareLen,
              fun h => absurd h hnz, hblock.2.2⟩
        · isplit
          · -- the error exit of the allocation phase
            iintro %word0 %word1 %word2 %word3 %hdrPtr %hdrLen %capacity
              %buffer %frameAfter %below' %storedCursor' %frontier'
              %history' %l4' %l5' %l6' %l7' %l9' %l10' %l12'
              Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hinput Hdata Hbump
              Hstreams %hfacts2
            have hreject : ¬ DecodeAccepts bytes := by
              intro haccept
              have h := haccept.2
              have hshort := hfacts2.2.2
              omega
            ihave Htail := BI.and_elim_r $$ Hcont
            ihave Hbad := BI.and_elim_l $$ Htail
            ihave Hbad := Hbad $$ %word0 %word1 %word2 %word3 %hdrPtr
              %hdrLen %frameAfter %below' %storedCursor' %frontier'
              %history'
              %(.i32 capacity) %l4' %l5' %l6' %l7' %(.i32 buffer) %l9'
              %l10' %(.i32 word0) %l12'
            iapply Hbad $$ Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hinput
              Hdata Hbump Hstreams
              %⟨hreject, hfacts2.1, hfacts2.2.1⟩
          · -- the out-of-memory trap of the allocation
            iintro %remaining' Hstreams
            ihave Htail := BI.and_elim_r $$ Hcont
            ihave Hoom := BI.and_elim_r $$ Htail
            iapply Hoom $$ %remaining' Hstreams
      · -- the out-of-memory trap of the error build
        iintro %remaining' Hstreams
        ihave Htail := BI.and_elim_r $$ Hcont
        ihave Hoom := BI.and_elim_r $$ Htail
        iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.Decoder
