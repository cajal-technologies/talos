import Project.RustHashMap.DecoderShortPair

/-!
# The borsh decoder: the short-input arm of the value read

A loop step reads the key first and the value second.  Fewer than four
bytes left after the key is the same "unexpected end of input" error, at
WAT lines 696 to 743.  `Project.RustHashMap.Decoder.shortValueError` is
that arm.

The arm is `Project.RustHashMap.Decoder.shortPairError` with four changes:

1. It has no guard.  The key read branches here.
2. It sets local 12, the value, to zero.
3. It keeps word 0 of the `io::Error` in local 11 and not in local 10.
4. It tests word 0 of the decode error with `i32.ne` and not with
   `i32.eq`.  The test is true, so the `br_if 4` after it leaves the whole
   loop through the error return, and the `br 1` after that is dead.

`shortValueBuild` below stops at the `i32.ne`, so the lemma holds for any
control stack.  It leaves the answer 1 on the stack, and the caller takes
the branch.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DecodeErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- The short-input arm of the value read, without the branch that leaves
the loop and the dead branch after it. -/
def shortValueBuild : Program :=
  [.localGet 2, .const 48, .add, .const 17, .const 1049080, .const 27,
    .call 55, .localGet 2, .localGet 4, .load64 0, .store64 32, .localGet 2,
    .localGet 4, .load32 8, .store32 40, .const 0, .localSet 12,
    .localGet 2, .load32 48, .localTee 11, .const 2147483649, .eq, .br_if 1,
    .localGet 4, .localGet 2, .load64 32, .store64 0, .localGet 4,
    .localGet 2, .load32 40, .store32 8, .localGet 2, .localGet 11,
    .store32 48, .localGet 2, .const 16, .add, .localGet 2, .const 48, .add,
    .call 52, .localGet 2, .load32 16, .localTee 11, .const 2147483649, .ne]

/-- The arm is the build, the branch out of the loop, and the dead
branch. -/
theorem shortValueError_shape :
    shortValueError = shortValueBuild ++ [.br_if 4, .br 1] := by rfl

set_option maxHeartbeats 2000000 in
/-- The short-input arm of the value read leaves a decode error in the
frame at `frame + 16` and the answer 1 on the stack.  Word 0 of that error
is never `okTag`, and the 16 frame bytes below the slot stay with the
caller. -/
theorem twp_short_value_error [WasmSmallStepGS hlc Universal.State]
    (out hdr frame : UInt32) (heapId : GName)
    (scratch below dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l3 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hscratchLength : scratch.length = 48)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame func49Depth below ∗
      Slices.ByteSlice 0 (frame + 16) scratch ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
          ∀ word3 : UInt32, ∀ scratchAfter : List UInt8,
          ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame func49Depth below' -∗
          Slices.ByteSlice 0 (frame + 16)
            (WordCodec.u32le.serialize [word0, word1, word2, word3] ++
              scratchAfter) -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜word0 ≠ okTag ∧ scratchAfter.length = 32⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 hdr],
                  [.i32 frame, l3, .i32 (frame + 52), l5, l6, l7, l8, l9,
                    l10, .i32 word0, .i32 0], .i32 1 :: stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, .i32 (frame + 52), l5, l6, l7, l8, l9, l10,
                l11, l12], stack⟩,
            shortValueBuild ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hscratch, Hdata, Hbump, Hstreams, Hcont⟩
  -- the arithmetic, named before the context grows
  have hokTag : okTag = (2147483649 : UInt32) := rfl
  have h27 : (27 : UInt32).toNat = 27 := rfl
  have hdataLen : dataBytes.length = 920 := by rw [hdataLength]; rfl
  have hE160 : errorNewDepth ≤ frame.toNat := by
    have : func49Depth = 176 := rfl
    have : errorNewDepth = 160 := rfl
    omega
  obtain ⟨⟨hq52a, hq32, hq52b, hq40, hq48, hq16⟩,
    hbf16_16, hbf16, hbf32, hbf40, hbf48_16, hbf48, hbf52, hbf60⟩ :=
    pair_bounds frame hframeNowrap
  obtain ⟨hf16, hf16a, hf16b, hf16c⟩ := offset_facts frame 16 16 rfl hq16
  obtain ⟨hf40, hf40a, hf40b, hf40c⟩ := offset_facts frame 40 40 rfl hq40
  obtain ⟨hf48, hf48a, hf48b, hf48c⟩ := offset_facts frame 48 48 rfl hq48
  obtain ⟨hs8, hs8a, hs8b, hs8c⟩ :=
    offset_facts (frame + 52) 8 8 rfl hq52b
  have hfa32 := offset_facts64 frame 32 32 rfl hq32
  have hfa52 := offset_facts64 (frame + 52) 0 0 rfl hq52a
  -- the addresses of the pieces
  have ha20 : frame + (16 : UInt32) + UInt32.ofNat 4 = frame + 20 :=
    frame_offset frame 16 4 20 rfl
  have ha32 : frame + (16 : UInt32) + UInt32.ofNat 16 = frame + 32 :=
    frame_offset frame 16 16 32 rfl
  have ha40 : frame + (32 : UInt32) + UInt32.ofNat 8 = frame + 40 :=
    frame_offset frame 32 8 40 rfl
  have ha44 : frame + (40 : UInt32) + UInt32.ofNat 4 = frame + 44 :=
    frame_offset frame 40 4 44 rfl
  have ha48 : frame + (44 : UInt32) + UInt32.ofNat 4 = frame + 48 :=
    frame_offset frame 44 4 48 rfl
  have ha52 : frame + (48 : UInt32) + UInt32.ofNat 4 = frame + 52 :=
    frame_offset frame 48 4 52 rfl
  have ha60 : frame + (52 : UInt32) + UInt32.ofNat 8 = frame + 60 :=
    frame_offset frame 52 8 60 rfl
  have hlit60 : frame + (52 : UInt32) + (8 : UInt32) = frame + 60 := by
    rw [UInt32.add_assoc, show (52 : UInt32) + 8 = 60 from by decide]
  have hzero52 : frame + (52 : UInt32) + 0 = frame + 52 := UInt32.add_zero _
  have hseg504 : entryStackTop + UInt32.ofNat 504 = 1049080 := by decide
  have hseg531 : (1049080 : UInt32) + UInt32.ofNat 27 = 1049107 := by decide
  -- the two regions, as named pieces
  obtain ⟨b, c1, c2, c3, d, hscratchShape, hb, hc1, hc2, hc3, hd⟩ :=
    scratch_pieces scratch hscratchLength
  obtain ⟨dpre, dmsg, dpost, hdataShape, hdpre, hdmsg, hdpost⟩ :=
    data_pieces dataBytes hdataLen
  have hc2one : c2.length = 4 * 1 := by rw [hc2]
  -- the frame bytes split into their five pieces
  isimp only [hscratchShape] at Hscratch
  ihave ⟨HfB, Hr2⟩ :=
    (Slices.ByteSlice_append 0 (frame + 16) b (c1 ++ (c2 ++ (c3 ++ d)))).mp $$
      Hscratch
  isimp only [hb, ha32] at Hr2
  ihave ⟨HfC1, Hr3⟩ :=
    (Slices.ByteSlice_append 0 (frame + 32) c1 (c2 ++ (c3 ++ d))).mp $$ Hr2
  isimp only [hc1, ha40] at Hr3
  ihave ⟨HfC2, Hr4⟩ :=
    (Slices.ByteSlice_append 0 (frame + 40) c2 (c3 ++ d)).mp $$ Hr3
  isimp only [hc2, ha44] at Hr4
  ihave ⟨HfC3, HfD⟩ :=
    (Slices.ByteSlice_append 0 (frame + 44) c3 d).mp $$ Hr4
  isimp only [hc3, ha48] at HfD
  -- the data segment lends its 27-byte message
  isimp only [hdataShape] at Hdata
  ihave ⟨Hdpre, Hdr1⟩ :=
    (Slices.ByteSlice_append 0 entryStackTop dpre (dmsg ++ dpost)).mp $$ Hdata
  isimp only [hdpre, hseg504] at Hdr1
  ihave ⟨Hdmsg, Hdpost⟩ :=
    (Slices.ByteSlice_append 0 1049080 dmsg dpost).mp $$ Hdr1
  isimp only [hdmsg, hseg531] at Hdpost
  -- the stack region that absolute `func 55` takes
  ihave ⟨Hbelow, %hbelowLength⟩ :=
    StackBelow_length frame func49Depth below $$ Hbelow
  have htakeLen :
      (below.take (func49Depth - errorNewDepth)).length =
        func49Depth - errorNewDepth := by
    rw [List.length_take, hbelowLength]
    have : func49Depth = 176 := rfl
    have : errorNewDepth = 160 := rfl
    omega
  ihave ⟨Hdeep, Herrzone⟩ :=
    frame_split frame func49Depth errorNewDepth below (by decide) $$ Hbelow
  -- absolute `func 55` builds the `io::Error` at `frame + 48`
  simp only [shortValueBuild, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (48 : UInt32) + frame = frame + 48 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_const twp_const twp_const]
  have Hnew : Func52Spec (hlc := hlc) :=
    Project.RustHashMap.Func52Proof.func52_correct
  unfold Func52Spec CallContract callExpr at Hnew
  simp only [List.cons_append, List.nil_append] at Hnew
  iapply Hnew (sp := frame) (out := frame + 48) (kind := 17)
    (msgPtr := 1049080) (msgLen := 27) (heapId := heapId) (outBefore := d)
    (below := below.drop (func49Depth - errorNewDepth)) (msgBytes := dmsg)
    (storedCursor := storedCursor) (frontier := frontier) (history := history)
    (input := input) (output := output) (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 hdr],
        locals := [.i32 frame, l3, .i32 (frame + 52), l5, l6, l7, l8, l9,
          l10, l11, l12], values := [] })
    (stack := stack)
  isplitl_exacts [Hruntime Hsp Herrzone HfD Hdmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨hd, hE160, hbf48_16, by decide, by decide, by rw [h27]; exact hdmsg⟩
  isplit
  · iintro %w0 %w1 %w2 %w3 %belowA %storedCursorA %frontierA %historyA
    iintro Hruntime Hsp Herrzone Herr Hdmsg Hbump Hstreams %hw0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    have hw0' : w0 ≠ (2147483649 : UInt32) := by rw [← hokTag]; exact hw0
    -- the error record splits into its three blocks
    isimp only [ser4_split121] at Herr
    ihave ⟨Herr0, Herr123⟩ :=
      (Slices.ByteSlice_append 0 (frame + 48) (WordCodec.u32le.serialize [w0])
        (WordCodec.u32le.serialize [w1, w2] ++
          WordCodec.u32le.serialize [w3])).mp $$ Herr
    isimp only [ser_one_length, ha52] at Herr123
    ihave ⟨Herr12, Herr3⟩ :=
      (Slices.ByteSlice_append 0 (frame + 52)
        (WordCodec.u32le.serialize [w1, w2])
        (WordCodec.u32le.serialize [w3])).mp $$ Herr123
    isimp only [ser_two_length, ha60] at Herr3
    -- the first block move: the middle two words go to `frame + 32`
    ihave Herr12w :=
      ByteSlice_as_word (frame + 52) (frame + 52 + 0)
        (WordCodec.u32le.serialize [w1, w2]) hzero52
        (ser_two_length w1 w2) $$ Herr12
    ihave Hc1w := ByteSlice_as_word (frame + 32) (frame + 32) c1 rfl hc1 $$ HfC1
    wasm_twp_block_move
      (frame + 52, 0, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [w1, w2]), hfa52)
      (frame, 32, Wasm.RustStd.HashMap.Table.groupWord c1, hfa32)
      with Herr12w Hc1w
    -- the last word goes to `frame + 40`
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave Herr3arr := cells_of_ByteSlice (frame + 60) [w3] $$ Herr3
    ihave ⟨Hw3, Hclose3⟩ :=
      cell_load (frame + 60) 0 [w3] 0 w3 (one_pos _) rfl (by decide) $$
        Herr3arr
    isimp only [UInt32.add_zero] at Hw3 Hclose3
    ihave Hw3 := word_move (frame + 60) (frame + 52 + 8) w3 hlit60 $$ Hw3
    wasm_twp_rebind twp_load32 (address := frame + 52) (offset := 8) w3
      hs8 hs8a hs8b hs8c with Hw3
    ihave Hw3 := word_move (frame + 52 + 8) (frame + 60) w3 hlit60.symm $$ Hw3
    ihave ⟨%hc2Words, Hc2arr⟩ :=
      ByteSlice_as_cells (frame + 40) c2 1 hc2one $$ HfC2
    obtain ⟨x2, hx2⟩ := one_word (Slices.decodeWords c2) hc2Words
    isimp only [hx2] at Hc2arr
    ihave ⟨Hx2, Hclose2⟩ :=
      cell_focus (frame + 40) 0 [x2] 0 x2 w3 (one_pos _) rfl (by decide) $$
        Hc2arr
    isimp only [UInt32.add_zero] at Hx2 Hclose2
    wasm_twp_rebind twp_store32 (address := frame) (offset := 40) x2
      hf40 hf40a hf40b hf40c with Hx2
    ihave Hc2arr := Hclose2 $$ Hx2
    isimp only [List.set] at Hc2arr
    ihave Herr3arr := Hclose3 $$ Hw3
    -- the value of the step is zero
    wasm_twp_pures [twp_const]
    wasm_twp_localSet
    -- the dead `okTag` test of the `io::Error`
    wasm_twp_pures [twp_localGet]
    ihave Herr0arr := cells_of_ByteSlice (frame + 48) [w0] $$ Herr0
    ihave ⟨Hw0, Hclose0⟩ :=
      cell_load (frame + 48) 0 [w0] 0 w0 (one_pos _) rfl (by decide) $$
        Herr0arr
    isimp only [UInt32.add_zero] at Hw0 Hclose0
    wasm_twp_rebind twp_load32 (address := frame) (offset := 48) w0
      hf48 hf48a hf48b hf48c with Hw0
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    iapply twp_eq (result := 0) (by rw [if_neg hw0'])
    iapply twp_brIfZero
    ihave Herr0arr := Hclose0 $$ Hw0
    -- the second block move: the middle two words come back
    wasm_twp_block_move
      (frame, 32, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [w1, w2]), hfa32)
      (frame + 52, 0, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [w1, w2]), hfa52)
      with Hc1w Herr12w
    -- the last word comes back
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Hx2, Hclose2⟩ :=
      cell_load (frame + 40) 0 [w3] 0 w3 (one_pos _) rfl (by decide) $$ Hc2arr
    isimp only [UInt32.add_zero] at Hx2 Hclose2
    wasm_twp_rebind twp_load32 (address := frame) (offset := 40) w3
      hf40 hf40a hf40b hf40c with Hx2
    ihave Hc2arr := Hclose2 $$ Hx2
    ihave ⟨Hw3, Hclose3⟩ :=
      cell_focus (frame + 60) 0 [w3] 0 w3 w3 (one_pos _) rfl (by decide) $$
        Herr3arr
    isimp only [UInt32.add_zero] at Hw3 Hclose3
    ihave Hw3 := word_move (frame + 60) (frame + 52 + 8) w3 hlit60 $$ Hw3
    wasm_twp_rebind twp_store32 (address := frame + 52) (offset := 8) w3
      hs8 hs8a hs8b hs8c with Hw3
    ihave Hw3 := word_move (frame + 52 + 8) (frame + 60) w3 hlit60.symm $$ Hw3
    ihave Herr3arr := Hclose3 $$ Hw3
    isimp only [List.set] at Herr3arr
    ihave Herr3 :=
      ByteSlice_of_cells (frame + 60) [w3] (cells_nowrap_one _ w3 hbf60) $$
        Herr3arr
    -- word 0 goes back where it was
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Hw0, Hclose0⟩ :=
      cell_focus (frame + 48) 0 [w0] 0 w0 w0 (one_pos _) rfl (by decide) $$
        Herr0arr
    isimp only [UInt32.add_zero] at Hw0 Hclose0
    wasm_twp_rebind twp_store32 (address := frame) (offset := 48) w0
      hf48 hf48a hf48b hf48c with Hw0
    ihave Herr0arr := Hclose0 $$ Hw0
    isimp only [List.set] at Herr0arr
    ihave Herr0 :=
      ByteSlice_of_cells (frame + 48) [w0] (cells_nowrap_one _ w0 hbf48) $$
        Herr0arr
    -- the error record, whole again
    ihave Herr12 :=
      ByteSlice_of_word (frame + 52) (frame + 52 + 0)
        (WordCodec.u32le.serialize [w1, w2]) hzero52 (ser_two_length w1 w2)
        hbf52 $$ Herr12w
    ihave Herr123 :=
      ByteSlice_glue (frame + 52) (WordCodec.u32le.serialize [w1, w2])
        (WordCodec.u32le.serialize [w3]) 8 (ser_two_length w1 w2) $$
        [Herr12 Herr3]
    · isplitl_exact Herr12
      · irw_exact [ha60] with Herr3
    ihave Herr :=
      ByteSlice_glue (frame + 48) (WordCodec.u32le.serialize [w0])
        (WordCodec.u32le.serialize [w1, w2] ++
          WordCodec.u32le.serialize [w3]) 4 (ser_one_length w0) $$
        [Herr0 Herr123]
    · isplitl_exact Herr0
      · irw_exact [ha52] with Herr123
    isimp only [← ser4_split121] at Herr
    -- the data segment, whole again
    ihave Hdr1 :=
      ByteSlice_glue 1049080 dmsg dpost 27 hdmsg $$ [Hdmsg Hdpost]
    · isplitl_exact Hdmsg
      · irw_exact [hseg531] with Hdpost
    ihave Hdata :=
      ByteSlice_glue entryStackTop dpre (dmsg ++ dpost) 504 hdpre $$
        [Hdpre Hdr1]
    · isplitl_exact Hdpre
      · irw_exact [hseg504] with Hdr1
    isimp only [← hdataShape] at Hdata
    -- the stack region, whole again
    ihave Hbelow :=
      frame_join frame func49Depth errorNewDepth
        (below.take (func49Depth - errorNewDepth)) belowA htakeLen
        (by decide) $$ [Hdeep Herrzone]
    · isplitl_exact Hdeep
      · iexact Herrzone
    -- absolute `func 52` turns it into the decode error at `frame + 16`
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + frame = frame + 16 from UInt32.add_comm _ _]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (48 : UInt32) + frame = frame + 48 from UInt32.add_comm _ _]
    have Hconv : Func49Spec (hlc := hlc) :=
      Project.RustHashMap.Func49Proof.func49_correct
    unfold Func49Spec CallContract callExpr at Hconv
    simp only [List.cons_append, List.nil_append] at Hconv
    iapply Hconv (sp := frame) (out := frame + 16) (errPtr := frame + 48)
      (errWord0 := w0) (errWord1 := w1) (errWord2 := w2) (errWord3 := w3)
      (heapId := heapId) (outBefore := b)
      (below := below.take (func49Depth - errorNewDepth) ++ belowA)
      (dataBytes := dataBytes) (storedCursor := storedCursorA)
      (frontier := frontierA) (history := historyA) (input := input)
      (output := output) (raised := raised)
      (callerLocals :=
        { params := [.i32 out, .i32 hdr],
          locals := [.i32 frame, l3, .i32 (frame + 52), l5, l6, l7, l8, l9,
            l10, .i32 w0, .i32 0], values := [] })
      (stack := stack)
    isplitl_exacts [Hruntime Hsp Hbelow HfB Herr Hdata Hbump Hstreams]
    isplitl_pureexact
      ⟨hb, hframeLow, hbf16_16, hbf48_16, hw0, hdataLength⟩
    isplit
    · iintro %v0 %v1 %v2 %v3 %errAfter %belowB %storedCursorB %frontierB
        %historyB
      iintro Hruntime Hsp Hbelow Hslot Herr Hdata Hbump Hstreams %hvFacts
      obtain ⟨hv0, hafterLength⟩ := hvFacts
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      have hv0' : v0 ≠ (2147483649 : UInt32) := by rw [← hokTag]; exact hv0
      -- the live test of the decode error
      isimp only [ser4_split13] at Hslot
      ihave ⟨Hv0s, Hv123⟩ :=
        (Slices.ByteSlice_append 0 (frame + 16)
          (WordCodec.u32le.serialize [v0])
          (WordCodec.u32le.serialize [v1, v2, v3])).mp $$ Hslot
      isimp only [ser_one_length, ha20] at Hv123
      wasm_twp_pures [twp_localGet]
      ihave Hv0arr := cells_of_ByteSlice (frame + 16) [v0] $$ Hv0s
      ihave ⟨Hv0, Hclosev0⟩ :=
        cell_load (frame + 16) 0 [v0] 0 v0 (one_pos _) rfl (by decide) $$
          Hv0arr
      isimp only [UInt32.add_zero] at Hv0 Hclosev0
      wasm_twp_rebind twp_load32 (address := frame) (offset := 16) v0
        hf16 hf16a hf16b hf16c with Hv0
      wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_const]
      iapply twp_ne (result := 1) (by rw [if_pos hv0'])
      ihave Hv0arr := Hclosev0 $$ Hv0
      ihave Hv0s :=
        ByteSlice_of_cells (frame + 16) [v0] (cells_nowrap_one _ v0 hbf16) $$
          Hv0arr
      ihave Hslot :=
        ByteSlice_glue (frame + 16) (WordCodec.u32le.serialize [v0])
          (WordCodec.u32le.serialize [v1, v2, v3]) 4 (ser_one_length v0) $$
          [Hv0s Hv123]
      · isplitl_exact Hv0s
        · irw_exact [ha20] with Hv123
      isimp only [← ser4_split13] at Hslot
      -- the frame bytes, whole again
      ihave HfC1 :=
        ByteSlice_of_word (frame + 32) (frame + 32)
          (WordCodec.u32le.serialize [w1, w2]) rfl (ser_two_length w1 w2)
          hbf32 $$ Hc1w
      ihave HfC2 :=
        ByteSlice_of_cells (frame + 40) [w3] (cells_nowrap_one _ w3 hbf40) $$
          Hc2arr
      ihave HfCD :=
        ByteSlice_glue (frame + 44) c3 errAfter 4 hc3 $$ [HfC3 Herr]
      · isplitl_exact HfC3
        · irw_exact [ha48] with Herr
      ihave HfC2D :=
        ByteSlice_glue (frame + 40) (WordCodec.u32le.serialize [w3])
          (c3 ++ errAfter) 4 (ser_one_length w3) $$ [HfC2 HfCD]
      · isplitl_exact HfC2
        · irw_exact [ha44] with HfCD
      ihave HfC1D :=
        ByteSlice_glue (frame + 32) (WordCodec.u32le.serialize [w1, w2])
          (WordCodec.u32le.serialize [w3] ++ (c3 ++ errAfter)) 8
          (ser_two_length w1 w2) $$ [HfC1 HfC2D]
      · isplitl_exact HfC1
        · irw_exact [ha40] with HfC2D
      ihave Hscratch :=
        ByteSlice_glue (frame + 16)
          (WordCodec.u32le.serialize [v0, v1, v2, v3])
          (WordCodec.u32le.serialize [w1, w2] ++
            (WordCodec.u32le.serialize [w3] ++ (c3 ++ errAfter))) 16
          (ser_four_length v0 v1 v2 v3) $$ [Hslot HfC1D]
      · isplitl_exact Hslot
        · irw_exact [ha32] with HfC1D
      -- the continuation
      obtain ⟨scratchAfter, hscratchAfter⟩ :
          ∃ t : List UInt8,
            t = WordCodec.u32le.serialize [w1, w2] ++
              (WordCodec.u32le.serialize [w3] ++ (c3 ++ errAfter)) :=
        ⟨_, rfl⟩
      isimp only [← hscratchAfter] at Hscratch
      have hscratchAfterLength : scratchAfter.length = 32 := by
        rw [hscratchAfter]
        simp only [List.length_append, ser_one_length, ser_two_length,
          hc3, hafterLength, Nat.reduceAdd]
      ihave Hnormal := BI.and_elim_l $$ Hcont
      ihave Hnormal := Hnormal $$ %v0 %v1 %v2 %v3 %scratchAfter %belowB
        %storedCursorB %frontierB %historyB
      iapply Hnormal $$ Hruntime Hsp Hbelow Hscratch Hdata Hbump Hstreams
        %⟨hv0, hscratchAfterLength⟩
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Decoder
