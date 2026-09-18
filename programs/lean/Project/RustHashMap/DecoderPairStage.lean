import Project.RustHashMap.DecoderShortValue

/-!
# The borsh decoder: the read of one pair

`Project.RustHashMap.Decoder.pairStage` is the first half of one loop step,
WAT lines 613 to 761.  It reads eight input bytes, and it holds five nested
blocks:

| Block | Body | Continuation |
| --- | --- | --- |
| `pairStage` | `valueStage` | the grow block |
| `valueStage` | `keyOutcome` | `shortValueError` |
| `keyOutcome` | `keyStage` | `zeroKey` |
| `keyStage` | `shortPairError` | `keyRead` |
| the guard | `shortPairError` | `keyRead` |

This file joins the four leaf lemmas of those blocks into one lemma for the
whole stage.  The stage has three paths, and the number of unread input
bytes picks one of them:

1. Three bytes or fewer take `shortPairError`, and `br 7` leaves the loop
   through the error return.
2. Four to seven bytes take `keyRead` and then `shortValueError`, and
   `br_if 4` leaves the loop the same way.
3. Eight bytes or more take `keyRead` and then `pairRead`, and the stage
   falls out of the `pairStage` block with the key in local 10 and the
   value in local 12.

The lemma hides all five blocks.  It gives the caller one normal arm, one
error arm, and the out-of-memory arm.  The two error paths differ in four
locals and in the two words of the slice header, so the error arm
quantifies over them.

`zeroKey` is the continuation of the `keyStage` block.  Only the two dead
`okTag` tests of `shortPairError` reach it, so this file never runs it.
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

/-! ## The frame of the allocation stage -/

/-- The block frame that both error paths leave through.  It is the frame
of `Project.RustHashMap.Decoder.allocStage`, and its continuation is the
error return. -/
def allocFrame (errorBody errorCont : Program) (errorBelow : List Value) :
    ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := errorBody,
    continuation := errorCont, belowStack := errorBelow }

/-! ## Words of the input -/

/-- A byte offset four bytes above another. -/
theorem addr_shift4 (ptr : UInt32) (pos : Nat) :
    ptr + UInt32.ofNat (pos + 4) = ptr + UInt32.ofNat pos + 4 := by
  rw [UInt32.ofNat_add, ← UInt32.add_assoc]
  rfl

/-- A byte offset eight bytes above another. -/
theorem addr_shift8 (ptr : UInt32) (pos : Nat) :
    ptr + UInt32.ofNat (pos + 8) = ptr + UInt32.ofNat pos + 8 := by
  rw [UInt32.ofNat_add, ← UInt32.add_assoc]
  rfl

open Wasm.RustStd.HashMap.Table in
/-- One word of the input, at a byte offset. -/
theorem input_wordFocus [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (pos : Nat)
    (hfit : pos + 4 ≤ bytes.length)
    (hnowrap : ptr.toNat + bytes.length < UInt32.size) :
    Slices.ByteSlice 0 ptr bytes ⊣⊢
      iprop(Slices.ByteSlice 0 ptr (bytes.take pos) ∗
        pointsTo_u32 0 (ptr + UInt32.ofNat pos)
          (WordCodec.decodeU32 ((bytes.drop pos).take 4)) ∗
        Slices.ByteSlice 0 (ptr + UInt32.ofNat pos + 4)
          (bytes.drop (pos + 4))) := by
  rw [← addr_shift4 ptr pos]
  refine (ByteSlice_window 0 ptr bytes pos 4 hfit).trans ?_
  refine BI.sep_congr .rfl (BI.sep_congr ?_ .rfl)
  refine Slices.ByteSlice_four_as_word 0 (ptr + UInt32.ofNat pos) _ ?_ ?_
  · rw [List.length_take, List.length_drop]; omega
  · have haddr := Slices.byteOffset_toNat ptr pos (by omega)
    omega

/-- Two words of the input, at a byte offset. -/
theorem input_pairFocus [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (pos : Nat)
    (hfit : pos + 8 ≤ bytes.length)
    (hnowrap : ptr.toNat + bytes.length < UInt32.size) :
    Slices.ByteSlice 0 ptr bytes ⊣⊢
      iprop(Slices.ByteSlice 0 ptr (bytes.take pos) ∗
        pointsTo_u32 0 (ptr + UInt32.ofNat pos)
          (WordCodec.decodeU32 ((bytes.drop pos).take 4)) ∗
        pointsTo_u32 0 (ptr + UInt32.ofNat pos + 4)
          (WordCodec.decodeU32 ((bytes.drop (pos + 4)).take 4)) ∗
        Slices.ByteSlice 0 (ptr + UInt32.ofNat pos + 8)
          (bytes.drop (pos + 8))) := by
  have hsuffix : bytes.drop (pos + 4) =
      (bytes.drop (pos + 4)).take 4 ++ bytes.drop (pos + 8) := by
    conv_lhs => rw [← List.take_append_drop 4 (bytes.drop (pos + 4))]
    rw [List.drop_drop, show pos + 4 + 4 = pos + 8 from by omega]
  have hlen2 : ((bytes.drop (pos + 4)).take 4).length = 4 := by
    rw [List.length_take, List.length_drop]; omega
  have hstep : ptr + UInt32.ofNat pos + 4 + UInt32.ofNat 4
      = ptr + UInt32.ofNat pos + 8 := by
    rw [UInt32.add_assoc]
    rfl
  have haddr4 := Slices.byteOffset_toNat ptr (pos + 4) (by omega)
  rw [addr_shift4 ptr pos] at haddr4
  refine (input_wordFocus ptr bytes pos (by omega) hnowrap).trans ?_
  refine BI.sep_congr .rfl (BI.sep_congr .rfl ?_)
  conv_lhs => rw [hsuffix]
  refine (Slices.ByteSlice_append 0 (ptr + UInt32.ofNat pos + 4)
    ((bytes.drop (pos + 4)).take 4) (bytes.drop (pos + 8))).trans ?_
  rw [hlen2, hstep]
  refine BI.sep_congr ?_ .rfl
  refine Slices.ByteSlice_four_as_word 0 _ _ hlen2 ?_
  omega

/-! ## The stage -/

set_option maxHeartbeats 2000000 in
/-- One read of a pair.  Eight bytes or more give the key and the value,
and fewer leave the loop with a decode error in the frame at
`frame + 16`. -/
theorem twp_pair_stage [WasmSmallStepGS hlc Universal.State]
    (out hdr frame ptr cursor remaining : UInt32) (pos : Nat)
    (heapId : GName) (bytes scratch below dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l3 l7 l8 l9 l10 l11 l12 : Value)
    (loopFrame decodeFrame : ControlFrame)
    (errorBody errorCont : Program) (errorBelow : List Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hcursor : cursor = ptr + UInt32.ofNat pos)
    (hpos : pos ≤ bytes.length)
    (hremaining : remaining.toNat = bytes.length - pos)
    (hptrNowrap : ptr.toNat + bytes.length < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
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
      pointsTo_u32 0 hdr cursor ∗
      pointsTo_u32 0 (hdr + 4) remaining ∗
      Slices.ByteSlice 0 ptr bytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ key : UInt32, ∀ value : UInt32,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame func49Depth below -∗
          Slices.ByteSlice 0 (frame + 16) scratch -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          pointsTo_u32 0 hdr (cursor + 8) -∗
          pointsTo_u32 0 (hdr + 4) (remaining - 8) -∗
          Slices.ByteSlice 0 ptr bytes -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output raised -∗
          ⌜pos + 8 ≤ bytes.length ∧
            key = WordCodec.decodeU32 ((bytes.drop pos).take 4) ∧
            value = WordCodec.decodeU32 ((bytes.drop (pos + 4)).take 4)⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 hdr],
                  [.i32 frame, l3, .i32 (frame + 52), .i32 (remaining - 8),
                    .i32 (cursor + 8), l7, l8, l9, .i32 key,
                    .i32 (cursor + 8), .i32 value], stack⟩,
                code, arity, remainder,
                loopFrame :: decodeFrame ::
                  allocFrame errorBody errorCont errorBelow :: controls,
                calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
            ∀ word3 : UInt32, ∀ hdrPtr : UInt32, ∀ hdrLen : UInt32,
            ∀ scratchAfter : List UInt8, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory, ∀ l5' : Value, ∀ l6' : Value,
            ∀ l10' : Value, ∀ l12' : Value,
            RuntimeContext -∗
            StackPointer frame -∗
            StackBelow frame func49Depth below' -∗
            Slices.ByteSlice 0 (frame + 16)
              (WordCodec.u32le.serialize [word0, word1, word2, word3] ++
                scratchAfter) -∗
            Slices.ByteSlice 0 entryStackTop dataBytes -∗
            pointsTo_u32 0 hdr hdrPtr -∗
            pointsTo_u32 0 (hdr + 4) hdrLen -∗
            Slices.ByteSlice 0 ptr bytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜bytes.length < pos + 8 ∧ word0 ≠ okTag ∧
              scratchAfter.length = 32⌝ -∗
            WP (.running
                ⟨⟨[.i32 out, .i32 hdr],
                    [.i32 frame, l3, .i32 (frame + 52), l5', l6', l7, l8, l9,
                      l10', .i32 word0, l12'], errorBelow⟩,
                  errorCont, arity, remainder, controls, calls⟩
                : Expr Universal.State) @ s; E [{ Φ }]) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, .i32 (frame + 52), .i32 remaining,
                .i32 cursor, l7, l8, l9, l10, l11, l12], stack⟩,
            .block 0 0 pairStage :: code, arity, remainder,
            loopFrame :: decodeFrame ::
              allocFrame errorBody errorCont errorBelow :: controls,
            calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  subst hcursor
  iintro ⟨Hruntime, Hsp, Hbelow, Hscratch, Hdata, Hhdr, Hlen, Hinput, Hbump,
    Hstreams, Hcont⟩
  simp only [pairStage, valueStage, keyOutcome, keyStage,
    shortPairError_shape]
  wasm_twp_pures [twp_block twp_block twp_block twp_block twp_block]
    using [List.drop_zero]
  have h4val : (4 : UInt32).toNat = 4 := by decide
  have hcursorNat : (ptr + UInt32.ofNat pos).toNat = ptr.toNat + pos :=
    Slices.byteOffset_toNat ptr pos (by omega)
  by_cases hshort : remaining > (3 : UInt32)
  · -- four bytes or more: the key read
    have hgt : 3 < remaining.toNat := by
      have h3 : (3 : UInt32).toNat = 3 := by decide
      have hlt := UInt32.lt_iff_toNat_lt.mp hshort
      omega
    have hfour : pos + 4 ≤ bytes.length := by omega
    have hle4 : (4 : UInt32) ≤ remaining :=
      UInt32.le_iff_toNat_le.mpr (by rw [h4val]; omega)
    have hsub4 : (remaining - 4).toNat = remaining.toNat - 4 :=
      UInt32.toNat_sub_of_le remaining 4 hle4
    simp only [shortPairBuild, List.cons_append, List.nil_append]
    wasm_twp_pures [twp_localGet twp_const]
    iapply twp_gtU (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    rw [keyRead_shape]
    by_cases hlong : 8 ≤ remaining.toNat
    · -- eight bytes or more: the key and the value
      have height : pos + 8 ≤ bytes.length := by omega
      have hge4 : (remaining - 4) ≥ (4 : UInt32) :=
        UInt32.le_iff_toNat_le.mpr (by rw [h4val, hsub4]; omega)
      ihave ⟨Hpre, Hkey, Hvalue, Hpost⟩ :=
        (input_pairFocus ptr bytes pos height hptrNowrap).mp $$ Hinput
      iapply twp_key_stores (out := out) (hdr := hdr) (frame := frame)
        (cursor := ptr + UInt32.ofNat pos) (remaining := remaining)
        (key := WordCodec.decodeU32 ((bytes.drop pos).take 4))
        (oldPtr := ptr + UInt32.ofNat pos) (oldLen := remaining)
        (l3 := l3) (l4 := .i32 (frame + 52)) (l7 := l7) (l8 := l8)
        (l9 := l9) (l10 := l10) (l11 := l11) (l12 := l12)
        hhdrNowrap (by omega)
      isplitl_exacts [Hhdr Hlen Hkey]
      iintro Hhdr Hlen Hkey
      wasm_twp_pures [twp_localGet twp_const]
      iapply twp_geU (result := 1) (by rw [if_pos hge4])
      iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
      simp only [List.take_zero, List.nil_append]
      rw [← List.append_nil pairRead]
      iapply twp_pair_read (out := out) (hdr := hdr) (frame := frame)
        (cursor := ptr + UInt32.ofNat pos) (remaining := remaining)
        (value := WordCodec.decodeU32 ((bytes.drop (pos + 4)).take 4))
        (oldPtr := ptr + UInt32.ofNat pos + 4) (oldLen := remaining - 4)
        (l3 := l3) (l4 := .i32 (frame + 52)) (l7 := l7) (l8 := l8)
        (l9 := l9)
        (l10 := .i32 (WordCodec.decodeU32 ((bytes.drop pos).take 4)))
        (l11 := .i32 (ptr + UInt32.ofNat pos + 4))
        (l12 := .i32 (remaining - 4))
        hhdrNowrap (by omega)
      isplitl_exacts [Hhdr Hlen Hvalue]
      iintro Hhdr Hlen Hvalue
      wasm_twp_pures [twp_exitControl]
        using [List.take_zero, List.drop_zero, List.nil_append]
      ihave Hinput :=
        (input_pairFocus ptr bytes pos height hptrNowrap).mpr $$
          [Hpre Hkey Hvalue Hpost]
      · isplitl_exacts [Hpre Hkey Hvalue]
        iexact Hpost
      ihave Hnormal := BI.and_elim_l $$ Hcont
      ihave Hnormal := Hnormal
        $$ %(WordCodec.decodeU32 ((bytes.drop pos).take 4))
          %(WordCodec.decodeU32 ((bytes.drop (pos + 4)).take 4))
      iapply Hnormal $$ Hruntime Hsp Hbelow Hscratch Hdata Hhdr Hlen Hinput
        Hbump Hstreams %⟨height, rfl, rfl⟩
    · -- four to seven bytes: the short-input arm of the value
      have hlt4 : ¬ ((remaining - 4) ≥ (4 : UInt32)) := by
        intro hcon
        have hcon' := UInt32.le_iff_toNat_le.mp hcon
        rw [h4val, hsub4] at hcon'
        omega
      ihave ⟨Hpre, Hkey, Hpost⟩ :=
        (input_wordFocus ptr bytes pos hfour hptrNowrap).mp $$ Hinput
      iapply twp_key_stores (out := out) (hdr := hdr) (frame := frame)
        (cursor := ptr + UInt32.ofNat pos) (remaining := remaining)
        (key := WordCodec.decodeU32 ((bytes.drop pos).take 4))
        (oldPtr := ptr + UInt32.ofNat pos) (oldLen := remaining)
        (l3 := l3) (l4 := .i32 (frame + 52)) (l7 := l7) (l8 := l8)
        (l9 := l9) (l10 := l10) (l11 := l11) (l12 := l12)
        hhdrNowrap (by omega)
      isplitl_exacts [Hhdr Hlen Hkey]
      iintro Hhdr Hlen Hkey
      ihave Hinput :=
        (input_wordFocus ptr bytes pos hfour hptrNowrap).mpr $$
          [Hpre Hkey Hpost]
      · isplitl_exacts [Hpre Hkey]
        iexact Hpost
      wasm_twp_pures [twp_localGet twp_const]
      iapply twp_geU (result := 0) (by rw [if_neg hlt4])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_localGet]
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      iapply twp_br (by rfl)
      simp only [List.take_zero, List.nil_append]
      rw [shortValueError_shape]
      iapply twp_short_value_error (out := out) (hdr := hdr) (frame := frame)
        (heapId := heapId) (scratch := scratch) (below := below)
        (dataBytes := dataBytes) (storedCursor := storedCursor)
        (frontier := frontier) (history := history) (input := input)
        (output := output) (raised := raised) (l3 := l3)
        (l5 := .i32 (remaining - 4))
        (l6 := .i32 (ptr + UInt32.ofNat pos + 4)) (l7 := l7) (l8 := l8)
        (l9 := l9)
        (l10 := .i32 (WordCodec.decodeU32 ((bytes.drop pos).take 4)))
        (l11 := .i32 (ptr + UInt32.ofNat pos + 4))
        (l12 := .i32 (remaining - 4))
        hscratchLength hdataLength hframeLow hframeNowrap
      isplitl_exacts [Hruntime Hsp Hbelow Hscratch Hdata Hbump Hstreams]
      isplit
      · iintro %word0 %word1 %word2 %word3 %scratchAfter %below'
          %storedCursor' %frontier' %history'
        iintro Hruntime Hsp Hbelow Hscratch Hdata Hbump Hstreams %hfacts
        iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [allocFrame, List.take_zero, List.nil_append]
        ihave Hrest := BI.and_elim_r $$ Hcont
        ihave Herror := BI.and_elim_l $$ Hrest
        ihave Herror := Herror $$ %word0 %word1 %word2 %word3
          %(ptr + UInt32.ofNat pos + 4) %(remaining - 4) %scratchAfter
          %below' %storedCursor' %frontier' %history'
          %(Value.i32 (remaining - 4))
          %(Value.i32 (ptr + UInt32.ofNat pos + 4))
          %(Value.i32 (WordCodec.decodeU32 ((bytes.drop pos).take 4)))
          %(Value.i32 0)
        iapply Herror $$ Hruntime Hsp Hbelow Hscratch Hdata Hhdr Hlen Hinput
          Hbump Hstreams %⟨by omega, hfacts.1, hfacts.2⟩
      · iintro %remaining' Hstreams
        ihave Hrest := BI.and_elim_r $$ Hcont
        ihave Hoom := BI.and_elim_r $$ Hrest
        ihave Hoom := Hoom $$ %remaining'
        iapply Hoom $$ Hstreams
  · -- three bytes or fewer: the short-input arm
    have hshortNat : remaining.toNat ≤ 3 := by
      have h3 : (3 : UInt32).toNat = 3 := by decide
      have hle : ¬ ((3 : UInt32).toNat < remaining.toNat) := fun hlt =>
        hshort (UInt32.lt_iff_toNat_lt.mpr hlt)
      omega
    iapply twp_short_pair_error (out := out) (hdr := hdr) (frame := frame)
      (remaining := remaining) (heapId := heapId) (scratch := scratch)
      (below := below) (dataBytes := dataBytes)
      (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised) (l3 := l3)
      (l6 := .i32 (ptr + UInt32.ofNat pos)) (l7 := l7) (l8 := l8)
      (l9 := l9) (l10 := l10) (l11 := l11) (l12 := l12)
      hshort hscratchLength hdataLength hframeLow hframeNowrap
    isplitl_exacts [Hruntime Hsp Hbelow Hscratch Hdata Hbump Hstreams]
    isplit
    · iintro %errWord0 %word0 %word1 %word2 %word3 %scratchAfter %below'
        %storedCursor' %frontier' %history'
      iintro Hruntime Hsp Hbelow Hscratch Hdata Hbump Hstreams %hfacts
      iapply twp_br (by rfl)
      simp only [allocFrame, List.take_zero, List.nil_append]
      ihave Hrest := BI.and_elim_r $$ Hcont
      ihave Herror := BI.and_elim_l $$ Hrest
      ihave Herror := Herror $$ %word0 %word1 %word2 %word3
        %(ptr + UInt32.ofNat pos) %remaining %scratchAfter %below'
        %storedCursor' %frontier' %history' %(Value.i32 remaining)
        %(Value.i32 (ptr + UInt32.ofNat pos)) %(Value.i32 errWord0) %l12
      iapply Herror $$ Hruntime Hsp Hbelow Hscratch Hdata Hhdr Hlen Hinput
        Hbump Hstreams %⟨by omega, hfacts.1, hfacts.2⟩
    · iintro %remaining' Hstreams
      ihave Hrest := BI.and_elim_r $$ Hcont
      ihave Hoom := BI.and_elim_r $$ Hrest
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams

end Project.RustHashMap.Decoder
