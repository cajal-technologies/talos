import Project.RustHashMap.DecoderPrologue
import Project.RustHashMap.Func49Proof

/-!
# The borsh decoder: the short-input arm of the header

The decoder reads the four-byte pair count first.  Fewer than four bytes
left is the "unexpected end of input" error, at WAT lines 481 to 545.
`Project.RustHashMap.Decoder.headerError` is that arm.

This module proves the arm up to its final branch.  The arm does four
steps:

1. It builds an `io::Error` into the frame at `frame + 48` with absolute
   `func 55`, from the 27-byte message at 1049080.
2. It moves the last twelve bytes of the error to `frame + 32` and back.
   The move changes nothing, and the proof of the round trip is the bulk
   of this file.
3. It turns the `io::Error` into the decode error with absolute `func 52`,
   into the frame at `frame + 16`.
4. It writes the four words of the decode error into the output slot.

The two `okTag` tests are dead arms.  Word 0 of a built `io::Error` is the
capacity of a `String`, and both `Func52Spec` and `Func49Spec` promise that
the capacity is not `okTag`.  So both tests take the fall-through.

The lemma leaves the final `.br 3` to the caller, so it holds for any
control stack.

## Why the bounds come from two lemmas

`omega` reads every hypothesis of the goal.  The proof of the arm holds
more than forty address facts at its deepest point, so one `omega` call
there costs about five seconds.  `frame_bounds` and `out_bounds` below
prove every bound that the arm needs, each in a context of one hypothesis.
The arm then names a bound instead of proving it again.
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

/-! ## Word blocks of a four-word record

Each `i32` rule takes one word and each `i64` rule takes two, so a 16-byte
record splits two ways.  The error record splits 1, 2, 1 and the decode
error splits 1, 1, 2. -/

/-- The 1, 2, 1 split of a four-word record. -/
private theorem ser4_split121 (w0 w1 w2 w3 : UInt32) :
    WordCodec.u32le.serialize [w0, w1, w2, w3] =
      WordCodec.u32le.serialize [w0] ++
        (WordCodec.u32le.serialize [w1, w2] ++
          WordCodec.u32le.serialize [w3]) := by
  simp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil, List.append_assoc]

/-- The 1, 1, 2 split of a four-word record. -/
private theorem ser4_split112 (w0 w1 w2 w3 : UInt32) :
    WordCodec.u32le.serialize [w0, w1, w2, w3] =
      WordCodec.u32le.serialize [w0] ++
        (WordCodec.u32le.serialize [w1] ++
          WordCodec.u32le.serialize [w2, w3]) := by
  simp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil]

private theorem ser_one_length (w : UInt32) :
    (WordCodec.u32le.serialize [w]).length = 4 := by
  simp

private theorem ser_two_length (a b : UInt32) :
    (WordCodec.u32le.serialize [a, b]).length = 8 := by
  simp

private theorem ser_four_length (a b c d : UInt32) :
    (WordCodec.u32le.serialize [a, b, c, d]).length = 16 := by
  simp

/-- A one-word list is not empty. -/
private theorem one_pos (w : UInt32) : 0 < ([w] : List UInt32).length := by
  simp

/-- The bound that `ByteSlice_of_cells` asks for over a one-word list. -/
private theorem cells_nowrap_one (base w : UInt32)
    (hbound : base.toNat + 4 < UInt32.size) :
    base.toNat + 4 * ([w] : List UInt32).length < UInt32.size := by
  simpa using hbound

/-! ## The bounds -/

/-- Every address bound of the 64-byte frame.  The first group is what
`offset_facts` and `offset_facts64` ask for, and the second is what
`ByteSlice_of_cells` and `ByteSlice_of_word` ask for. -/
private theorem frame_bounds (base : UInt32)
    (h : base.toNat + 64 < UInt32.size) :
    (base.toNat + 16 + 4 ≤ UInt32.size ∧ base.toNat + 20 + 4 ≤ UInt32.size ∧
        base.toNat + 24 + 8 ≤ UInt32.size ∧
        base.toNat + 32 + 8 ≤ UInt32.size ∧
        base.toNat + 40 + 4 ≤ UInt32.size ∧
        base.toNat + 48 + 4 ≤ UInt32.size ∧
        base.toNat + 52 + 8 ≤ UInt32.size ∧
        base.toNat + 60 + 4 ≤ UInt32.size) ∧
      ((base + 16).toNat + 16 < UInt32.size ∧
        (base + 16).toNat + 4 < UInt32.size ∧
        (base + 20).toNat + 4 < UInt32.size ∧
        (base + 24).toNat + 8 < UInt32.size ∧
        (base + 32).toNat + 8 < UInt32.size ∧
        (base + 40).toNat + 4 < UInt32.size ∧
        (base + 48).toNat + 16 < UInt32.size ∧
        (base + 48).toNat + 4 < UInt32.size ∧
        (base + 52).toNat + 8 < UInt32.size ∧
        (base + 60).toNat + 4 < UInt32.size) := by
  have h16 : (base + (16 : UInt32)).toNat = base.toNat + 16 :=
    Slices.byteOffset_toNat base 16 (by omega)
  have h20 : (base + (20 : UInt32)).toNat = base.toNat + 20 :=
    Slices.byteOffset_toNat base 20 (by omega)
  have h24 : (base + (24 : UInt32)).toNat = base.toNat + 24 :=
    Slices.byteOffset_toNat base 24 (by omega)
  have h32 : (base + (32 : UInt32)).toNat = base.toNat + 32 :=
    Slices.byteOffset_toNat base 32 (by omega)
  have h40 : (base + (40 : UInt32)).toNat = base.toNat + 40 :=
    Slices.byteOffset_toNat base 40 (by omega)
  have h48 : (base + (48 : UInt32)).toNat = base.toNat + 48 :=
    Slices.byteOffset_toNat base 48 (by omega)
  have h52 : (base + (52 : UInt32)).toNat = base.toNat + 52 :=
    Slices.byteOffset_toNat base 52 (by omega)
  have h60 : (base + (60 : UInt32)).toNat = base.toNat + 60 :=
    Slices.byteOffset_toNat base 60 (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Every address bound of the 16-byte output slot. -/
private theorem out_bounds (base : UInt32)
    (h : base.toNat + 16 < UInt32.size) :
    (base.toNat + 0 + 4 ≤ UInt32.size ∧ base.toNat + 4 + 4 ≤ UInt32.size ∧
        base.toNat + 8 + 8 ≤ UInt32.size) ∧
      (base.toNat + 4 < UInt32.size ∧ (base + 4).toNat + 4 < UInt32.size ∧
        (base + 8).toNat + 8 < UInt32.size) := by
  have h4 : (base + (4 : UInt32)).toNat = base.toNat + 4 :=
    Slices.byteOffset_toNat base 4 (by omega)
  have h8 : (base + (8 : UInt32)).toNat = base.toNat + 8 :=
    Slices.byteOffset_toNat base 8 (by omega)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega

/-! ## The pieces of the three byte regions -/

/-- The 64 frame bytes, as the six pieces that the arm uses.  They are the
pad, the output slot of absolute `func 52`, the eight scratch bytes, the
four scratch bytes, the gap, and the `io::Error` slot. -/
private theorem frame_pieces (bytes : List UInt8) (hlength : bytes.length = 64) :
    ∃ a b c1 c2 c3 d : List UInt8,
      bytes = a ++ (b ++ (c1 ++ (c2 ++ (c3 ++ d)))) ∧
      a.length = 16 ∧ b.length = 16 ∧ c1.length = 8 ∧ c2.length = 4 ∧
      c3.length = 4 ∧ d.length = 16 := by
  refine ⟨bytes.take 16, (bytes.drop 16).take 16,
    ((bytes.drop 16).drop 16).take 8,
    (((bytes.drop 16).drop 16).drop 8).take 4,
    ((((bytes.drop 16).drop 16).drop 8).drop 4).take 4,
    ((((bytes.drop 16).drop 16).drop 8).drop 4).drop 4,
    by simp only [List.take_append_drop], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

/-- The 16 bytes of the output slot, as the three pieces that the arm
writes. -/
private theorem out_pieces (bytes : List UInt8) (hlength : bytes.length = 16) :
    ∃ a b c : List UInt8,
      bytes = a ++ (b ++ c) ∧ a.length = 4 ∧ b.length = 4 ∧ c.length = 8 := by
  refine ⟨bytes.take 4, (bytes.drop 4).take 4, (bytes.drop 4).drop 4,
    by simp only [List.take_append_drop], ?_, ?_, ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

/-- The data segment, as the message of this arm and what is around it.
The message is 27 bytes at 1049080, which is `entryStackTop + 504`. -/
private theorem data_pieces (bytes : List UInt8) (hlength : bytes.length = 920) :
    ∃ a b c : List UInt8,
      bytes = a ++ (b ++ c) ∧ a.length = 504 ∧ b.length = 27 ∧
      c.length = 389 := by
  refine ⟨bytes.take 504, (bytes.drop 504).take 27, (bytes.drop 504).drop 27,
    by simp only [List.take_append_drop], ?_, ?_, ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

/-! ## The arm -/

/-- The short-input arm of the header read, without its final branch. -/
def headerBuild : Program :=
  [.localGet 1, .load32 4, .localTee 3, .const 3, .gtU, .br_if 0,
    .localGet 2, .const 48, .add, .const 17, .const 1049080, .const 27,
    .call 55, .localGet 2, .localGet 2, .load64 52, .store64 32,
    .localGet 2, .localGet 2, .load32 60, .store32 40, .localGet 2,
    .load32 48, .localTee 3, .const 2147483649, .eq, .br_if 1, .localGet 2,
    .localGet 3, .store32 48, .localGet 2, .localGet 2, .load64 32,
    .store64 52, .localGet 2, .localGet 2, .load32 40, .store32 60,
    .localGet 2, .const 16, .add, .localGet 2, .const 48, .add, .call 52,
    .localGet 2, .load32 16, .localTee 3, .const 2147483649, .eq, .br_if 1,
    .localGet 2, .load32 20, .localSet 4, .localGet 0, .localGet 2,
    .load64 24, .store64 8, .localGet 0, .localGet 4, .store32 4,
    .localGet 0, .localGet 3, .store32 0]

/-- The arm is the build and the branch out of the outer block. -/
theorem headerError_shape : headerError = headerBuild ++ [.br 3] := by rfl

set_option maxHeartbeats 2000000 in
/-- The short-input arm writes a decode error into the output slot.  Word 0
of the output is never `okTag`, and the frame keeps its 64 bytes. -/
theorem twp_header_error [WasmSmallStepGS hlc Universal.State]
    (out hdr frame len : UInt32) (heapId : GName)
    (frameBytes outBefore below dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hshort : ¬ (len > (3 : UInt32)))
    (hframeLength : frameBytes.length = 64)
    (houtLength : outBefore.length = 16)
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
      pointsTo_u32 0 (hdr + 4) len ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
          ∀ word3 : UInt32, ∀ frameAfter : List UInt8,
          ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame func49Depth below' -∗
          Slices.ByteSlice 0 frame frameAfter -∗
          Slices.ByteSlice 0 out
            (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
          pointsTo_u32 0 (hdr + 4) len -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜word0 ≠ okTag ∧ frameAfter.length = 64⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 hdr],
                  [.i32 frame, .i32 word0, .i32 word1, l5, l6, l7, l8, l9,
                    l10, l11, l12], stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12],
            stack⟩,
            headerBuild ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hframe, Hout, Hlen, Hdata, Hbump, Hstreams,
    Hcont⟩
  -- the arithmetic, named before the context grows
  have hokTag : okTag = (2147483649 : UInt32) := rfl
  have h27 : (27 : UInt32).toNat = 27 := rfl
  have hdataLen : dataBytes.length = 920 := by rw [hdataLength]; rfl
  have hE160 : errorNewDepth ≤ frame.toNat := by
    have : func49Depth = 176 := rfl
    have : errorNewDepth = 160 := rfl
    omega
  obtain ⟨⟨hq16, hq20, hq24, hq32, hq40, hq48, hq52, hq60⟩,
    hbf16_16, hbf16, hbf20, hbf24, hbf32, hbf40, hbf48_16, hbf48, hbf52,
    hbf60⟩ := frame_bounds frame hframeNowrap
  obtain ⟨⟨hqo0, hqo4, hqo8⟩, hbo0, hbo4, hbo8⟩ := out_bounds out houtNowrap
  obtain ⟨hh4, hh4a, hh4b, hh4c⟩ :=
    offset_facts hdr 4 4 rfl (by omega)
  obtain ⟨hf16, hf16a, hf16b, hf16c⟩ := offset_facts frame 16 16 rfl hq16
  obtain ⟨hf20, hf20a, hf20b, hf20c⟩ := offset_facts frame 20 20 rfl hq20
  obtain ⟨hf40, hf40a, hf40b, hf40c⟩ := offset_facts frame 40 40 rfl hq40
  obtain ⟨hf48, hf48a, hf48b, hf48c⟩ := offset_facts frame 48 48 rfl hq48
  obtain ⟨hf60, hf60a, hf60b, hf60c⟩ := offset_facts frame 60 60 rfl hq60
  obtain ⟨ho0, ho0a, ho0b, ho0c⟩ := offset_facts out 0 0 rfl hqo0
  obtain ⟨ho4, ho4a, ho4b, ho4c⟩ := offset_facts out 4 4 rfl hqo4
  have hfa52 := offset_facts64 frame 52 52 rfl hq52
  have hfa32 := offset_facts64 frame 32 32 rfl hq32
  have hfa24 := offset_facts64 frame 24 24 rfl hq24
  have hoa8 := offset_facts64 out 8 8 rfl hqo8
  -- the addresses of the pieces
  have ha16 : frame + UInt32.ofNat 16 = frame + 16 := rfl
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
  have ha20 : frame + (16 : UInt32) + UInt32.ofNat 4 = frame + 20 :=
    frame_offset frame 16 4 20 rfl
  have ha24 : frame + (20 : UInt32) + UInt32.ofNat 4 = frame + 24 :=
    frame_offset frame 20 4 24 rfl
  have hb4 : out + UInt32.ofNat 4 = out + 4 := rfl
  have hb8 : out + (4 : UInt32) + UInt32.ofNat 4 = out + 8 :=
    frame_offset out 4 4 8 rfl
  have hseg504 : entryStackTop + UInt32.ofNat 504 = 1049080 := by decide
  have hseg531 : (1049080 : UInt32) + UInt32.ofNat 27 = 1049107 := by decide
  -- the three regions, as named pieces
  obtain ⟨a, b, c1, c2, c3, d, hframeShape, ha, hb, hc1, hc2, hc3, hd⟩ :=
    frame_pieces frameBytes hframeLength
  obtain ⟨o0, o1, o2, houtShape, ho0len, ho1len, ho2len⟩ :=
    out_pieces outBefore houtLength
  obtain ⟨dpre, dmsg, dpost, hdataShape, hdpre, hdmsg, hdpost⟩ :=
    data_pieces dataBytes hdataLen
  have hc2one : c2.length = 4 * 1 := by rw [hc2]
  have ho1one : o1.length = 4 * 1 := by rw [ho1len]
  have ho0one : o0.length = 4 * 1 := by rw [ho0len]
  -- the frame splits into its six pieces
  isimp only [hframeShape] at Hframe
  ihave ⟨HfA, Hr1⟩ :=
    (Slices.ByteSlice_append 0 frame a (b ++ (c1 ++ (c2 ++ (c3 ++ d))))).mp $$
      Hframe
  isimp only [ha, ha16] at Hr1
  ihave ⟨HfB, Hr2⟩ :=
    (Slices.ByteSlice_append 0 (frame + 16) b (c1 ++ (c2 ++ (c3 ++ d)))).mp $$
      Hr1
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
  -- the output slot splits into its three pieces
  isimp only [houtShape] at Hout
  ihave ⟨Ho0, Hor1⟩ :=
    (Slices.ByteSlice_append 0 out o0 (o1 ++ o2)).mp $$ Hout
  isimp only [ho0len, hb4] at Hor1
  ihave ⟨Ho1, Ho2⟩ :=
    (Slices.ByteSlice_append 0 (out + 4) o1 o2).mp $$ Hor1
  isimp only [ho1len, hb8] at Ho2
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
  -- the guard: fewer than four bytes are left
  simp only [headerBuild, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := hdr) (offset := 4) len
    hh4 hh4a hh4b hh4c with Hlen
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  iapply twp_gtU (result := 0) (by rw [if_neg hshort])
  iapply twp_brIfZero
  -- absolute `func 55` builds the `io::Error` at `frame + 48`
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
        locals := [.i32 frame, .i32 len, l4, l5, l6, l7, l8, l9, l10, l11,
          l12], values := [] })
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
      ByteSlice_as_word (frame + 52) (frame + 52)
        (WordCodec.u32le.serialize [w1, w2]) rfl (ser_two_length w1 w2) $$
        Herr12
    ihave Hc1w := ByteSlice_as_word (frame + 32) (frame + 32) c1 rfl hc1 $$ HfC1
    wasm_twp_block_move
      (frame, 52, Wasm.RustStd.HashMap.Table.groupWord
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
    wasm_twp_rebind twp_load32 (address := frame) (offset := 60) w3
      hf60 hf60a hf60b hf60c with Hw3
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
    -- the word goes back where it was
    ihave Herr0arr := Hclose0 $$ Hw0
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
    -- the second block move: the middle two words come back
    wasm_twp_block_move
      (frame, 32, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [w1, w2]), hfa32)
      (frame, 52, Wasm.RustStd.HashMap.Table.groupWord
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
    wasm_twp_rebind twp_store32 (address := frame) (offset := 60) w3
      hf60 hf60a hf60b hf60c with Hw3
    ihave Herr3arr := Hclose3 $$ Hw3
    isimp only [List.set] at Herr3arr
    ihave Herr3 :=
      ByteSlice_of_cells (frame + 60) [w3] (cells_nowrap_one _ w3 hbf60) $$
        Herr3arr
    -- the error record, whole again
    ihave Herr12 :=
      ByteSlice_of_word (frame + 52) (frame + 52)
        (WordCodec.u32le.serialize [w1, w2]) rfl (ser_two_length w1 w2)
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
          locals := [.i32 frame, .i32 w0, l4, l5, l6, l7, l8, l9, l10, l11,
            l12], values := [] })
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
      -- the decode error splits into its three blocks
      isimp only [ser4_split112] at Hslot
      ihave ⟨Hv0s, Hv123⟩ :=
        (Slices.ByteSlice_append 0 (frame + 16)
          (WordCodec.u32le.serialize [v0])
          (WordCodec.u32le.serialize [v1] ++
            WordCodec.u32le.serialize [v2, v3])).mp $$ Hslot
      isimp only [ser_one_length, ha20] at Hv123
      ihave ⟨Hv1s, Hv23⟩ :=
        (Slices.ByteSlice_append 0 (frame + 20)
          (WordCodec.u32le.serialize [v1])
          (WordCodec.u32le.serialize [v2, v3])).mp $$ Hv123
      isimp only [ser_one_length, ha24] at Hv23
      -- the dead `okTag` test of the decode error
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
      iapply twp_eq (result := 0) (by rw [if_neg hv0'])
      iapply twp_brIfZero
      ihave Hv0arr := Hclosev0 $$ Hv0
      ihave Hv0s :=
        ByteSlice_of_cells (frame + 16) [v0] (cells_nowrap_one _ v0 hbf16) $$
          Hv0arr
      -- word 1 goes into local 4
      wasm_twp_pures [twp_localGet]
      ihave Hv1arr := cells_of_ByteSlice (frame + 20) [v1] $$ Hv1s
      ihave ⟨Hv1, Hclosev1⟩ :=
        cell_load (frame + 20) 0 [v1] 0 v1 (one_pos _) rfl (by decide) $$
          Hv1arr
      isimp only [UInt32.add_zero] at Hv1 Hclosev1
      wasm_twp_rebind twp_load32 (address := frame) (offset := 20) v1
        hf20 hf20a hf20b hf20c with Hv1
      wasm_twp_localSet
      ihave Hv1arr := Hclosev1 $$ Hv1
      ihave Hv1s :=
        ByteSlice_of_cells (frame + 20) [v1] (cells_nowrap_one _ v1 hbf20) $$
          Hv1arr
      -- the last two words go into the output slot
      ihave Hv23w :=
        ByteSlice_as_word (frame + 24) (frame + 24)
          (WordCodec.u32le.serialize [v2, v3]) rfl (ser_two_length v2 v3) $$
          Hv23
      ihave Ho2w := ByteSlice_as_word (out + 8) (out + 8) o2 rfl ho2len $$ Ho2
      wasm_twp_block_move
        (frame, 24, Wasm.RustStd.HashMap.Table.groupWord
          (WordCodec.u32le.serialize [v2, v3]), hfa24)
        (out, 8, Wasm.RustStd.HashMap.Table.groupWord o2, hoa8)
        with Hv23w Ho2w
      -- word 1 and word 0 go into the output slot
      wasm_twp_pures [twp_localGet twp_localGet]
      ihave ⟨%ho1Words, Ho1arr⟩ :=
        ByteSlice_as_cells (out + 4) o1 1 ho1one $$ Ho1
      obtain ⟨y1, hy1⟩ := one_word (Slices.decodeWords o1) ho1Words
      isimp only [hy1] at Ho1arr
      ihave ⟨Hy1, Hclosey1⟩ :=
        cell_focus (out + 4) 0 [y1] 0 y1 v1 (one_pos _) rfl (by decide) $$
          Ho1arr
      isimp only [UInt32.add_zero] at Hy1 Hclosey1
      wasm_twp_rebind twp_store32 (address := out) (offset := 4) y1
        ho4 ho4a ho4b ho4c with Hy1
      ihave Ho1arr := Hclosey1 $$ Hy1
      isimp only [List.set] at Ho1arr
      ihave Ho1 :=
        ByteSlice_of_cells (out + 4) [v1] (cells_nowrap_one _ v1 hbo4) $$
          Ho1arr
      wasm_twp_pures [twp_localGet twp_localGet]
      ihave ⟨%ho0Words, Ho0arr⟩ :=
        ByteSlice_as_cells out o0 1 ho0one $$ Ho0
      obtain ⟨y0, hy0⟩ := one_word (Slices.decodeWords o0) ho0Words
      isimp only [hy0] at Ho0arr
      ihave ⟨Hy0, Hclosey0⟩ :=
        cell_focus out 0 [y0] 0 y0 v0 (one_pos _) rfl (by decide) $$ Ho0arr
      wasm_twp_rebind twp_store32 (address := out) (offset := 0) y0
        ho0 ho0a ho0b ho0c with Hy0
      ihave Ho0arr := Hclosey0 $$ Hy0
      isimp only [List.set] at Ho0arr
      ihave Ho0 :=
        ByteSlice_of_cells out [v0] (cells_nowrap_one _ v0 hbo0) $$ Ho0arr
      -- the output slot, whole again
      ihave Ho2 :=
        ByteSlice_of_word (out + 8) (out + 8)
          (WordCodec.u32le.serialize [v2, v3]) rfl (ser_two_length v2 v3)
          hbo8 $$ Ho2w
      ihave Hor1 :=
        ByteSlice_glue (out + 4) (WordCodec.u32le.serialize [v1])
          (WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v1) $$
          [Ho1 Ho2]
      · isplitl_exact Ho1
        · irw_exact [hb8] with Ho2
      ihave Hout :=
        ByteSlice_glue out (WordCodec.u32le.serialize [v0])
          (WordCodec.u32le.serialize [v1] ++
            WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v0) $$
          [Ho0 Hor1]
      · isplitl_exact Ho0
        · irw_exact [hb4] with Hor1
      isimp only [← ser4_split112] at Hout
      -- the frame, whole again
      ihave Hv23 :=
        ByteSlice_of_word (frame + 24) (frame + 24)
          (WordCodec.u32le.serialize [v2, v3]) rfl (ser_two_length v2 v3)
          hbf24 $$ Hv23w
      ihave Hv123 :=
        ByteSlice_glue (frame + 20) (WordCodec.u32le.serialize [v1])
          (WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v1) $$
          [Hv1s Hv23]
      · isplitl_exact Hv1s
        · irw_exact [ha24] with Hv23
      ihave HfB :=
        ByteSlice_glue (frame + 16) (WordCodec.u32le.serialize [v0])
          (WordCodec.u32le.serialize [v1] ++
            WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v0) $$
          [Hv0s Hv123]
      · isplitl_exact Hv0s
        · irw_exact [ha20] with Hv123
      isimp only [← ser4_split112] at HfB
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
      ihave HfBD :=
        ByteSlice_glue (frame + 16)
          (WordCodec.u32le.serialize [v0, v1, v2, v3])
          (WordCodec.u32le.serialize [w1, w2] ++
            (WordCodec.u32le.serialize [w3] ++ (c3 ++ errAfter))) 16
          (ser_four_length v0 v1 v2 v3) $$ [HfB HfC1D]
      · isplitl_exact HfB
        · irw_exact [ha32] with HfC1D
      ihave Hframe :=
        ByteSlice_glue frame a
          (WordCodec.u32le.serialize [v0, v1, v2, v3] ++
            (WordCodec.u32le.serialize [w1, w2] ++
              (WordCodec.u32le.serialize [w3] ++ (c3 ++ errAfter)))) 16
          ha $$ [HfA HfBD]
      · isplitl_exact HfA
        · irw_exact [ha16] with HfBD
      -- the continuation
      obtain ⟨frameAfter, hframeAfter⟩ :
          ∃ t : List UInt8,
            t = a ++ (WordCodec.u32le.serialize [v0, v1, v2, v3] ++
              (WordCodec.u32le.serialize [w1, w2] ++
                (WordCodec.u32le.serialize [w3] ++ (c3 ++ errAfter)))) :=
        ⟨_, rfl⟩
      isimp only [← hframeAfter] at Hframe
      have hframeAfterLength : frameAfter.length = 64 := by
        rw [hframeAfter]
        simp only [List.length_append, ser_one_length, ser_two_length,
          ser_four_length, ha, hc3, hafterLength, Nat.reduceAdd]
      ihave Hnormal := BI.and_elim_l $$ Hcont
      ihave Hnormal := Hnormal $$ %v0 %v1 %v2 %v3 %frameAfter %belowB
        %storedCursorB %frontierB %historyB
      iapply Hnormal $$ Hruntime Hsp Hbelow Hframe Hout Hlen Hdata Hbump
        Hstreams %⟨hv0, hframeAfterLength⟩
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Decoder
