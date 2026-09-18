import Project.RustHashMap.DecoderShortValue

/-!
# The borsh decoder: the writes of the error return

Every error arm of the decoder leaves the four words of the decode error
in the frame at `frame + 16` and word 0 of the error in local 11.  The
error return, WAT lines 821 to 844, copies them into the output slot and
then frees the pair buffer.

This module proves the copy.  `errorStores` below is the first four writes:

1. Word 1 of the error goes into local 3.
2. Words 2 and 3 go into the output slot at `out + 8`, as one `i64` move.
3. Word 1 goes into the output slot at `out + 4`.
4. Local 11 goes into the output slot at `out + 0`.

The frame keeps its four words, and the output slot takes local 11 first
and the last three words of the error after it.  The free that follows the
copy tests the capacity word and branches, so it belongs to the proof of
the outer block and not here.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The 1, 1, 2 split of a four-word record. -/
private theorem ser4_split112 (w0 w1 w2 w3 : UInt32) :
    WordCodec.u32le.serialize [w0, w1, w2, w3] =
      WordCodec.u32le.serialize [w0] ++
        (WordCodec.u32le.serialize [w1] ++
          WordCodec.u32le.serialize [w2, w3]) := by
  simp [WordCodec.serialize_cons, WordCodec.serialize_nil]

/-- The 16 bytes of the output slot, as the three pieces that the copy
writes. -/
private theorem out_pieces (bytes : List UInt8) (hlength : bytes.length = 16) :
    ∃ a b c : List UInt8,
      bytes = a ++ (b ++ c) ∧ a.length = 4 ∧ b.length = 4 ∧ c.length = 8 := by
  refine ⟨bytes.take 4, (bytes.drop 4).take 4, (bytes.drop 4).drop 4,
    by simp only [List.take_append_drop], ?_, ?_, ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

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

/-- Every address bound of the two error words that the copy reads. -/
private theorem slot_bounds (base : UInt32)
    (h : base.toNat + 64 < UInt32.size) :
    base.toNat + 20 + 4 ≤ UInt32.size ∧ base.toNat + 24 + 8 ≤ UInt32.size ∧
      (base + 20).toNat + 4 < UInt32.size ∧
      (base + 24).toNat + 8 < UInt32.size := by
  have h20 : (base + (20 : UInt32)).toNat = base.toNat + 20 :=
    Slices.byteOffset_toNat base 20 (by omega)
  have h24 : (base + (24 : UInt32)).toNat = base.toNat + 24 :=
    Slices.byteOffset_toNat base 24 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The four writes of the error return. -/
def errorStores : Program :=
  [.localGet 2, .load32 20, .localSet 3, .localGet 0, .localGet 2,
    .load64 24, .store64 8, .localGet 0, .localGet 3, .store32 4,
    .localGet 0, .localGet 11, .store32 0]

/-- The error return is the four writes and the free of the pair buffer. -/
theorem errorReturn_shape :
    errorReturn = errorStores ++
      [.localGet 2, .load32 4, .localTee 3, .eqz, .br_if 0, .localGet 8,
        .localGet 3, .const 3, .shl, .const 4, .call 60] := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The copy of the error return.  The output slot takes local 11 and the
last three words of the decode error, and the frame keeps all four. -/
theorem twp_error_stores [WasmSmallStepGS hlc Universal.State]
    (out hdr frame word0 v0 v1 v2 v3 : UInt32) (outBefore : List UInt8)
    (l3 l4 l5 l6 l7 l8 l9 l10 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (houtLength : outBefore.length = 16)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      Slices.ByteSlice 0 (frame + 16)
        (WordCodec.u32le.serialize [v0, v1, v2, v3]) ∗
      (Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [word0, v1, v2, v3]) -∗
        Slices.ByteSlice 0 (frame + 16)
            (WordCodec.u32le.serialize [v0, v1, v2, v3]) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 v1, l4, l5, l6, l7, l8, l9, l10,
                  .i32 word0, l12], stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, .i32 word0, l12],
            stack⟩,
            errorStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hslot, Hcont⟩
  obtain ⟨hs20, hs24, hs20b, hs24b⟩ := slot_bounds frame hframeNowrap
  obtain ⟨⟨hqo0, hqo4, hqo8⟩, hbo0, hbo4, hbo8⟩ := out_bounds out houtNowrap
  obtain ⟨hf20, hf20a, hf20b, hf20c⟩ := offset_facts frame 20 20 rfl hs20
  obtain ⟨ho0, ho0a, ho0b, ho0c⟩ := offset_facts out 0 0 rfl hqo0
  obtain ⟨ho4, ho4a, ho4b, ho4c⟩ := offset_facts out 4 4 rfl hqo4
  have hfa24 := offset_facts64 frame 24 24 rfl hs24
  have hoa8 := offset_facts64 out 8 8 rfl hqo8
  have ha20 : frame + (16 : UInt32) + UInt32.ofNat 4 = frame + 20 :=
    frame_offset frame 16 4 20 rfl
  have ha24 : frame + (20 : UInt32) + UInt32.ofNat 4 = frame + 24 :=
    frame_offset frame 20 4 24 rfl
  have hb4 : out + UInt32.ofNat 4 = out + 4 := rfl
  have hb8 : out + (4 : UInt32) + UInt32.ofNat 4 = out + 8 :=
    frame_offset out 4 4 8 rfl
  obtain ⟨o0, o1, o2, houtShape, ho0len, ho1len, ho2len⟩ :=
    out_pieces outBefore houtLength
  have ho0one : o0.length = 4 * 1 := by rw [ho0len]
  have ho1one : o1.length = 4 * 1 := by rw [ho1len]
  -- the decode error splits into its three blocks
  isimp only [ser4_split112] at Hslot
  ihave ⟨Hv0s, Hv123⟩ :=
    (Slices.ByteSlice_append 0 (frame + 16) (WordCodec.u32le.serialize [v0])
      (WordCodec.u32le.serialize [v1] ++
        WordCodec.u32le.serialize [v2, v3])).mp $$ Hslot
  isimp only [ser_one_length, ha20] at Hv123
  ihave ⟨Hv1s, Hv23⟩ :=
    (Slices.ByteSlice_append 0 (frame + 20) (WordCodec.u32le.serialize [v1])
      (WordCodec.u32le.serialize [v2, v3])).mp $$ Hv123
  isimp only [ser_one_length, ha24] at Hv23
  -- the output slot splits into its three pieces
  isimp only [houtShape] at Hout
  ihave ⟨Ho0, Hor1⟩ :=
    (Slices.ByteSlice_append 0 out o0 (o1 ++ o2)).mp $$ Hout
  isimp only [ho0len, hb4] at Hor1
  ihave ⟨Ho1, Ho2⟩ := (Slices.ByteSlice_append 0 (out + 4) o1 o2).mp $$ Hor1
  isimp only [ho1len, hb8] at Ho2
  simp only [errorStores, List.cons_append, List.nil_append]
  -- word 1 goes into local 3
  wasm_twp_pures [twp_localGet]
  ihave Hv1arr := cells_of_ByteSlice (frame + 20) [v1] $$ Hv1s
  ihave ⟨Hv1, Hclosev1⟩ :=
    cell_load (frame + 20) 0 [v1] 0 v1 (one_pos _) rfl (by decide) $$ Hv1arr
  isimp only [UInt32.add_zero] at Hv1 Hclosev1
  wasm_twp_rebind twp_load32 (address := frame) (offset := 20) v1
    hf20 hf20a hf20b hf20c with Hv1
  wasm_twp_localSet
  ihave Hv1arr := Hclosev1 $$ Hv1
  ihave Hv1s :=
    ByteSlice_of_cells (frame + 20) [v1] (cells_nowrap_one _ v1 hs20b) $$
      Hv1arr
  -- the last two words go into the output slot
  ihave Hv23w :=
    ByteSlice_as_word (frame + 24) (frame + 24)
      (WordCodec.u32le.serialize [v2, v3]) rfl (ser_two_length v2 v3) $$ Hv23
  ihave Ho2w := ByteSlice_as_word (out + 8) (out + 8) o2 rfl ho2len $$ Ho2
  wasm_twp_block_move
    (frame, 24, Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [v2, v3]), hfa24)
    (out, 8, Wasm.RustStd.HashMap.Table.groupWord o2, hoa8)
    with Hv23w Ho2w
  -- word 1 goes into the output slot
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave ⟨%ho1Words, Ho1arr⟩ := ByteSlice_as_cells (out + 4) o1 1 ho1one $$ Ho1
  obtain ⟨y1, hy1⟩ := one_word (Slices.decodeWords o1) ho1Words
  isimp only [hy1] at Ho1arr
  ihave ⟨Hy1, Hclosey1⟩ :=
    cell_focus (out + 4) 0 [y1] 0 y1 v1 (one_pos _) rfl (by decide) $$ Ho1arr
  isimp only [UInt32.add_zero] at Hy1 Hclosey1
  wasm_twp_rebind twp_store32 (address := out) (offset := 4) y1
    ho4 ho4a ho4b ho4c with Hy1
  ihave Ho1arr := Hclosey1 $$ Hy1
  isimp only [List.set] at Ho1arr
  ihave Ho1 :=
    ByteSlice_of_cells (out + 4) [v1] (cells_nowrap_one _ v1 hbo4) $$ Ho1arr
  -- local 11 goes into the output slot
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave ⟨%ho0Words, Ho0arr⟩ := ByteSlice_as_cells out o0 1 ho0one $$ Ho0
  obtain ⟨y0, hy0⟩ := one_word (Slices.decodeWords o0) ho0Words
  isimp only [hy0] at Ho0arr
  ihave ⟨Hy0, Hclosey0⟩ :=
    cell_focus out 0 [y0] 0 y0 word0 (one_pos _) rfl (by decide) $$ Ho0arr
  wasm_twp_rebind twp_store32 (address := out) (offset := 0) y0
    ho0 ho0a ho0b ho0c with Hy0
  ihave Ho0arr := Hclosey0 $$ Hy0
  isimp only [List.set] at Ho0arr
  ihave Ho0 :=
    ByteSlice_of_cells out [word0] (cells_nowrap_one _ word0 hbo0) $$ Ho0arr
  -- the output slot, whole again
  ihave Ho2 :=
    ByteSlice_of_word (out + 8) (out + 8)
      (WordCodec.u32le.serialize [v2, v3]) rfl (ser_two_length v2 v3)
      hbo8 $$ Ho2w
  ihave Hor1 :=
    ByteSlice_glue (out + 4) (WordCodec.u32le.serialize [v1])
      (WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v1) $$ [Ho1 Ho2]
  · isplitl_exact Ho1
    · irw_exact [hb8] with Ho2
  ihave Hout :=
    ByteSlice_glue out (WordCodec.u32le.serialize [word0])
      (WordCodec.u32le.serialize [v1] ++
        WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length word0) $$
      [Ho0 Hor1]
  · isplitl_exact Ho0
    · irw_exact [hb4] with Hor1
  isimp only [← ser4_split112] at Hout
  -- the frame slot, whole again
  ihave Hv23 :=
    ByteSlice_of_word (frame + 24) (frame + 24)
      (WordCodec.u32le.serialize [v2, v3]) rfl (ser_two_length v2 v3)
      hs24b $$ Hv23w
  ihave Hv123 :=
    ByteSlice_glue (frame + 20) (WordCodec.u32le.serialize [v1])
      (WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v1) $$
      [Hv1s Hv23]
  · isplitl_exact Hv1s
    · irw_exact [ha24] with Hv23
  ihave Hslot :=
    ByteSlice_glue (frame + 16) (WordCodec.u32le.serialize [v0])
      (WordCodec.u32le.serialize [v1] ++
        WordCodec.u32le.serialize [v2, v3]) 4 (ser_one_length v0) $$
      [Hv0s Hv123]
  · isplitl_exact Hv0s
    · irw_exact [ha20] with Hv123
  isimp only [← ser4_split112] at Hslot
  iapply Hcont $$ Hout Hslot

end Project.RustHashMap.Decoder
