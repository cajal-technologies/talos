import Project.RustHashMap.DecoderAlloc

/-!
# The borsh decoder: the accepting return

Every pair that the header declared is written, so the decoder copies the
three words of the vector out of the frame and into the output slot under
the tag `okTag`.  That is
`Project.RustHashMap.Decoder.okReturn`, WAT lines 803 to 814.

`okStores` below is the return without its final branch, so the lemma
holds for any control stack.  The caller does the branch.

The frame holds the capacity at offset 4, the pointer at offset 8 and the
length at offset 12.  The output slot takes the tag at offset 0, then the
same three words in the same order.  The two `i64` moves of the compiled
body copy the capacity and the pointer as one block.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- A one-word list is not empty. -/
private theorem one_pos (w : UInt32) : 0 < ([w] : List UInt32).length := by
  simp

/-- The bound that `ByteSlice_of_cells` asks for over a one-word list. -/
private theorem cells_nowrap_one (base w : UInt32)
    (hbound : base.toNat + 4 < UInt32.size) :
    base.toNat + 4 * ([w] : List UInt32).length < UInt32.size := by
  simpa using hbound

private theorem ser_one_length (w : UInt32) :
    (WordCodec.u32le.serialize [w]).length = 4 := by simp

private theorem ser_two_length (a b : UInt32) :
    (WordCodec.u32le.serialize [a, b]).length = 8 := by simp

/-- Three words, as a two-word block and a one-word block. -/
private theorem ser3_split21 (a b c : UInt32) :
    WordCodec.u32le.serialize [a, b, c] =
      WordCodec.u32le.serialize [a, b] ++ WordCodec.u32le.serialize [c] := by
  simp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil, List.append_assoc]

/-- Four words, as a word, a two-word block and a word. -/
private theorem ser4_split121 (w0 w1 w2 w3 : UInt32) :
    WordCodec.u32le.serialize [w0, w1, w2, w3] =
      WordCodec.u32le.serialize [w0] ++
        (WordCodec.u32le.serialize [w1, w2] ++
          WordCodec.u32le.serialize [w3]) := by
  simp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil, List.append_assoc]

/-- Two offsets from one base add. -/
private theorem add_lit (base a b c : UInt32) (h : a + b = c) :
    base + a + b = base + c := by
  rw [UInt32.add_assoc, h]

/-- The sixteen-byte output slot, as a word, a block and a word. -/
private theorem out_pieces (bytes : List UInt8) (hlength : bytes.length = 16) :
    ∃ a b c : List UInt8, bytes = a ++ (b ++ c) ∧
      a.length = 4 ∧ b.length = 8 ∧ c.length = 4 := by
  refine ⟨bytes.take 4, (bytes.drop 4).take 8, (bytes.drop 4).drop 8, ?_,
    ?_, ?_, ?_⟩ <;>
    simp only [List.take_append_drop, List.length_take, List.length_drop,
      hlength] <;> omega

/-- The accepting return, without its final branch. -/
def okStores : Program :=
  [.localGet 0, .localGet 2, .load32 12, .store32 12, .localGet 0,
    .localGet 2, .load64 4, .store64 4, .localGet 0, .const 2147483649,
    .store32 0]

/-- The return is the stores and the branch out of the allocation block. -/
theorem okReturn_shape : okReturn = okStores ++ [.br 2] := by rfl

set_option maxHeartbeats 2000000 in
/-- The accepting return.  The output slot takes the tag and the three
words of the vector.  The frame keeps its own copy. -/
theorem twp_ok_stores [WasmSmallStepGS hlc Universal.State]
    (out hdr frame capacity buffer length : UInt32) (outBefore : List UInt8)
    (l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (houtLength : outBefore.length = 16)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      Slices.ByteSlice 0 (frame + 4)
        (WordCodec.u32le.serialize [capacity, buffer, length]) ∗
      (Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [okTag, capacity, buffer, length]) -∗
        Slices.ByteSlice 0 (frame + 4)
          (WordCodec.u32le.serialize [capacity, buffer, length]) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12],
              stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12],
            stack⟩,
            okStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hframe, Hcont⟩
  -- the arithmetic, named before the context grows
  have hout4 : out + UInt32.ofNat 4 = out + 4 := rfl
  have hout12 : out + 4 + UInt32.ofNat 8 = out + 12 :=
    add_lit out 4 8 12 (by decide)
  have hframe12 : frame + 4 + UInt32.ofNat 8 = frame + 12 :=
    add_lit frame 4 8 12 (by decide)
  have hb4 : (frame + 4).toNat = frame.toNat + 4 :=
    Slices.byteOffset_toNat frame 4 (by omega)
  have hb12 : (frame + 12).toNat = frame.toNat + 12 :=
    Slices.byteOffset_toNat frame 12 (by omega)
  have ho4 : (out + 4).toNat = out.toNat + 4 :=
    Slices.byteOffset_toNat out 4 (by omega)
  have ho12 : (out + 12).toNat = out.toNat + 12 :=
    Slices.byteOffset_toNat out 12 (by omega)
  obtain ⟨hfl12, hfl12a, hfl12b, hfl12c⟩ := offset_facts frame 12 12 rfl (by omega)
  have hfl4 := offset_facts64 frame 4 4 rfl (by omega)
  obtain ⟨hos12, hos12a, hos12b, hos12c⟩ := offset_facts out 12 12 rfl (by omega)
  have hos4 := offset_facts64 out 4 4 rfl (by omega)
  obtain ⟨hos0, hos0a, hos0b, hos0c⟩ := offset_facts out 0 0 rfl (by omega)
  obtain ⟨outA, outB, outC, houtShape, houtA, houtB, houtC⟩ :=
    out_pieces outBefore houtLength
  -- cut the output slot into a word, a block and a word
  isimp only [houtShape] at Hout
  ihave ⟨HoutA, Hrest⟩ :=
    (Slices.ByteSlice_append 0 out outA (outB ++ outC)).mp $$ Hout
  isimp only [houtA, hout4] at Hrest
  ihave ⟨HoutB, HoutC⟩ :=
    (Slices.ByteSlice_append 0 (out + 4) outB outC).mp $$ Hrest
  isimp only [houtB, hout12] at HoutC
  -- cut the frame words into a block and a word
  isimp only [ser3_split21] at Hframe
  ihave ⟨HframeB, HframeC⟩ :=
    (Slices.ByteSlice_append 0 (frame + 4)
      (WordCodec.u32le.serialize [capacity, buffer])
      (WordCodec.u32le.serialize [length])).mp $$ Hframe
  isimp only [ser_two_length, hframe12] at HframeC
  -- the length word of the frame
  ihave HframeCells := cells_of_ByteSlice (frame + 12) [length] $$ HframeC
  ihave ⟨HframeLen, HframeClose⟩ :=
    cell_load (frame + 12) 0 [length] 0 length (one_pos _) rfl (by decide) $$
      HframeCells
  isimp only [UInt32.add_zero] at HframeLen HframeClose
  -- the old word of the output slot at offset 12
  ihave ⟨%houtCLen, HoutCCells⟩ :=
    ByteSlice_as_cells (out + 12) outC 1 (by omega) $$ HoutC
  obtain ⟨oldC, holdC⟩ := one_word (Slices.decodeWords outC) houtCLen
  isimp only [holdC] at HoutCCells
  ihave ⟨HoutCell, HoutCClose⟩ :=
    cell_focus (out + 12) 0 [oldC] 0 oldC length (one_pos _) rfl (by decide) $$
      HoutCCells
  isimp only [UInt32.add_zero] at HoutCell HoutCClose
  -- `[out + 12] := [frame + 12]`
  simp only [okStores, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := frame) (offset := 12) length
    hfl12 hfl12a hfl12b hfl12c with HframeLen
  wasm_twp_rebind twp_store32 (address := out) (offset := 12) oldC
    hos12 hos12a hos12b hos12c with HoutCell
  ihave HframeC := ByteSlice_of_cells (frame + 12) [length]
    (cells_nowrap_one (frame + 12) length (by omega)) $$ [HframeClose HframeLen]
  · iapply HframeClose
    iexact HframeLen
  ihave HoutCArr := HoutCClose $$ HoutCell
  isimp only [List.set] at HoutCArr
  ihave HoutC := ByteSlice_of_cells (out + 12) [length]
    (cells_nowrap_one (out + 12) length (by omega)) $$ HoutCArr
  -- `[out + 4] := [frame + 4]`, eight bytes as one block
  ihave HframeWord :=
    ByteSlice_as_word (frame + 4) (frame + 4)
      (WordCodec.u32le.serialize [capacity, buffer]) rfl
      (ser_two_length capacity buffer) $$ HframeB
  ihave HoutWord :=
    ByteSlice_as_word (out + 4) (out + 4) outB rfl houtB $$ HoutB
  wasm_twp_block_move
    (frame, 4, Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [capacity, buffer]), hfl4)
    (out, 4, Wasm.RustStd.HashMap.Table.groupWord outB, hos4)
    with HframeWord HoutWord
  ihave HframeB :=
    ByteSlice_of_word (frame + 4) (frame + 4)
      (WordCodec.u32le.serialize [capacity, buffer]) rfl
      (ser_two_length capacity buffer) (by omega) $$ HframeWord
  ihave HoutB :=
    ByteSlice_of_word (out + 4) (out + 4)
      (WordCodec.u32le.serialize [capacity, buffer]) rfl
      (ser_two_length capacity buffer) (by omega) $$ HoutWord
  -- `[out] := okTag`
  ihave ⟨%houtALen, HoutACells⟩ :=
    ByteSlice_as_cells out outA 1 (by omega) $$ HoutA
  obtain ⟨oldA, holdA⟩ := one_word (Slices.decodeWords outA) houtALen
  isimp only [holdA] at HoutACells
  ihave ⟨HoutCellA, HoutAClose⟩ :=
    cell_focus out 0 [oldA] 0 oldA okTag (one_pos _) rfl (by decide) $$
      HoutACells
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind twp_store32 (address := out) (offset := 0) oldA
    hos0 hos0a hos0b hos0c with HoutCellA
  ihave HoutCellA : pointsTo_u32 0 (out + 0) okTag $$ [HoutCellA]
  · isimp only [okTag]
    iexact HoutCellA
  ihave HoutAArr := HoutAClose $$ HoutCellA
  isimp only [List.set] at HoutAArr
  ihave HoutA := ByteSlice_of_cells out [okTag]
    (cells_nowrap_one out okTag (by omega)) $$ HoutAArr
  -- the frame and the output slot, whole again
  ihave Hframe := ByteSlice_glue (frame + 4)
    (WordCodec.u32le.serialize [capacity, buffer])
    (WordCodec.u32le.serialize [length]) 8
    (ser_two_length capacity buffer) $$ [HframeB HframeC]
  · isplitl_exact HframeB
    · irw_exact [hframe12] with HframeC
  ihave Hlow := ByteSlice_glue (out + 4)
    (WordCodec.u32le.serialize [capacity, buffer])
    (WordCodec.u32le.serialize [length]) 8
    (ser_two_length capacity buffer) $$ [HoutB HoutC]
  · isplitl_exact HoutB
    · irw_exact [hout12] with HoutC
  ihave Hout := ByteSlice_glue out (WordCodec.u32le.serialize [okTag])
    (WordCodec.u32le.serialize [capacity, buffer] ++
      WordCodec.u32le.serialize [length]) 4
    (ser_one_length okTag) $$ [HoutA Hlow]
  · isplitl_exact HoutA
    · irw_exact [hout4] with Hlow
  isimp only [← ser3_split21] at Hframe
  isimp only [← ser4_split121] at Hout
  iapply Hcont $$ Hout Hframe

end Project.RustHashMap.Decoder
