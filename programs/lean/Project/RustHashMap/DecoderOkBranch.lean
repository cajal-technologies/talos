import Project.RustHashMap.DecoderOkReturn

/-!
# The accepting return of the decoder with its branch

`Project.RustHashMap.Decoder.okReturn` is `okStores` and then `.br 2`.
`Project.RustHashMap.Decoder.twp_ok_stores` proves the stores, so this
file adds the branch and gives the lemma the shape that the first arm of
`LoopCont` hands over.

The loop gives the three vector words of the frame one word at a time,
while `twp_ok_stores` asks for the twelve bytes as one slice.
`frame_words_join` and `frame_words_split` move between the two shapes
through `arrayAt`.

The branch leaves two blocks, the decode block and the allocation block,
so the caller gives the target of depth 2 as a hypothesis.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- Two offsets from one base add. -/
private theorem frame_step4 (frame a b : UInt32) (h : a + 4 = b) :
    frame + a + 4 = frame + b := by
  rw [UInt32.add_assoc, h]

/-- The three vector words stay inside the frame. -/
private theorem frame_words_nowrap (frame : UInt32)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    (frame + 4).toNat +
      4 * ([0, 0, 0] : List UInt32).length < UInt32.size := by
  have h4 : (frame + 4).toNat = frame.toNat + 4 :=
    Slices.byteOffset_toNat frame 4 (by omega)
  rw [h4]
  simp only [List.length_cons, List.length_nil]
  omega

/-- Three frame words are the twelve bytes above the frame base. -/
theorem frame_words_join [WasmHeapGS Universal.State]
    (frame capacity buffer length : UInt32)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(pointsTo_u32 0 (frame + 4) capacity ∗
      pointsTo_u32 0 (frame + 8) buffer ∗
      pointsTo_u32 0 (frame + 12) length) ⊢
      Slices.ByteSlice 0 (frame + 4)
        (WordCodec.u32le.serialize [capacity, buffer, length]) := by
  iintro ⟨Hcapacity, Hbuffer, Hlength⟩
  iapply ByteSlice_of_cells (frame + 4) [capacity, buffer, length]
    (frame_words_nowrap frame hframeNowrap)
  isimp only [arrayAt, frame_step4 frame 4 8 (by decide),
    frame_step4 frame 8 12 (by decide)]
  iframe Hcapacity Hbuffer Hlength

/-- The twelve bytes above the frame base are three frame words. -/
theorem frame_words_split [WasmHeapGS Universal.State]
    (frame capacity buffer length : UInt32) :
    Slices.ByteSlice 0 (frame + 4)
        (WordCodec.u32le.serialize [capacity, buffer, length]) ⊢
      iprop(pointsTo_u32 0 (frame + 4) capacity ∗
        pointsTo_u32 0 (frame + 8) buffer ∗
        pointsTo_u32 0 (frame + 12) length) := by
  iintro Hbytes
  ihave Hcells := cells_of_ByteSlice (frame + 4) [capacity, buffer, length]
    $$ Hbytes
  isimp only [arrayAt, frame_step4 frame 4 8 (by decide),
    frame_step4 frame 8 12 (by decide)] at Hcells
  icases Hcells with ⟨Hcapacity, Hbuffer, Hlength, Hempty⟩
  iframe Hcapacity Hbuffer Hlength

set_option maxHeartbeats 2000000 in
/-- The accepting return writes the output slot and leaves both blocks. -/
theorem twp_ok_return [WasmSmallStepGS hlc Universal.State]
    (out hdr frame capacity buffer length : UInt32) (outBefore : List UInt8)
    (l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    (targetCode : Program) (targetControls : List ControlFrame)
    (targetValues : List Value)
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (houtLength : outBefore.length = 16)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (htarget : branchTarget? arity 2 controls [] =
      some (targetCode, targetControls, targetValues)) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 (frame + 4) capacity ∗
      pointsTo_u32 0 (frame + 8) buffer ∗
      pointsTo_u32 0 (frame + 12) length ∗
      (Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [okTag, capacity, buffer, length]) -∗
        pointsTo_u32 0 (frame + 4) capacity -∗
        pointsTo_u32 0 (frame + 8) buffer -∗
        pointsTo_u32 0 (frame + 12) length -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12],
              targetValues⟩,
              targetCode, arity, remainder, targetControls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12], []⟩,
            okReturn, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hcapacity, Hbuffer, Hlength, Hcont⟩
  ihave Hframe := frame_words_join frame capacity buffer length hframeNowrap
    $$ [Hcapacity Hbuffer Hlength]
  · isplitl_exact Hcapacity
    · isplitl_exact Hbuffer
      · iexact Hlength
  rw [okReturn_shape]
  iapply twp_ok_stores out hdr frame capacity buffer length outBefore
    l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 houtLength houtNowrap hframeNowrap
  isplitl_exacts [Hout Hframe]
  iintro Hout Hframe
  iapply twp_br htarget
  ihave ⟨Hcapacity, Hbuffer, Hlength⟩ :=
    frame_words_split frame capacity buffer length $$ Hframe
  iapply Hcont $$ Hout Hcapacity Hbuffer Hlength

end Project.RustHashMap.Decoder
