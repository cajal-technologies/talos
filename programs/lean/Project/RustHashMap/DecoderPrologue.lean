import Project.RustHashMap.DecodeErrorContract
import Project.RustHashMap.FrameCells

/-!
# The borsh decoder: the frame and the empty result

This module proves the two straight-line fragments of the decoder that need
no callee.  The proof of the body can then use them as one step each.

* `twp_decoder_frame` runs `framePrologue`, WAT lines 472 to 476.  It lowers
  the stack pointer by 64 and keeps the new value in local 2.  It splits the
  region below the pointer into the 64 bytes of the frame and the region that
  the callees of the decoder get.
* `twp_empty_result` runs `emptyStores`, WAT lines 566 to 571.  A declared
  pair count of zero allocates nothing, so the two `i64` stores fill the whole
  16-byte output slot with the four words `okTag, 0, 4, 0`.

The rest of the header stage calls absolute `func 52`, the decode-error
conversion.  `Project.RustHashMap.BodyContracts.Func52Spec` states its
contract, `Project.RustHashMap.DecodeErrorContracts` names the 14 bodies
below it, and `Func52Proof.func52_correct` proves it.
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

set_option maxHeartbeats 2000000 in
/-- The frame of the decoder.  The body keeps 64 bytes of the region below
the caller and lends the rest to its callees. -/
theorem twp_decoder_frame [WasmSmallStepGS hlc Universal.State]
    (sp out hdr : UInt32) (below : List UInt8)
    (l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      StackPointer sp ∗
      StackBelow sp decoderDepth below ∗
      (StackPointer (sp - 64) -∗
        StackBelow (sp - 64) func49Depth (below.take func49Depth) -∗
        Slices.ByteSlice 0 (sp - 64) (below.drop func49Depth) -∗
        ⌜(below.drop func49Depth).length = 64⌝ -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 (sp - 64), l3, l4, l5, l6, l7, l8, l9, l10, l11, l12],
                stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12], stack⟩,
            framePrologue ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hsp, Hbelow, Hcont⟩
  have hcut : decoderDepth - 64 = func49Depth := rfl
  have hbase : sp - UInt32.ofNat 64 = sp - 64 := rfl
  isimp only [StackPointer] at Hsp
  simp only [framePrologue, List.cons_append, List.nil_append]
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp decoderDepth 64 below (by decide) $$ Hbelow
  isimp only [hcut, hbase] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 64) 64 (below.drop func49Depth) hbase $$ Hframe
  ihave Hsp : StackPointer (sp - 64) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ Hsp Hlower Hframe
  ipureintro
  exact hframeLength


/-- The stores of the empty vector.  A declared count of zero allocates
nothing, so the output slot takes the tag, the capacity 0, the dangling
pointer 4 and the length 0.  WAT lines 566 to 571. -/
def emptyStores : Program :=
  [.localGet 0, .constI64 4, .store64 8, .localGet 0,
    .constI64 2147483649, .store64 0]

/-- `emptyResult` is the stores and the branch out of the header stage. -/
theorem emptyResult_shape : emptyResult = emptyStores ++ [.br 1] := by rfl

private theorem groupWord_four :
    Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [(4 : UInt32), 0]) = 4 := by decide

private theorem groupWord_okTag :
    Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [okTag, 0]) = 2147483649 := by decide

set_option maxHeartbeats 2000000 in
/-- The empty vector.  The two `i64` stores fill the whole output slot. -/
theorem twp_empty_result [WasmSmallStepGS hlc Universal.State]
    (out hdr : UInt32) (outBefore : List UInt8)
    (l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (houtLength : outBefore.length = 16)
    (hout : out.toNat + 16 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      (Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [okTag, 0, 4, 0]) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12], stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12], stack⟩,
            emptyStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hcont⟩
  have hlow : (outBefore.take 8).length = 8 := by
    simp [houtLength]
  have hhigh : (outBefore.drop 8).length = 8 := by
    rw [List.length_drop, houtLength]
  have hlit8 : out + UInt32.ofNat 8 = out + 8 := rfl
  have hfa0 := offset_facts64 out 0 0 rfl (by omega)
  have hfa8 := offset_facts64 out 8 8 rfl (by omega)
  simp only [emptyStores, List.cons_append, List.nil_append]
  ihave ⟨Hlow, Hhigh⟩ := ByteSlice_cut out outBefore 8 (by omega) $$ Hout
  isimp only [hlit8] at Hhigh
  ihave Hhighword :=
    ByteSlice_as_word (out + 8) (out + 8) (outBefore.drop 8) rfl hhigh $$
      Hhigh
  ihave Hlowword :=
    ByteSlice_as_word out (out + 0) (outBefore.take 8) (by
      rw [UInt32.add_zero]) hlow $$ Hlow
  wasm_twp_pures [twp_localGet twp_constI64]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 8)
    (Wasm.RustStd.HashMap.Table.groupWord (outBefore.drop 8))
    hfa8.1 hfa8.2.1 hfa8.2.2.1 hfa8.2.2.2.1 hfa8.2.2.2.2.1
    hfa8.2.2.2.2.2.1 hfa8.2.2.2.2.2.2.1 hfa8.2.2.2.2.2.2.2 with Hhighword
  wasm_twp_pures [twp_localGet twp_constI64]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 0)
    (Wasm.RustStd.HashMap.Table.groupWord (outBefore.take 8))
    hfa0.1 hfa0.2.1 hfa0.2.2.1 hfa0.2.2.2.1 hfa0.2.2.2.2.1
    hfa0.2.2.2.2.2.1 hfa0.2.2.2.2.2.2.1 hfa0.2.2.2.2.2.2.2 with Hlowword
  ihave Hhigh :=
    ByteSlice_of_word (out + 8) (out + 8)
      (WordCodec.u32le.serialize [(4 : UInt32), 0]) rfl
      (by simp) (by
        have h := hfa8.1
        have h8 : (8 : UInt32).toNat = 8 := rfl
        omega) $$
      [Hhighword]
  · irw_exact [← groupWord_four] with Hhighword
  ihave Hlow :=
    ByteSlice_of_word out (out + 0)
      (WordCodec.u32le.serialize [okTag, 0]) (by rw [UInt32.add_zero])
      (by simp) (by omega) $$ [Hlowword]
  · irw_exact [← groupWord_okTag] with Hlowword
  ihave Hout :=
    ByteSlice_glue out (WordCodec.u32le.serialize [okTag, 0])
      (WordCodec.u32le.serialize [(4 : UInt32), 0]) 8
      (by simp) $$ [Hlow Hhigh]
  · isplitl_exact Hlow
    · irw_exact [hlit8] with Hhigh
  iapply Hcont
  wasm_serialize_norm at Hout
  isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil, List.append_assoc]
  iexact Hout

end Project.RustHashMap.Decoder
