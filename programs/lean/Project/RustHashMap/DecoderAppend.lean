import Project.RustHashMap.DecoderPairRead

/-!
# The borsh decoder: the append of one pair

One loop step ends at `Project.RustHashMap.Decoder.appendPair`, WAT lines
777 to 801.  The append writes the pair that the step read:

1. Local 9 holds the byte offset of the next value.  It starts at 4 and
   steps by 8, so `buffer + offset` is the value slot and the four bytes
   below it are the key slot.
2. The key goes to `buffer + 8 i` and the value to `buffer + 8 i + 4`.
3. The length word of the vector at `frame + 12` takes `i + 1`, and local
   9 takes eight more.

`appendStores` below is the append without the compare and the back edge
of the loop, so the lemma holds for any control stack.  The caller does
the compare and the branch.

The lemma names the key slot `slot` and asks the caller for
`offset + buffer = slot + 4`.  That keeps the two owned words in the form
that the loop invariant carries, one pair at one address.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The key slot is four bytes below the value slot. -/
private theorem key_addr (x : UInt32) : 4294967292 + (x + 4) = x := by
  rw [UInt32.add_comm, sub_four, UInt32.add_sub_cancel]

/-- The append, without the compare and the back edge. -/
def appendStores : Program :=
  [.localGet 8, .localGet 9, .add, .localTee 11, .localGet 12, .store32 0,
    .localGet 11, .const 4294967292, .add, .localGet 10, .store32 0,
    .localGet 2, .localGet 3, .const 1, .add, .localTee 3, .store32 12,
    .localGet 9, .const 8, .add, .localSet 9]

/-- The step is the append, the compare, and the back edge. -/
theorem appendPair_shape :
    appendPair = appendStores ++ [.localGet 7, .localGet 3, .ne, .br_if 0] := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The append writes the key and the value, and raises the length. -/
theorem twp_append_stores [WasmSmallStepGS hlc Universal.State]
    (out hdr frame buffer offset slot key value written : UInt32)
    (oldKey oldValue oldCount : UInt32)
    (l4 l5 l6 l7 l11 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (haddr : offset + buffer = slot + 4)
    (hslotNowrap : slot.toNat + 8 < UInt32.size)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      pointsTo_u32 0 slot oldKey ∗
      pointsTo_u32 0 (slot + 4) oldValue ∗
      pointsTo_u32 0 (frame + 12) oldCount ∗
      (pointsTo_u32 0 slot key -∗
        pointsTo_u32 0 (slot + 4) value -∗
        pointsTo_u32 0 (frame + 12) (written + 1) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 (written + 1), l4, l5, l6, l7,
                  .i32 buffer, .i32 (offset + 8), .i32 key, .i32 (slot + 4),
                  .i32 value],
              stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 written, l4, l5, l6, l7, .i32 buffer,
                .i32 offset, .i32 key, l11, .i32 value],
            stack⟩,
            appendStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hkey, Hvalue, Hcount, Hcont⟩
  have hslot4 : (slot + 4).toNat = slot.toNat + 4 :=
    Slices.byteOffset_toNat slot 4 (by omega)
  obtain ⟨hv0, hv0a, hv0b, hv0c⟩ := offset_facts (slot + 4) 0 0 rfl (by omega)
  obtain ⟨hk0, hk0a, hk0b, hk0c⟩ := offset_facts slot 0 0 rfl (by omega)
  obtain ⟨hf12, hf12a, hf12b, hf12c⟩ := offset_facts frame 12 12 rfl (by omega)
  have hzeroV : slot + 4 + 0 = slot + 4 := UInt32.add_zero (slot + 4)
  have hzeroK : slot + 0 = slot := UInt32.add_zero slot
  simp only [appendStores, List.cons_append, List.nil_append]
  -- the value goes to `buffer + offset`
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
  rw [haddr]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  ihave Hvalue := word_move (slot + 4) (slot + 4 + 0) oldValue hzeroV $$ Hvalue
  wasm_twp_rebind twp_store32 (address := slot + 4) (offset := 0) oldValue
    hv0 hv0a hv0b hv0c with Hvalue
  ihave Hvalue := word_move (slot + 4 + 0) (slot + 4) value hzeroV.symm $$
    Hvalue
  -- the key goes four bytes below it
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [key_addr]
  wasm_twp_pures [twp_localGet]
  ihave Hkey := word_move slot (slot + 0) oldKey hzeroK $$ Hkey
  wasm_twp_rebind twp_store32 (address := slot) (offset := 0) oldKey
    hk0 hk0a hk0b hk0c with Hkey
  ihave Hkey := word_move (slot + 0) slot key hzeroK.symm $$ Hkey
  -- the length word of the vector
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (1 : UInt32) written]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_store32 (address := frame) (offset := 12) oldCount
    hf12 hf12a hf12b hf12c with Hcount
  -- the byte offset of the next value
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (8 : UInt32) offset]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply Hcont $$ Hkey Hvalue Hcount

end Project.RustHashMap.Decoder
