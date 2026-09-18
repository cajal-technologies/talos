import Project.RustHashMap.DecoderAppend

/-!
# The borsh decoder: the key read

Four or more unread bytes takes one loop step to
`Project.RustHashMap.Decoder.keyRead`, WAT lines 668 to 691.  The read
takes four bytes off the slice:

1. The length in the slice header goes down by four and the cursor goes up
   by four.
2. Local 12 keeps the new length and local 11 the new cursor.
3. Local 10 takes the key from the old cursor.

The step then compares the new length against four.  Four or more takes
the value read, which repeats both stores with a step of eight, so the two
stores here are dead on that path.  Fewer takes the short-input arm of the
value, which keeps them.

`keyStores` below is the read without the compare and the two branches, so
the lemma holds for any control stack.  The caller does all three.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The key read, without the compare and the two branches. -/
def keyStores : Program :=
  [.localGet 1, .localGet 5, .const 4294967292, .add, .localTee 12,
    .store32 4, .localGet 1, .localGet 6, .const 4, .add, .localTee 11,
    .store32 0, .localGet 6, .load32 0, .localSet 10]

/-- The read is the stores, the compare, and the two branches. -/
theorem keyRead_shape :
    keyRead = keyStores ++
      [.localGet 12, .const 4, .geU, .br_if 2, .localGet 11, .localSet 6,
        .localGet 12, .localSet 5, .br 1] := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The key read takes four bytes off the slice and loads the key. -/
theorem twp_key_stores [WasmSmallStepGS hlc Universal.State]
    (out hdr frame cursor remaining key oldPtr oldLen : UInt32)
    (l3 l4 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hcursorNowrap : cursor.toNat + 4 < UInt32.size) :
    iprop(
      pointsTo_u32 0 hdr oldPtr ∗
      pointsTo_u32 0 (hdr + 4) oldLen ∗
      pointsTo_u32 0 cursor key ∗
      (pointsTo_u32 0 hdr (cursor + 4) -∗
        pointsTo_u32 0 (hdr + 4) (remaining - 4) -∗
        pointsTo_u32 0 cursor key -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, l3, l4, .i32 remaining, .i32 cursor, l7, l8, l9,
                  .i32 key, .i32 (cursor + 4), .i32 (remaining - 4)],
              stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, .i32 remaining, .i32 cursor, l7, l8, l9,
                l10, l11, l12],
            stack⟩,
            keyStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hptr, Hlen, Hkey, Hcont⟩
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts hdr 4 4 rfl (by omega)
  obtain ⟨hf0, hf0a, hf0b, hf0c⟩ := offset_facts hdr 0 0 rfl (by omega)
  obtain ⟨hc1, hc2, hc3⟩ := addr_facts cursor (by omega)
  have hzero : hdr + 0 = hdr := UInt32.add_zero hdr
  simp only [keyStores, List.cons_append, List.nil_append]
  -- the new length goes into the slice header
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (4294967292 : UInt32), sub_four]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_store32 (address := hdr) (offset := 4) oldLen
    hf4 hf4a hf4b hf4c with Hlen
  -- the new cursor goes into the slice header
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [show (4 : UInt32) + cursor = cursor + 4 from UInt32.add_comm _ _]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  ihave Hptr := word_move hdr (hdr + 0) oldPtr hzero $$ Hptr
  wasm_twp_rebind twp_store32 (address := hdr) (offset := 0) oldPtr
    hf0 hf0a hf0b hf0c with Hptr
  ihave Hptr := word_move (hdr + 0) hdr (cursor + 4) hzero.symm $$ Hptr
  -- the key
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr (addr := cursor) key hc1 hc2 hc3 with Hkey
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply Hcont $$ Hptr Hlen Hkey

end Project.RustHashMap.Decoder
