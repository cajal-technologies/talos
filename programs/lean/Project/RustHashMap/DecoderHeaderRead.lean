import Project.RustHashMap.DecoderHeader

/-!
# The borsh decoder: the header read

Four or more bytes left takes the decoder out of the header block and into
`Project.RustHashMap.Decoder.headerRead`, WAT lines 547 to 564.  The read
does three things:

1. It takes four bytes off the slice.  The length goes down by four and the
   pointer goes up by four, in the slice header that local 1 points at.
2. It keeps the old pointer in local 3, the new length in local 5 and the
   new pointer in local 6.
3. It loads the four bytes as the declared pair count, into local 7 and
   onto the stack.

`headerAdvance` below is the read without its final branch, so the lemma
holds for any control stack.  The caller does the branch.

The `.store32 0` of the new pointer goes through `twp_store32` with the
offset 0, because the offset-free `twp_store32_addr` holds for the
normal-result adapter alone.  `word_move` carries the word between the
address `hdr` and the address `hdr + 0` on both sides of the rule.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DecodeErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- `.const 4294967292` is minus four.  The compiled body adds it where the
source subtracts four. -/
theorem sub_four (x : UInt32) : x + 4294967292 = x - 4 := by
  have hmax : (4294967292 : UInt32) = 0 - 4 := by decide
  calc x + 4294967292 = (x - 4 + 4) + (0 - 4) := by
        rw [UInt32.sub_add_cancel, hmax]
    _ = (x - 4) + ((0 - 4) + 4) := by ac_rfl
    _ = x - 4 := by rw [UInt32.sub_add_cancel, UInt32.add_zero]

/-- A byte slice carries its own bound. -/
private theorem ByteSlice_nowrap [WasmHeapGS Universal.State]
    (base : UInt32) (bytes : List UInt8) :
    Slices.ByteSlice 0 base bytes ⊢
      iprop(Slices.ByteSlice 0 base bytes ∗
        ⌜base.toNat + bytes.length < UInt32.size⌝) := by
  iintro Hslice
  unfold Slices.ByteSlice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  isplitl [Hbytes]
  · isplitl_pureexact hnowrap
    iexact Hbytes
  · ipureexact hnowrap

/-- Move an owned word between two names of one address. -/
theorem word_move [WasmHeapGS Universal.State]
    (addr target word : UInt32) (haddr : target = addr) :
    pointsTo_u32 0 addr word ⊢ pointsTo_u32 0 target word := by
  subst haddr
  iintro Hword
  iexact Hword

/-- The three address facts that the offset-free load rule asks for. -/
theorem addr_facts (base : UInt32)
    (hbound : base.toNat + 4 ≤ UInt32.size) :
    (base + 1).toNat = base.toNat + 1 ∧
      (base + 2).toNat = base.toNat + 2 ∧
      (base + 3).toNat = base.toNat + 3 :=
  ⟨Slices.byteOffset_toNat base 1 (by omega),
    Slices.byteOffset_toNat base 2 (by omega),
    Slices.byteOffset_toNat base 3 (by omega)⟩

/-- More than three bytes is four bytes or more. -/
private theorem four_le_of_three_lt {len : UInt32} (hlong : (3 : UInt32) < len) :
    4 ≤ len.toNat := by
  have h := UInt32.lt_iff_toNat_lt.mp hlong
  have h3 : (3 : UInt32).toNat = 3 := rfl
  omega

/-- The header read, without its final branch. -/
def headerAdvance : Program :=
  [.localGet 1, .localGet 3, .const 4294967292, .add, .localTee 5,
    .store32 4, .localGet 1, .localGet 1, .load32 0, .localTee 3, .const 4,
    .add, .localTee 6, .store32 0, .localGet 3, .load32 0, .localTee 7]

/-- The read is the advance and the branch out of the header stage. -/
theorem headerRead_shape : headerRead = headerAdvance ++ [.br_if 1] := by rfl

set_option maxHeartbeats 2000000 in
/-- The header read takes four bytes off the slice and loads the declared
pair count.  The bytes themselves do not move. -/
theorem twp_header_advance [WasmSmallStepGS hlc Universal.State]
    (out hdr frame ptr len : UInt32) (bytes : List UInt8)
    (l4 l5 l6 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hlong : (3 : UInt32) < len)
    (hbytesLength : bytes.length = len.toNat)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size) :
    iprop(
      pointsTo_u32 0 hdr ptr ∗
      pointsTo_u32 0 (hdr + 4) len ∗
      Slices.ByteSlice 0 ptr bytes ∗
      (pointsTo_u32 0 hdr (ptr + 4) -∗
        pointsTo_u32 0 (hdr + 4) (len - 4) -∗
        Slices.ByteSlice 0 ptr bytes -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 ptr, l4, .i32 (len - 4), .i32 (ptr + 4),
                  .i32 (headerWord bytes), l8, l9, l10, l11, l12],
              .i32 (headerWord bytes) :: stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 len, l4, l5, l6, l7, l8, l9, l10, l11, l12],
            stack⟩,
            headerAdvance ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hptr, Hlen, Hbytes, Hcont⟩
  isimp only [headerWord] at Hcont
  have hfour : 4 ≤ bytes.length := by
    rw [hbytesLength]; exact four_le_of_three_lt hlong
  ihave ⟨Hbytes, %hptrNowrap⟩ := ByteSlice_nowrap ptr bytes $$ Hbytes
  obtain ⟨hd1, hd2, hd3⟩ := addr_facts hdr (by omega)
  obtain ⟨hp1, hp2, hp3⟩ := addr_facts ptr (by omega)
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts hdr 4 4 rfl (by omega)
  obtain ⟨hf0, hf0a, hf0b, hf0c⟩ := offset_facts hdr 0 0 rfl (by omega)
  have hzero : hdr + 0 = hdr := UInt32.add_zero hdr
  -- the four bytes of the header, as the declared pair count
  ihave ⟨Hhead, Htail⟩ := ByteSlice_cut ptr bytes 4 hfour $$ Hbytes
  have hheadLength : (bytes.take 4).length = 4 := by
    rw [List.length_take]; omega
  ihave Hcount :=
    (Slices.ByteSlice_four_as_word 0 ptr (bytes.take 4) hheadLength
      (by omega)).mp $$ Hhead
  -- the new length goes into the slice header
  simp only [headerAdvance, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (4294967292 : UInt32), sub_four]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_store32 (address := hdr) (offset := 4) len
    hf4 hf4a hf4b hf4c with Hlen
  -- the new pointer goes into the slice header
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32_addr (addr := hdr) ptr hd1 hd2 hd3 with Hptr
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_add]
  rw [show (4 : UInt32) + ptr = ptr + 4 from UInt32.add_comm _ _]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  ihave Hptr := word_move hdr (hdr + 0) ptr hzero $$ Hptr
  wasm_twp_rebind twp_store32 (address := hdr) (offset := 0) ptr
    hf0 hf0a hf0b hf0c with Hptr
  ihave Hptr := word_move (hdr + 0) hdr (ptr + 4) hzero.symm $$ Hptr
  -- the count comes off the front of the payload
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr (addr := ptr)
    (WordCodec.decodeU32 (bytes.take 4)) hp1 hp2 hp3 with Hcount
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the payload, whole again
  ihave Hhead :=
    (Slices.ByteSlice_four_as_word 0 ptr (bytes.take 4) hheadLength
      (by omega)).mpr $$ Hcount
  ihave Hbytes := ByteSlice_glue ptr (bytes.take 4) (bytes.drop 4) 4
    hheadLength $$ [Hhead Htail]
  · isplitl_exact Hhead
    · iexact Htail
  isimp only [List.take_append_drop] at Hbytes
  iapply Hcont $$ Hptr Hlen Hbytes

end Project.RustHashMap.Decoder
