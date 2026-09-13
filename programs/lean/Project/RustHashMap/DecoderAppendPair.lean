import Project.RustHashMap.DecoderPairStage
import Project.RustHashMap.PairGrow

/-!
# The borsh decoder: the append into the live pair buffer

`Project.RustHashMap.Decoder.twp_append_stores` writes one pair through two
owned words at one address.  The loop carries the pair buffer as one live
block, so this file lifts the append to that form.

The block holds `capacity` pairs, and the step writes the pair of index
`index`.  The key slot is `buffer + 8 index` and the value slot is four
bytes above it, so the eight bytes of the slot come out of the block, take
the new pair, and go back.  The bytes of the block below and above the slot
do not change.

The lemma keeps the compare and the back edge of the loop with the caller,
because the back edge needs the loop frame and the loop invariant.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-! ## Words of the loop -/

/-- The length word of the vector steps by one. -/
theorem ofNat_succ_word (index : Nat) :
    UInt32.ofNat (index + 1) = UInt32.ofNat index + 1 := by
  rw [UInt32.ofNat_add]
  rfl

/-- The byte offset of the next value steps by eight. -/
theorem ofNat_offset_step (index : Nat) :
    UInt32.ofNat (8 * (index + 1) + 4) = UInt32.ofNat (8 * index + 4) + 8 := by
  rw [show 8 * (index + 1) + 4 = 8 * index + 4 + 8 from by omega,
    UInt32.ofNat_add]
  rfl

/-! ## The slot of one pair -/

/-- A byte slice does not wrap the address space. -/
private theorem ByteSlice_bound [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (bytes : List UInt8) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(Slices.ByteSlice 0 ptr bytes ∗
        ⌜ptr.toNat + bytes.length < UInt32.size⌝) := by
  iintro Hslice
  isimp only [Slices.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  isplitl [Hbytes]
  · unfold Slices.ByteSlice
    isplitl_pureexact hnowrap
    · iexact Hbytes
  · ipureexact hnowrap

/-- Two serialized words are two owned words. -/
theorem pair_words [WasmSmallStepGS hlc Universal.State]
    (addr key value : UInt32) (hnowrap : addr.toNat + 8 < UInt32.size) :
    Slices.ByteSlice 0 addr (WordCodec.u32le.serialize [key, value]) ⊣⊢
      iprop(pointsTo_u32 0 addr key ∗ pointsTo_u32 0 (addr + 4) value) := by
  have hsplit : WordCodec.u32le.serialize [key, value]
      = WordCodec.u32le.serialize [key] ++
        WordCodec.u32le.serialize [value] := by
    simp
  have hlen1 : (WordCodec.u32le.serialize [key]).length = 4 := by simp
  have hlen2 : (WordCodec.u32le.serialize [value]).length = 4 := by simp
  have hdec1 :
      WordCodec.decodeU32 (WordCodec.u32le.serialize [key]) = key := by
    change WordCodec.decodeU32 (WordCodec.encodeU32 key) = key
    exact WordCodec.u32le.decode_encode key
  have hdec2 :
      WordCodec.decodeU32 (WordCodec.u32le.serialize [value]) = value := by
    change WordCodec.decodeU32 (WordCodec.encodeU32 value) = value
    exact WordCodec.u32le.decode_encode value
  have haddr : (addr + 4).toNat = addr.toNat + 4 :=
    Slices.byteOffset_toNat addr 4 (by omega)
  have hstep4 : addr + UInt32.ofNat 4 = addr + 4 := by rfl
  rw [hsplit]
  refine (Slices.ByteSlice_append 0 addr _ _).trans ?_
  rw [hlen1, hstep4]
  refine BI.sep_congr ?_ ?_
  · have hword := Slices.ByteSlice_four_as_word (α := Universal.State) 0 addr
      (WordCodec.u32le.serialize [key]) hlen1 (by omega)
    rw [hdec1] at hword
    exact hword
  · have hword := Slices.ByteSlice_four_as_word (α := Universal.State) 0
      (addr + 4) (WordCodec.u32le.serialize [value]) hlen2 (by omega)
    rw [hdec2] at hword
    exact hword

/-- Focus the pair slot at a byte offset of a slice, for a write.  The
continuation gives the slice back with the new pair in place. -/
theorem slot_storeFocus [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (pos : Nat) (key value : UInt32)
    (hfit : pos + 8 ≤ bytes.length)
    (hnowrap : ptr.toNat + bytes.length < UInt32.size) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(pointsTo_u32 0 (ptr + UInt32.ofNat pos)
          (WordCodec.decodeU32 ((bytes.drop pos).take 4)) ∗
        pointsTo_u32 0 (ptr + UInt32.ofNat pos + 4)
          (WordCodec.decodeU32 ((bytes.drop (pos + 4)).take 4)) ∗
        (pointsTo_u32 0 (ptr + UInt32.ofNat pos) key -∗
          pointsTo_u32 0 (ptr + UInt32.ofNat pos + 4) value -∗
          Slices.ByteSlice 0 ptr
            (bytes.take pos ++ WordCodec.u32le.serialize [key, value] ++
              bytes.drop (pos + 8)))) := by
  have hslotNat : (ptr + UInt32.ofNat pos).toNat = ptr.toNat + pos :=
    Slices.byteOffset_toNat ptr pos (by omega)
  have hprefixLength : (bytes.take pos).length = pos := by
    rw [List.length_take]; omega
  have hmidLength : (WordCodec.u32le.serialize [key, value]).length = 8 := by
    simp
  have hstep : ptr + UInt32.ofNat pos + UInt32.ofNat 8
      = ptr + UInt32.ofNat pos + 8 := rfl
  iintro Hslice
  ihave ⟨Hprefix, Hkey, Hvalue, Hsuffix⟩ :=
    (input_pairFocus ptr bytes pos hfit hnowrap).mp $$ Hslice
  isplitl_exact Hkey
  · isplitl_exact Hvalue
    · iintro Hnewkey
      iintro Hnewvalue
      ihave Hmid := (pair_words (ptr + UInt32.ofNat pos) key value
        (by omega)).mpr $$ [Hnewkey Hnewvalue]
      · isplitl_exact Hnewkey
        · iexact Hnewvalue
      ihave Htail := (Slices.ByteSlice_append 0 (ptr + UInt32.ofNat pos)
        (WordCodec.u32le.serialize [key, value])
        (bytes.drop (pos + 8))).mpr $$ [Hmid Hsuffix]
      · rw [hmidLength, hstep]
        isplitl_exact Hmid
        · iexact Hsuffix
      rw [List.append_assoc]
      iapply (Slices.ByteSlice_append 0 ptr (bytes.take pos)
        (WordCodec.u32le.serialize [key, value] ++
          bytes.drop (pos + 8))).mpr
      rw [hprefixLength]
      isplitl_exact Hprefix
      · iexact Htail

/-! ## The append -/

set_option maxHeartbeats 2000000 in
/-- The append writes the pair into the live block and raises the length
word of the vector. -/
theorem twp_append_pair [WasmSmallStepGS hlc Universal.State]
    (out hdr frame buffer capacity key value oldCount : UInt32)
    (index allocationId : Nat) (heapId : GName) (allBytes : List UInt8)
    (l4 l5 l6 l7 l11 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hindex : index < capacity.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      LiveBlock heapId allocationId buffer (pairBlock capacity.toNat)
        allBytes ∗
      pointsTo_u32 0 (frame + 12) oldCount ∗
      (LiveBlock heapId allocationId buffer (pairBlock capacity.toNat)
          (allBytes.take (8 * index) ++
            WordCodec.u32le.serialize [key, value] ++
            allBytes.drop (8 * index + 8)) -∗
        pointsTo_u32 0 (frame + 12) (UInt32.ofNat (index + 1)) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 (UInt32.ofNat (index + 1)), l4, l5, l6, l7,
                  .i32 buffer, .i32 (UInt32.ofNat (8 * (index + 1) + 4)),
                  .i32 key, .i32 (buffer + UInt32.ofNat (8 * index) + 4),
                  .i32 value],
              stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 (UInt32.ofNat index), l4, l5, l6, l7,
                .i32 buffer, .i32 (UInt32.ofNat (8 * index + 4)), .i32 key,
                l11, .i32 value],
            stack⟩,
            appendStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  rw [ofNat_offset_step index, ofNat_succ_word index]
  iintro ⟨Hblock, Hcount, Hcont⟩
  ihave ⟨Htoken, Hbytes, %hfacts⟩ :=
    (LiveBlock_open heapId allocationId buffer (pairBlock capacity.toNat)
      allBytes).mp $$ Hblock
  ihave ⟨Hbytes, %hnowrap⟩ := ByteSlice_bound buffer allBytes $$ Hbytes
  have hsize : allBytes.length = 8 * capacity.toNat := hfacts.1
  have hfit : 8 * index + 8 ≤ allBytes.length := by omega
  have hslotNat : (buffer + UInt32.ofNat (8 * index)).toNat
      = buffer.toNat + 8 * index :=
    Slices.byteOffset_toNat buffer (8 * index) (by omega)
  have haddr : UInt32.ofNat (8 * index + 4) + buffer
      = buffer + UInt32.ofNat (8 * index) + 4 := by
    rw [UInt32.add_comm, addr_shift4]
  have hnewLength : (allBytes.take (8 * index) ++
      WordCodec.u32le.serialize [key, value] ++
      allBytes.drop (8 * index + 8)).length
        = (pairBlock capacity.toNat).size := by
    have hmid : (WordCodec.u32le.serialize [key, value]).length = 8 := by
      simp
    simp only [List.length_append, List.length_take, List.length_drop, hmid,
      pairBlock]
    omega
  ihave ⟨Hkey, Hvalue, Hclose⟩ := slot_storeFocus buffer allBytes
    (8 * index) key value hfit hnowrap $$ Hbytes
  iapply twp_append_stores out hdr frame buffer
    (UInt32.ofNat (8 * index + 4)) (buffer + UInt32.ofNat (8 * index))
    key value (UInt32.ofNat index)
    (WordCodec.decodeU32 ((allBytes.drop (8 * index)).take 4))
    (WordCodec.decodeU32 ((allBytes.drop (8 * index + 4)).take 4))
    oldCount l4 l5 l6 l7 l11 haddr (by omega) hframeNowrap
  isplitl_exacts [Hkey Hvalue Hcount]
  iintro Hkey Hvalue Hcount
  ihave Hbytes := Hclose $$ Hkey Hvalue
  ihave Hblock := (LiveBlock_open heapId allocationId buffer
      (pairBlock capacity.toNat)
      (allBytes.take (8 * index) ++
        WordCodec.u32le.serialize [key, value] ++
        allBytes.drop (8 * index + 8))).mpr $$ [Htoken Hbytes]
  · isplitl_exact Htoken
    · isplitl_exact Hbytes
      · ipureexact ⟨hnewLength, hfacts.2.1, hfacts.2.2⟩
  iapply Hcont $$ Hblock Hcount

end Project.RustHashMap.Decoder
