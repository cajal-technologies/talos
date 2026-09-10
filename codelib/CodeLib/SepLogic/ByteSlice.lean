import CodeLib.SepLogic.WasmHeap
import CodeLib.WordCodec.UInt32

/-!
# Byte slices and word slices

Exclusive ownership of one non-wrapping byte range, and the same range seen
as an array of little-endian `u32` words.  `ByteSlice` packs `pointsToBytes`
with the fact that the range does not wrap around the address space.
`WordSlice` adds four-byte alignment and packs the bytes as
`WordCodec.u32le.serialize values`.  `WordCells` is the byte view of a word
list without those two facts.

The lemmas do three things:

* split and join a slice at a list boundary (`ByteSlice_append`,
  `WordSlice_append`);
* move between the byte view, the single-word view, and the word-array view
  (`ByteSlice_four_as_word`, `ByteSlice_serialize_as_WordSlice`,
  `ByteSlice_as_decodedWordSlice`, `arrayAt_eq_wordCells`);
* focus one word cell for a load or a store and get the slice back
  (`ByteSlice_storeWordFocus`, `WordSlice_get`, `WordSlice_set`).

Every definition and theorem is a port of the same-named item in
`Project.Mergesort.Representations`, which fixes memory `0` and its own copy
of the `u32` codec (`Project.Mergesort.Spec.u32Codec`).  This module takes
the memory index as an argument and uses `WordCodec.u32le`.  The two codecs
have the same `encode` and `decode` bodies, so the byte-level proofs
(`encodeU32_eq_u32Bytes`, `encodeU32_decodeU32_of_length`) are the same
proofs.  A follow-up can point `Project.Mergesort.Representations` at this
module; this module does not change that file.

The definitions live in the namespace `Wasm.SepLogic.Slices`, not in
`Wasm.SepLogic`.  The mergesort proofs open `Wasm.SepLogic` together with
`Project.Mergesort.Representations` and use the names above without a
prefix.  A second `WordSlice` in `Wasm.SepLogic` would make those names
ambiguous.  The sub-namespace keeps the original names and keeps the
mergesort files unchanged.

The module stays at the list level: `append`, `cons`, and `arrayAt`.  It does
not state byte-window focus lemmas over `take` and `drop`.

Consumer: `CodeLib.SepLogic.BorshSlice`, which states the borsh layouts of
`CodeLib.RustStd.Borsh` as slices.
-/

namespace Wasm.WordCodec

variable {W : Type}

/-- Packed serialization splits at a list boundary. -/
theorem serialize_append (codec : WordCodec W) (xs ys : List W) :
    codec.serialize (xs ++ ys) = codec.serialize xs ++ codec.serialize ys := by
  simp [serialize]

@[simp] theorem u32le_width : u32le.width = 4 := rfl

@[simp] theorem u32le_serialize_length (values : List UInt32) :
    (u32le.serialize values).length = 4 * values.length := by
  rw [serialize_length]; rfl

end Wasm.WordCodec

namespace Wasm.SepLogic.Slices

open Iris Std

/-! ## The `u32le` codec and the byte primitive -/

/-- The bytes that `WordCodec.u32le` writes are the bytes that `pointsTo_u32`
owns. -/
theorem encodeU32_eq_u32Bytes (value : UInt32) :
    WordCodec.encodeU32 value =
      [u32Byte value 0, u32Byte value 1, u32Byte value 2, u32Byte value 3] := by
  rfl

/-- Every four-byte list is the encoding of the word that `decodeU32` reads
from it. -/
theorem encodeU32_decodeU32_of_length
    (bytes : List UInt8) (hlength : bytes.length = 4) :
    WordCodec.encodeU32 (WordCodec.decodeU32 bytes) = bytes := by
  rcases bytes with _ | ⟨b0, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨b1, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨b2, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨b3, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨extra, bytes⟩
  · simp only [WordCodec.encodeU32, WordCodec.decodeU32]
    rw [UInt32.packBytes_byte0, UInt32.packBytes_byte1,
      UInt32.packBytes_byte2, UInt32.packBytes_byte3]
  · simp at hlength

/-- The word view of a byte list made of complete four-byte chunks.  A
trailing partial chunk is dropped.  Callers use
`u32le_serialize_decodeWords_of_length`, which needs an exact length, so the
partial case never describes a live allocation. -/
def decodeWords : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest =>
      WordCodec.decodeU32 [b0, b1, b2, b3] :: decodeWords rest
  | _ => []

/-- Every `4 * count`-byte list is the serialization of its `count`-word
view. -/
theorem u32le_serialize_decodeWords_of_length (bytes : List UInt8) (count : Nat)
    (hlength : bytes.length = 4 * count) :
    WordCodec.u32le.serialize (decodeWords bytes) = bytes ∧
      (decodeWords bytes).length = count := by
  induction count generalizing bytes with
  | zero =>
      have : bytes = [] := by simpa using hlength
      subst bytes
      simp [decodeWords]
  | succ count ih =>
      rcases bytes with _ | ⟨b0, bytes⟩
      · simp at hlength
      rcases bytes with _ | ⟨b1, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b2, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b3, rest⟩
      · simp at hlength; omega
      have hrest : rest.length = 4 * count := by
        simp only [List.length_cons, Nat.mul_succ] at hlength; omega
      have hind := ih rest hrest
      constructor
      · change WordCodec.u32le.serialize
          (WordCodec.decodeU32 [b0, b1, b2, b3] :: decodeWords rest) =
            b0 :: b1 :: b2 :: b3 :: rest
        rw [WordCodec.serialize_cons]
        change WordCodec.encodeU32 (WordCodec.decodeU32 [b0, b1, b2, b3]) ++
            WordCodec.u32le.serialize (decodeWords rest) = _
        rw [encodeU32_decodeU32_of_length [b0, b1, b2, b3] (by simp), hind.1]
        simp
      · change (WordCodec.decodeU32 [b0, b1, b2, b3] ::
          decodeWords rest).length = count + 1
        simp [hind.2]

/-! ## Offsets that do not wrap -/

/-- A byte offset inside a non-wrapping range has the expected address. -/
theorem byteOffset_toNat (ptr : UInt32) (count : Nat)
    (h : ptr.toNat + count < UInt32.size) :
    (ptr + UInt32.ofNat count).toNat = ptr.toNat + count :=
  UInt32.add_ofNat_toNat_noWrap ptr count
    (by simpa only [UInt32.size] using (show count < UInt32.size by omega))
    (by simpa only [UInt32.size] using h)

/-- A word offset inside a non-wrapping range has the expected address. -/
theorem wordOffset_toNat (ptr : UInt32) (count : Nat)
    (h : ptr.toNat + 4 * count < UInt32.size) :
    (ptr + 4 * UInt32.ofNat count).toNat = ptr.toNat + 4 * count := by
  have hprod : 4 * UInt32.ofNat count = UInt32.ofNat (4 * count) := by
    rw [UInt32.ofNat_mul]; rfl
  rw [hprod]
  exact byteOffset_toNat ptr (4 * count) h

private theorem wordOffset_eq_byteOffset
    (ptr : UInt32) (values : List UInt32) :
    ptr + 4 * UInt32.ofNat values.length =
      ptr + UInt32.ofNat (WordCodec.u32le.serialize values).length := by
  simp only [WordCodec.u32le_serialize_length]
  rw [UInt32.ofNat_mul]; rfl

section Ownership

variable {α : Type} [WasmHeapGS α]

/-! ## Byte slices -/

/-- Exclusive ownership of one initialized byte range that does not wrap
around the address space.  In-bounds facts about the physical memory come
from `stateInterp`; this predicate does not repeat them. -/
def ByteSlice (memId : Nat) (ptr : UInt32) (bytes : List UInt8) :
    IProp (WasmHeapGF α) :=
  iprop(⌜ptr.toNat + bytes.length < UInt32.size⌝ ∗
    pointsToBytes memId ptr bytes)

/-- Split a byte slice at a list boundary, and join two adjacent slices. -/
theorem ByteSlice_append (memId : Nat) (ptr : UInt32)
    (left right : List UInt8) :
    ByteSlice (α := α) memId ptr (left ++ right) ⊣⊢
      iprop(ByteSlice memId ptr left ∗
        ByteSlice memId (ptr + UInt32.ofNat left.length) right) := by
  unfold ByteSlice
  simp only [List.length_append]
  constructor
  · iintro ⟨%hnowrap, Hbytes⟩
    icases (pointsToBytes_append memId ptr left right).mp $$ Hbytes with
      ⟨Hleft, Hright⟩
    have hleftNowrap :
        ptr.toNat + left.length < UInt32.size := by omega
    have hoffset := byteOffset_toNat ptr left.length hleftNowrap
    have hrightNowrap :
        (ptr + UInt32.ofNat left.length).toNat + right.length <
          UInt32.size := by omega
    isplitl [Hleft]
    · iframe Hleft
      ipureexact hleftNowrap
    · iframe Hright
      ipureexact hrightNowrap
  · iintro ⟨⟨%hleftNowrap, Hleft⟩,
        ⟨%hrightNowrap, Hright⟩⟩
    have hoffset := byteOffset_toNat ptr left.length hleftNowrap
    have hnowrap :
        ptr.toNat + (left.length + right.length) < UInt32.size := by
      rw [hoffset] at hrightNowrap; omega
    isplitl_pureexact hnowrap
    · iapply_frame (pointsToBytes_append memId ptr left right).mpr

/-- Exclusive ownership of a byte range whose current contents have no
meaning. -/
def OwnedRegion (memId : Nat) (ptr : UInt32) (size : Nat) :
    IProp (WasmHeapGF α) :=
  iprop(∃ bytes : List UInt8, ⌜bytes.length = size⌝ ∗ ByteSlice memId ptr bytes)

/-! ## Word slices -/

/-- The bytes of a little-endian word list, without the alignment and
no-wrap facts that `WordSlice` packs. -/
abbrev WordCells (memId : Nat) (ptr : UInt32) (values : List UInt32) :
    IProp (WasmHeapGF α) :=
  pointsToBytes memId ptr (WordCodec.u32le.serialize values)

/-- Four-aligned, initialized, non-wrapping ownership of a word array. -/
def WordSlice (memId : Nat) (ptr : UInt32) (values : List UInt32) :
    IProp (WasmHeapGF α) :=
  iprop(⌜ptr.toNat % 4 = 0⌝ ∗
    ByteSlice memId ptr (WordCodec.u32le.serialize values))

/-- At an aligned address, the byte view and the word-array view of a
serialized word list are the same ownership. -/
theorem ByteSlice_serialize_as_WordSlice (memId : Nat) (ptr : UInt32)
    (values : List UInt32) (halign : ptr.toNat % 4 = 0) :
    ByteSlice (α := α) memId ptr (WordCodec.u32le.serialize values) ⊣⊢
      WordSlice memId ptr values := by
  unfold WordSlice
  constructor
  · iintro Hbytes
    isplitl_pureexact halign
    · iexact Hbytes
  · iintro ⟨%_halign, Hbytes⟩
    iexact Hbytes

/-- An aligned `4 * count`-byte slice is a `count`-word slice.  The theorem
adds no initialization assumption: the words are the decoded bytes. -/
theorem ByteSlice_as_decodedWordSlice (memId : Nat) (ptr : UInt32)
    (bytes : List UInt8) (count : Nat)
    (halign : ptr.toNat % 4 = 0)
    (hlength : bytes.length = 4 * count) :
    ByteSlice (α := α) memId ptr bytes ⊣⊢
      WordSlice memId ptr (decodeWords bytes) := by
  have hdecode := u32le_serialize_decodeWords_of_length bytes count hlength
  have hslice :
      ByteSlice (α := α) memId ptr
          (WordCodec.u32le.serialize (decodeWords bytes)) =
        ByteSlice memId ptr bytes :=
    congrArg (fun concrete => ByteSlice (α := α) memId ptr concrete) hdecode.1
  constructor
  · iintro Hbytes
    ihave Hencoded :
        ByteSlice memId ptr (WordCodec.u32le.serialize (decodeWords bytes))
        $$ [Hbytes]
    · irw_exact [hslice] with Hbytes
    iapply (ByteSlice_serialize_as_WordSlice memId ptr
      (decodeWords bytes) halign).mp
    iexact Hencoded
  · iintro Hwords
    ihave Hencoded := (ByteSlice_serialize_as_WordSlice memId ptr
      (decodeWords bytes) halign).mpr $$ Hwords
    ihave Hbytes : ByteSlice memId ptr bytes $$ [Hencoded]
    · irw_exact [← hslice] with Hencoded
    iexact Hbytes

/-- At a non-wrapping four-byte slot, the byte view and the single-word view
are the same ownership. -/
theorem ByteSlice_four_as_word (memId : Nat) (ptr : UInt32)
    (bytes : List UInt8)
    (hlength : bytes.length = 4)
    (hnowrap : ptr.toNat + 4 < UInt32.size) :
    ByteSlice (α := α) memId ptr bytes ⊣⊢
      pointsTo_u32 memId ptr (WordCodec.decodeU32 bytes) := by
  let word := WordCodec.decodeU32 bytes
  have hencoded :
      [u32Byte word 0, u32Byte word 1, u32Byte word 2, u32Byte word 3] =
        bytes := by
    rw [← encodeU32_eq_u32Bytes]; exact encodeU32_decodeU32_of_length bytes hlength
  constructor
  · iintro Hslice
    isimp only [ByteSlice] at Hslice
    icases Hslice with ⟨%_hsliceNowrap, Hbytes⟩
    iapply (pointsTo_u32_as_bytes memId ptr word).mpr
    irw_exact [hencoded] with Hbytes
  · iintro Hword
    unfold ByteSlice
    isplitl_pureexact (by simpa [hlength] using hnowrap)
    · ihave Hbytes := (pointsTo_u32_as_bytes memId ptr word).mp $$ Hword
      ihave Hbytes' : pointsToBytes memId ptr bytes $$ [Hbytes]
      · irw_exact [← hencoded] with Hbytes
      iexact Hbytes'

/-- Focus a four-byte slice for a word store of any value.  The continuation
returns the slice as the serialization of the new word. -/
theorem ByteSlice_storeAnyWordFocus (memId : Nat) (ptr : UInt32)
    (oldBytes : List UInt8)
    (hlength : oldBytes.length = 4)
    (hnowrap : ptr.toNat + 4 < UInt32.size) :
    ByteSlice (α := α) memId ptr oldBytes ⊢
      iprop(pointsTo_u32 memId ptr (WordCodec.decodeU32 oldBytes) ∗
        (∀ newValue : UInt32, pointsTo_u32 memId ptr newValue -∗
          ByteSlice memId ptr (WordCodec.u32le.serialize [newValue]))) := by
  iintro Hslice
  ihave Hold := (ByteSlice_four_as_word memId ptr oldBytes hlength hnowrap).mp $$
    Hslice
  isplitl_exact Hold
  · iintro %newValue
    iintro Hnew
    have hnewLength : (WordCodec.u32le.serialize [newValue]).length = 4 := by
      simp
    have hdecode :
        WordCodec.decodeU32 (WordCodec.u32le.serialize [newValue]) = newValue := by
      change WordCodec.decodeU32 (WordCodec.encodeU32 newValue) = newValue
      exact WordCodec.u32le.decode_encode newValue
    iapply (ByteSlice_four_as_word memId ptr (WordCodec.u32le.serialize [newValue])
      hnewLength hnowrap).mpr
    irw_exact [hdecode] with Hnew

/-- Focus a four-byte slice for one word store of a known value. -/
theorem ByteSlice_storeWordFocus (memId : Nat) (ptr : UInt32)
    (oldBytes : List UInt8) (newValue : UInt32)
    (hlength : oldBytes.length = 4)
    (hnowrap : ptr.toNat + 4 < UInt32.size) :
    ByteSlice (α := α) memId ptr oldBytes ⊢
      iprop(pointsTo_u32 memId ptr (WordCodec.decodeU32 oldBytes) ∗
        (pointsTo_u32 memId ptr newValue -∗
          ByteSlice memId ptr (WordCodec.u32le.serialize [newValue]))) := by
  iintro Hslice
  ihave ⟨Hold, Hclose⟩ := ByteSlice_storeAnyWordFocus memId ptr oldBytes
    hlength hnowrap $$ Hslice
  isplitl_exact Hold
  ispecialize Hclose $$ %newValue
  iexact Hclose

/-- The empty word slice owns nothing.  This is the dangling-pointer case
that a driver takes when the input is empty. -/
theorem WordSlice_nil (memId : Nat) (ptr : UInt32) (halign : ptr.toNat % 4 = 0) :
    emp ⊢ WordSlice (α := α) memId ptr [] := by
  iintro _Hemp
  unfold WordSlice ByteSlice
  isplitl_pureexact halign
  isplitl_pureexact (by simpa [UInt32.size] using ptr.toBitVec.isLt)
  · isimp only [WordCodec.serialize_nil]
    iapply (pointsToBytes_nil memId ptr).mpr
    itrivial

/-- Split a word slice at a list boundary, and join two adjacent word
slices.  The right part starts at `ptr + 4 * count`. -/
theorem WordSlice_append (memId : Nat) (ptr : UInt32) (xs ys : List UInt32) :
    WordSlice (α := α) memId ptr (xs ++ ys) ⊣⊢
      iprop(WordSlice memId ptr xs ∗
        WordSlice memId (ptr + 4 * UInt32.ofNat xs.length) ys) := by
  unfold WordSlice ByteSlice
  simp only [WordCodec.serialize_append, List.length_append,
    WordCodec.u32le_serialize_length]
  constructor
  · iintro ⟨%halign, %hnowrap, Hbytes⟩
    icases (pointsToBytes_append memId ptr (WordCodec.u32le.serialize xs)
      (WordCodec.u32le.serialize ys)).mp $$ Hbytes with ⟨Hleft, Hright⟩
    have hleftNowrap :
        ptr.toNat + 4 * xs.length < UInt32.size := by omega
    have hoffset := wordOffset_toNat ptr xs.length hleftNowrap
    have hrightNowrap :
        (ptr + 4 * UInt32.ofNat xs.length).toNat +
            4 * ys.length < UInt32.size := by omega
    have hrightAlign :
        (ptr + 4 * UInt32.ofNat xs.length).toNat % 4 = 0 := by
      rw [hoffset, Nat.add_mod]; omega
    ihave Hright' :
        pointsToBytes memId (ptr + 4 * UInt32.ofNat xs.length)
          (WordCodec.u32le.serialize ys) $$ [Hright]
    · irw_exact [wordOffset_eq_byteOffset] with Hright
    isplitl [Hleft]
    · iframe Hleft
      ipureexact ⟨halign, hleftNowrap⟩
    · iframe Hright'
      ipureexact ⟨hrightAlign, hrightNowrap⟩
  · iintro ⟨⟨%halign, %hleftNowrap, Hleft⟩,
        ⟨%_hrightAlign, %hrightNowrap, Hright⟩⟩
    have hoffset := wordOffset_toNat ptr xs.length hleftNowrap
    have hnowrap :
        ptr.toNat + 4 * (xs.length + ys.length) < UInt32.size := by
      rw [hoffset] at hrightNowrap; omega
    isplitl_pureexact halign
    isplitl_pureexact (by simpa only [Nat.mul_add] using hnowrap)
    iapply_splitl_exact (pointsToBytes_append memId ptr
      (WordCodec.u32le.serialize xs) (WordCodec.u32le.serialize ys)).mpr with Hleft
    · irw_exact [← wordOffset_eq_byteOffset] with Hright

/-- Keep a word slice and expose its alignment and no-wrap facts. -/
theorem WordSlice_facts (memId : Nat) (ptr : UInt32) (values : List UInt32) :
    WordSlice (α := α) memId ptr values ⊢
      iprop(WordSlice memId ptr values ∗
        ⌜ptr.toNat % 4 = 0 ∧
          ptr.toNat + 4 * values.length < UInt32.size⌝) := by
  unfold WordSlice ByteSlice
  iintro ⟨%halign, %hnowrap, Hbytes⟩
  isplitl [Hbytes]
  · iframe Hbytes
    ipureexact ⟨halign, hnowrap⟩
  · ipureexact ⟨halign,
      by simpa only [WordCodec.u32le_serialize_length] using hnowrap⟩

/-- `arrayAt` and the `u32le` serialization describe the same bytes. -/
theorem arrayAt_eq_wordCells (memId : Nat) (ptr : UInt32) (values : List UInt32) :
    arrayAt (α := α) memId ptr values ⊣⊢ WordCells memId ptr values := by
  induction values generalizing ptr with
  | nil => exact .rfl
  | cons value rest ih =>
      simp only [arrayAt, WordCells, WordCodec.serialize_cons]
      change pointsTo_u32 memId ptr value ∗ arrayAt memId (ptr + 4) rest ⊣⊢
        pointsToBytes memId ptr
          (WordCodec.encodeU32 value ++ WordCodec.u32le.serialize rest)
      rw [encodeU32_eq_u32Bytes]; exact (BI.sep_congr
          (pointsTo_u32_as_bytes memId ptr value)
          (by simpa using ih (ptr + 4))).trans
        (pointsToBytes_append memId ptr
          [u32Byte value 0, u32Byte value 1,
            u32Byte value 2, u32Byte value 3]
          (WordCodec.u32le.serialize rest)).symm

/-- Focus one word cell for a load.  The continuation returns the same word
slice.  The index premise is the bounds check of the generated code. -/
theorem WordSlice_get (memId : Nat) (ptr : UInt32) (values : List UInt32)
    (k : Nat) (hk : k < values.length) :
    WordSlice (α := α) memId ptr values ⊢
      iprop(pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) values[k] ∗
        (pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) values[k] -∗
          WordSlice memId ptr values)) := by
  unfold WordSlice ByteSlice
  iintro ⟨%halign, %hnowrap, Hbytes⟩
  ihave Harray : arrayAt memId ptr values $$ [Hbytes]
  · iapply_exact (arrayAt_eq_wordCells memId ptr values).mpr with Hbytes
  ihave ⟨Hcell, Hclose⟩ := arrayAt_get memId ptr values k hk $$ Harray
  isplitl_exact Hcell
  · iintro Hcell
    ihave Harray := Hclose $$ Hcell
    ihave Hbytes : WordCells memId ptr values $$ [Harray]
    · iapply_exact (arrayAt_eq_wordCells memId ptr values).mp with Harray
    iframe_pureexact using [Hbytes] => ⟨halign, hnowrap⟩

/-- Focus one word cell for a store.  The continuation returns the word slice
with the list updated at the same index. -/
theorem WordSlice_set (memId : Nat) (ptr : UInt32) (values : List UInt32)
    (k : Nat) (newValue : UInt32) (hk : k < values.length) :
    WordSlice (α := α) memId ptr values ⊢
      iprop(pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) values[k] ∗
        (pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) newValue -∗
          WordSlice memId ptr (values.set k newValue))) := by
  unfold WordSlice ByteSlice
  iintro ⟨%halign, %hnowrap, Hbytes⟩
  ihave Harray : arrayAt memId ptr values $$ [Hbytes]
  · iapply_exact (arrayAt_eq_wordCells memId ptr values).mpr with Hbytes
  ihave ⟨Hcell, Hclose⟩ := arrayAt_set memId ptr values k newValue hk $$ Harray
  isplitl_exact Hcell
  · iintro Hcell
    ihave Harray := Hclose $$ Hcell
    ihave Hbytes : WordCells memId ptr (values.set k newValue) $$ [Harray]
    · iapply_exact (arrayAt_eq_wordCells memId ptr (values.set k newValue)).mp
        with Harray
    iframe Hbytes
    ipureintro
    refine ⟨halign, ?_⟩
    simpa using hnowrap

end Ownership

end Wasm.SepLogic.Slices
