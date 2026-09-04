import Project.Mergesort.Spec
import CodeLib.RustStd.Region
import CodeLib.SepLogic.SmallStepState

/-!
# Canonical logical representations for generated merge-sort

The allocator predicates in this file are tied to the authoritative sparse
heap frontier in `stateInterp`.  In particular, allocation history is not used
as a substitute for freshness: fresh byte ownership is created only by
`stateInterp_alloc_freshRange`.
-/

namespace Project.Mergesort.Representations

open Wasm
open Iris
open Std
open Wasm.SepLogic Wasm.SmallStep

/-! ## Canonical codec -/

/-- The sole word codec used by public streams and internal word arrays. -/
abbrev U32Codec : WordCodec UInt32 := Spec.u32Codec

/-- Canonical packed little-endian serialization. -/
abbrev serialize (values : List UInt32) : List UInt8 :=
  U32Codec.serialize values

/-- The public semantic result relation, reused unchanged by internal specs. -/
abbrev SortedPermutation (input output : List UInt32) : Prop :=
  Spec.SortedPermutation input output

@[simp] theorem serialize_length (values : List UInt32) :
    (serialize values).length = 4 * values.length := by
  exact U32Codec.serialize_length values

@[simp] theorem serialize_append (xs ys : List UInt32) :
    serialize (xs ++ ys) = serialize xs ++ serialize ys := by
  unfold serialize U32Codec WordCodec.serialize
  simp

@[simp] theorem deserialize_serialize (values : List UInt32) :
    U32Codec.deserialize (serialize values) = some values := by
  exact U32Codec.deserialize_serialize values

/-- A zeroed four-byte allocation is exactly the canonical serialization of
the corresponding zero-valued word array. -/
@[simp] theorem serialize_replicate_zero (count : Nat) :
    serialize (List.replicate count 0) =
      List.replicate (4 * count) 0 := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ, Nat.mul_succ]
      change U32Codec.serialize (0 :: List.replicate count 0) =
        List.replicate (4 * count + 4) 0
      rw [Wasm.WordCodec.serialize_cons]
      change Spec.encodeWord 0 ++ serialize (List.replicate count 0) =
        List.replicate (4 * count + 4) 0
      rw [ih, show 4 * count + 4 = 4 + 4 * count by omega,
        List.replicate_add]
      rfl

/-- The byte footprint used by the separation-logic word primitive is the
canonical stream encoding, not a second serializer. -/
theorem encodeWord_eq_u32Bytes (value : UInt32) :
    Spec.encodeWord value =
        [u32Byte value 0, u32Byte value 1,
        u32Byte value 2, u32Byte value 3] := by
  rfl

/-- Every exact four-byte sequence is the canonical encoding of the word
obtained by the generated little-endian decoder. -/
theorem encodeWord_decodeWord_of_length
    (bytes : List UInt8) (hlength : bytes.length = 4) :
    Spec.encodeWord (Spec.decodeWord bytes) = bytes := by
  rcases bytes with _ | ⟨b0, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨b1, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨b2, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨b3, bytes⟩
  · simp at hlength
  rcases bytes with _ | ⟨extra, bytes⟩
  · simp [Spec.encodeWord, Spec.decodeWord]
    bv_decide
  · simp at hlength

/-- Deterministic word view of an arbitrary complete four-byte-chunk list.
Trailing partial chunks are discarded; callers use the exact-length theorem
below, so that case is never used for a live word allocation. -/
def decodeWords : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest =>
      Spec.decodeWord [b0, b1, b2, b3] :: decodeWords rest
  | _ => []

/-- Every concrete `4*n`-byte allocation has a canonical `n`-word view. -/
theorem serialize_decodeWords_of_length (bytes : List UInt8) (count : Nat)
    (hlength : bytes.length = 4 * count) :
    serialize (decodeWords bytes) = bytes ∧
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
      · simp at hlength
        omega
      rcases bytes with _ | ⟨b2, bytes⟩
      · simp at hlength
        omega
      rcases bytes with _ | ⟨b3, rest⟩
      · simp at hlength
        omega
      have hrest : rest.length = 4 * count := by
        simp only [List.length_cons, Nat.mul_succ] at hlength
        omega
      have hind := ih rest hrest
      constructor
      · change U32Codec.serialize
          (Spec.decodeWord [b0, b1, b2, b3] :: decodeWords rest) =
            b0 :: b1 :: b2 :: b3 :: rest
        rw [Wasm.WordCodec.serialize_cons]
        change Spec.encodeWord (Spec.decodeWord [b0, b1, b2, b3]) ++
            serialize (decodeWords rest) = _
        rw [encodeWord_decodeWord_of_length [b0, b1, b2, b3]
          (by simp), hind.1]
        simp
      · change (Spec.decodeWord [b0, b1, b2, b3] ::
          decodeWords rest).length = count + 1
        simp [hind.2]

/-- Logical destination contents after the decode loop has overwritten the
first `copied` words of an arbitrary fresh allocation. -/
def overwritePrefix (source initial : List UInt32) (copied : Nat) :
    List UInt32 :=
  source.take copied ++ initial.drop copied

@[simp] theorem overwritePrefix_zero (source initial : List UInt32) :
    overwritePrefix source initial 0 = initial := by
  simp [overwritePrefix]

theorem overwritePrefix_length (source initial : List UInt32) (copied : Nat)
    (hlength : source.length = initial.length) :
    (overwritePrefix source initial copied).length = source.length := by
  simp [overwritePrefix, hlength]
  omega

/-- One generated decode store advances the exact logical prefix by one word.
The unrolled loop applies this law four times per iteration. -/
theorem overwritePrefix_set_next (source initial : List UInt32) (copied : Nat)
    (hlength : source.length = initial.length)
    (hcopied : copied < source.length) :
    (overwritePrefix source initial copied).set copied source[copied] =
      overwritePrefix source initial (copied + 1) := by
  induction source generalizing initial copied with
  | nil => simp at hcopied
  | cons head source ih =>
      cases initial with
      | nil => simp at hlength
      | cons old initial =>
          cases copied with
          | zero => simp [overwritePrefix]
          | succ copied =>
              have hlength' : source.length = initial.length := by
                simp at hlength
                exact hlength
              have hcopied' : copied < source.length := by
                simp at hcopied
                exact hcopied
              change
                (head :: overwritePrefix source initial copied).set
                    (Nat.succ copied) source[copied] =
                  head :: overwritePrefix source initial (copied + 1)
              simp only [List.set]
              rw [ih initial copied hlength' hcopied']

@[simp] theorem overwritePrefix_all (source initial : List UInt32)
    (hlength : source.length = initial.length) :
    overwritePrefix source initial source.length = source := by
  simp [overwritePrefix, hlength]

/-! ## Byte and word regions -/

/-- Exclusive initialized ownership of one non-wrapping memory-0 byte range.
Physical in-bounds facts are obtained by combining this ownership with
`stateInterp`; they are not duplicated as an uncoupled pure assertion. -/
def ByteSlice {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (bytes : List UInt8) : IProp (WasmHeapGF host) :=
  iprop(⌜ptr.toNat + bytes.length < UInt32.size⌝ ∗
    pointsToBytes 0 ptr bytes)

/-- A non-wrapping logical byte offset has the expected natural-number
address. -/
theorem byteOffset_toNat (ptr : UInt32) (count : Nat)
    (h : ptr.toNat + count < UInt32.size) :
    (ptr + UInt32.ofNat count).toNat = ptr.toNat + count := by
  have hcount : count < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hcount]
  change (ptr.toNat + count) % 2 ^ 32 = ptr.toNat + count
  rw [Nat.mod_eq_of_lt]
  norm_num [UInt32.size] at h ⊢
  exact h

/-- Split and recombine canonical byte ownership at a logical list boundary. -/
theorem ByteSlice_append {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (left right : List UInt8) :
    ByteSlice (host := host) ptr (left ++ right) ⊣⊢
      iprop(ByteSlice ptr left ∗
        ByteSlice (ptr + UInt32.ofNat left.length) right) := by
  unfold ByteSlice
  simp only [List.length_append]
  constructor
  · iintro ⟨%hnowrap, Hbytes⟩
    icases (pointsToBytes_append 0 ptr left right).mp $$ Hbytes with
      ⟨Hleft, Hright⟩
    have hleftNowrap :
        ptr.toNat + left.length < UInt32.size := by omega
    have hoffset := byteOffset_toNat ptr left.length hleftNowrap
    have hrightNowrap :
        (ptr + UInt32.ofNat left.length).toNat + right.length <
          UInt32.size := by
      rw [hoffset]
      omega
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
      rw [hoffset] at hrightNowrap
      omega
    isplitl_pureexact hnowrap
    · iapply_frame (pointsToBytes_append 0 ptr left right).mpr

/-- Exclusive ownership of a region whose current contents have no semantic
role. -/
def OwnedRegion {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (size : Nat) : IProp (WasmHeapGF host) :=
  iprop(∃ bytes : List UInt8, ⌜bytes.length = size⌝ ∗ ByteSlice ptr bytes)

/-- Canonical byte ownership of a list of little-endian words, without the
layout facts packaged by `WordSlice`. -/
abbrev WordCells {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32) : IProp (WasmHeapGF host) :=
  pointsToBytes 0 ptr (serialize values)

/-- Four-aligned, initialized, non-wrapping ownership of a word array. -/
def WordSlice {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32) : IProp (WasmHeapGF host) :=
  iprop(⌜ptr.toNat % 4 = 0⌝ ∗ ByteSlice ptr (serialize values))

/-- At an aligned address, the byte and word-array views are exactly the same
physical ownership. -/
theorem ByteSlice_serialize_as_WordSlice {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32)
    (halign : ptr.toNat % 4 = 0) :
    ByteSlice (host := host) ptr (serialize values) ⊣⊢
      WordSlice ptr values := by
  unfold WordSlice
  constructor
  · iintro Hbytes
    isplitl_pureexact halign
    · iexact Hbytes
  · iintro ⟨%_halign, Hbytes⟩
    iexact Hbytes

/-- An arbitrary aligned `4*n`-byte slice can be viewed canonically as `n`
words, without adding an initialization assumption. -/
theorem ByteSlice_as_decodedWordSlice {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (bytes : List UInt8) (count : Nat)
    (halign : ptr.toNat % 4 = 0)
    (hlength : bytes.length = 4 * count) :
    ByteSlice (host := host) ptr bytes ⊣⊢
      WordSlice ptr (decodeWords bytes) := by
  have hdecode := serialize_decodeWords_of_length bytes count hlength
  have hslice :
      ByteSlice (host := host) ptr (serialize (decodeWords bytes)) =
        ByteSlice ptr bytes :=
    congrArg (fun concrete => ByteSlice (host := host) ptr concrete) hdecode.1
  constructor
  · iintro Hbytes
    ihave Hencoded : ByteSlice ptr (serialize (decodeWords bytes)) $$ [Hbytes]
    · irw_exact [hslice] with Hbytes
    iapply (ByteSlice_serialize_as_WordSlice ptr
      (decodeWords bytes) halign).mp
    iexact Hencoded
  · iintro Hwords
    ihave Hencoded := (ByteSlice_serialize_as_WordSlice ptr
      (decodeWords bytes) halign).mpr $$ Hwords
    ihave Hbytes : ByteSlice ptr bytes $$ [Hencoded]
    · irw_exact [← hslice] with Hencoded
    iexact Hbytes

/-- At a known non-wrapping four-byte slot, arbitrary current bytes and the
single-word points-to view are equivalent. -/
theorem ByteSlice_four_as_word {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (bytes : List UInt8)
    (hlength : bytes.length = 4)
    (hnowrap : ptr.toNat + 4 < UInt32.size) :
    ByteSlice (host := host) ptr bytes ⊣⊢
      pointsTo_u32 0 ptr (Spec.decodeWord bytes) := by
  let word := Spec.decodeWord bytes
  have hencoded :
      [u32Byte word 0, u32Byte word 1, u32Byte word 2, u32Byte word 3] =
        bytes := by
    rw [← encodeWord_eq_u32Bytes]
    exact encodeWord_decodeWord_of_length bytes hlength
  constructor
  · iintro Hslice
    isimp only [ByteSlice] at Hslice
    icases Hslice with ⟨%_hsliceNowrap, Hbytes⟩
    iapply (pointsTo_u32_as_bytes 0 ptr word).mpr
    irw_exact [hencoded] with Hbytes
  · iintro Hword
    unfold ByteSlice
    isplitl_pureexact (by simpa [hlength] using hnowrap)
    · ihave Hbytes := (pointsTo_u32_as_bytes 0 ptr word).mp $$ Hword
      ihave Hbytes' : pointsToBytes 0 ptr bytes $$ [Hbytes]
      · irw_exact [← hencoded] with Hbytes
      iexact Hbytes'

/-- Focus the driver's reusable four-byte output slot for one word store and
reassemble it as the canonical singleton serialization. -/
theorem ByteSlice_storeWordFocus {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (oldBytes : List UInt8) (newValue : UInt32)
    (hlength : oldBytes.length = 4)
    (hnowrap : ptr.toNat + 4 < UInt32.size) :
    ByteSlice (host := host) ptr oldBytes ⊢
      iprop(pointsTo_u32 0 ptr (Spec.decodeWord oldBytes) ∗
        (pointsTo_u32 0 ptr newValue -∗
          ByteSlice ptr (serialize [newValue]))) := by
  iintro Hslice
  ihave Hold := (ByteSlice_four_as_word ptr oldBytes hlength hnowrap).mp $$
    Hslice
  isplitl_exact Hold
  · iintro Hnew
    have hnewLength : (serialize [newValue]).length = 4 := by
      rw [serialize_length]
      norm_num
    have hdecode : Spec.decodeWord (serialize [newValue]) = newValue := by
      change Spec.decodeWord (Spec.encodeWord newValue) = newValue
      exact Spec.u32Codec.decode_encode newValue
    iapply (ByteSlice_four_as_word ptr (serialize [newValue])
      hnewLength hnowrap).mpr
    irw_exact [hdecode] with Hnew

/-- Empty canonical word ownership is resource-free.  This is the exact
dangling-pointer case taken by the driver when the public input is empty. -/
theorem WordSlice_nil {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (halign : ptr.toNat % 4 = 0) :
    emp ⊢ WordSlice (host := host) ptr [] := by
  iintro _Hemp
  unfold WordSlice ByteSlice
  isplitl_pureexact halign
  isplitl_pureexact (by simpa [UInt32.size] using ptr.toBitVec.isLt)
  · isimp only [serialize, Wasm.WordCodec.serialize_nil]
    iapply (pointsToBytes_nil 0 ptr).mpr
    itrivial

private theorem wordOffset_eq_byteOffset
    (ptr : UInt32) (values : List UInt32) :
    ptr + 4 * UInt32.ofNat values.length =
      ptr + UInt32.ofNat (serialize values).length := by
  simp only [serialize_length]
  rw [UInt32.ofNat_mul]
  rfl

/-- A no-wrap logical word offset has the expected natural-number address. -/
theorem wordOffset_toNat (ptr : UInt32) (count : Nat)
    (h : ptr.toNat + 4 * count < UInt32.size) :
    (ptr + 4 * UInt32.ofNat count).toNat =
      ptr.toNat + 4 * count := by
  have hcount : count < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul]
  rw [show (4 : UInt32).toNat = 4 by decide,
    UInt32.toNat_ofNat_of_lt' hcount]
  have hprod : 4 * count < 2 ^ 32 := by
    norm_num [UInt32.size] at h ⊢
    omega
  rw [Nat.mod_eq_of_lt hprod]
  change (ptr.toNat + 4 * count) % 2 ^ 32 =
    ptr.toNat + 4 * count
  rw [Nat.mod_eq_of_lt]
  norm_num [UInt32.size] at h ⊢
  exact h

/-- Split and recombine a canonical word slice at a logical list boundary.
The theorem also validates the exact `base + 4 * count` pointer used at both
recursive `func2` call sites. -/
theorem WordSlice_append {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (xs ys : List UInt32) :
    WordSlice (host := host) ptr (xs ++ ys) ⊣⊢
      iprop(WordSlice ptr xs ∗
        WordSlice (ptr + 4 * UInt32.ofNat xs.length) ys) := by
  unfold WordSlice ByteSlice
  simp only [serialize_append, List.length_append, serialize_length]
  constructor
  · iintro ⟨%halign, %hnowrap, Hbytes⟩
    icases (pointsToBytes_append 0 ptr (serialize xs)
      (serialize ys)).mp $$ Hbytes with ⟨Hleft, Hright⟩
    have hleftNowrap :
        ptr.toNat + 4 * xs.length < UInt32.size := by omega
    have hoffset := wordOffset_toNat ptr xs.length hleftNowrap
    have hrightNowrap :
        (ptr + 4 * UInt32.ofNat xs.length).toNat +
            4 * ys.length < UInt32.size := by
      rw [hoffset]
      omega
    have hrightAlign :
        (ptr + 4 * UInt32.ofNat xs.length).toNat % 4 = 0 := by
      rw [hoffset, Nat.add_mod]
      omega
    ihave Hright' :
        pointsToBytes 0 (ptr + 4 * UInt32.ofNat xs.length)
          (serialize ys) $$ [Hright]
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
      rw [hoffset] at hrightNowrap
      omega
    isplitl_pureexact halign
    isplitl_pureexact (by simpa only [Nat.mul_add] using hnowrap)
    iapply (pointsToBytes_append 0 ptr (serialize xs) (serialize ys)).mpr
    isplitl_exact Hleft
    · irw_exact [← wordOffset_eq_byteOffset] with Hright

/-- Retain a word slice while exposing its alignment and exact no-wrap facts. -/
theorem WordSlice_facts {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32) :
    WordSlice (host := host) ptr values ⊢
      iprop(WordSlice ptr values ∗
        ⌜ptr.toNat % 4 = 0 ∧
          ptr.toNat + 4 * values.length < UInt32.size⌝) := by
  unfold WordSlice ByteSlice
  iintro ⟨%halign, %hnowrap, Hbytes⟩
  isplitl [Hbytes]
  · iframe Hbytes
    ipureexact ⟨halign, hnowrap⟩
  · ipureexact ⟨halign, by simpa only [serialize_length] using hnowrap⟩

/-- Existing `arrayAt` proofs and the canonical codec describe the same
physical bytes. -/
theorem arrayAt_eq_wordCells {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32) :
    arrayAt (α := host) 0 ptr values ⊣⊢ WordCells ptr values := by
  induction values generalizing ptr with
  | nil => exact .rfl
  | cons value rest ih =>
      simp only [arrayAt, WordCells, serialize, WordCodec.serialize_cons]
      change pointsTo_u32 0 ptr value ∗ arrayAt 0 (ptr + 4) rest ⊣⊢
        pointsToBytes 0 ptr
          (Spec.encodeWord value ++ U32Codec.serialize rest)
      rw [encodeWord_eq_u32Bytes]
      exact (BI.sep_congr
          (pointsTo_u32_as_bytes 0 ptr value)
          (by simpa using ih (ptr + 4))).trans
        (pointsToBytes_append 0 ptr
          [u32Byte value 0, u32Byte value 1,
            u32Byte value 2, u32Byte value 3]
          (U32Codec.serialize rest)).symm

/-- Focus one readable word cell and return the exact continuation that
reassembles the canonical word slice.  The explicit index premise is the
originating guard obligation for generated bounds-error branches. -/
theorem WordSlice_get {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32) (k : Nat)
    (hk : k < values.length) :
    WordSlice (host := host) ptr values ⊢
      iprop(pointsTo_u32 0 (ptr + 4 * UInt32.ofNat k) values[k] ∗
        (pointsTo_u32 0 (ptr + 4 * UInt32.ofNat k) values[k] -∗
          WordSlice ptr values)) := by
  unfold WordSlice ByteSlice
  iintro ⟨%halign, %hnowrap, Hbytes⟩
  ihave Harray : arrayAt 0 ptr values $$ [Hbytes]
  · iapply (arrayAt_eq_wordCells ptr values).mpr
    iexact Hbytes
  ihave ⟨Hcell, Hclose⟩ := arrayAt_get 0 ptr values k hk $$ Harray
  isplitl_exact Hcell
  · iintro Hcell
    ihave Harray := Hclose $$ Hcell
    ihave Hbytes : WordCells ptr values $$ [Harray]
    · iapply (arrayAt_eq_wordCells ptr values).mp
      iexact Harray
    iframe Hbytes
    ipureexact ⟨halign, hnowrap⟩

/-- Focus one writable word cell.  Returning a new value reassembles the same
physical slice with exactly the corresponding logical list update. -/
theorem WordSlice_set {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (values : List UInt32) (k : Nat)
    (newValue : UInt32) (hk : k < values.length) :
    WordSlice (host := host) ptr values ⊢
      iprop(pointsTo_u32 0 (ptr + 4 * UInt32.ofNat k) values[k] ∗
        (pointsTo_u32 0 (ptr + 4 * UInt32.ofNat k) newValue -∗
          WordSlice ptr (values.set k newValue))) := by
  unfold WordSlice ByteSlice
  iintro ⟨%halign, %hnowrap, Hbytes⟩
  ihave Harray : arrayAt 0 ptr values $$ [Hbytes]
  · iapply (arrayAt_eq_wordCells ptr values).mpr
    iexact Hbytes
  ihave ⟨Hcell, Hclose⟩ := arrayAt_set 0 ptr values k newValue hk $$ Harray
  isplitl_exact Hcell
  · iintro Hcell
    ihave Harray := Hclose $$ Hcell
    ihave Hbytes : WordCells ptr (values.set k newValue) $$ [Harray]
    · iapply (arrayAt_eq_wordCells ptr (values.set k newValue)).mp
      iexact Harray
    iframe Hbytes
    ipureintro
    refine ⟨halign, ?_⟩
    simpa using hnowrap

/-- The two disjoint equal-length arrays owned by recursive merge sort. -/
def SortBuffers {host : Type} [WasmHeapGS host]
    (source scratch : UInt32)
    (input scratchValues : List UInt32) : IProp (WasmHeapGF host) :=
  iprop(WordSlice source input ∗ WordSlice scratch scratchValues ∗
    ⌜input.length = scratchValues.length ∧
      MemRegion.Disjoint
        ⟨source, 4 * input.length⟩
        ⟨scratch, 4 * scratchValues.length⟩⌝)

/-- Chronological bump-allocation order is sufficient for the cross-buffer
disjointness field required by `SortBuffers`. -/
theorem wordRegions_disjoint_of_order
    (source scratch : UInt32)
    (input scratchValues : List UInt32)
    (horder : source.toNat + 4 * input.length ≤ scratch.toNat) :
    MemRegion.Disjoint
      ⟨source, 4 * input.length⟩
      ⟨scratch, 4 * scratchValues.length⟩ := by
  unfold MemRegion.Disjoint
  exact Or.inl horder

/-- The driver may pass its aligned dangling pointer as both arrays at length
zero; neither empty slice owns bytes. -/
theorem SortBuffers_empty {host : Type} [WasmHeapGS host]
    (ptr : UInt32) (halign : ptr.toNat % 4 = 0) :
    emp ⊢ SortBuffers (host := host) ptr ptr [] [] := by
  iintro _Hemp
  unfold SortBuffers
  isplitl []
  · iapply WordSlice_nil ptr halign
    itrivial
  isplitl []
  · iapply WordSlice_nil ptr halign
    itrivial
  · ipureintro
    constructor
    · rfl
    · unfold MemRegion.Disjoint
      simp

/-- Simultaneously focus a source read and scratch write.  The closing
continuation retains the source and updates exactly one scratch element while
preserving equal lengths and full cross-buffer disjointness. -/
theorem SortBuffers_copyFocus {host : Type} [WasmHeapGS host]
    (source scratch : UInt32)
    (input scratchValues : List UInt32)
    (i k : Nat) (newValue : UInt32)
    (hi : i < input.length) (hk : k < scratchValues.length) :
    SortBuffers (host := host) source scratch input scratchValues ⊢
      iprop(
        pointsTo_u32 0 (source + 4 * UInt32.ofNat i) input[i] ∗
        pointsTo_u32 0 (scratch + 4 * UInt32.ofNat k) scratchValues[k] ∗
        (pointsTo_u32 0 (source + 4 * UInt32.ofNat i) input[i] -∗
         pointsTo_u32 0 (scratch + 4 * UInt32.ofNat k) newValue -∗
          SortBuffers source scratch input
            (scratchValues.set k newValue))) := by
  unfold SortBuffers
  iintro ⟨Hsource, Hscratch, %hfacts⟩
  ihave ⟨HsourceCell, HsourceClose⟩ := WordSlice_get source input i hi $$ Hsource
  ihave ⟨HscratchCell, HscratchClose⟩ :=
    WordSlice_set scratch scratchValues k newValue hk $$ Hscratch
  isplitl_exacts [HsourceCell HscratchCell]
  iintro HsourceCell
  iintro HscratchCell
  ihave Hsource := HsourceClose $$ HsourceCell
  ihave Hscratch := HscratchClose $$ HscratchCell
  iframe Hsource Hscratch
  ipureintro
  simpa using hfacts

/-- Expose both complete byte ranges for the generated final
`memory.copy(source, scratch, 4*n)`.  Returning the overwritten source bytes
and the unchanged scratch bytes reseals the exact nontrivial `func2` post in
which both arrays contain the same output. -/
theorem SortBuffers_copyBackFocus {host : Type} [WasmHeapGS host]
    (source scratch : UInt32)
    (sourceValues output : List UInt32) :
    SortBuffers (host := host) source scratch sourceValues output ⊢
      iprop(
        pointsToBytes 0 source (serialize sourceValues) ∗
        pointsToBytes 0 scratch (serialize output) ∗
        (pointsToBytes 0 source (serialize output) -∗
         pointsToBytes 0 scratch (serialize output) -∗
          SortBuffers source scratch output output)) := by
  unfold SortBuffers WordSlice ByteSlice
  iintro ⟨⟨%hsourceAlign, %hsourceNowrap, Hsource⟩,
    ⟨%hscratchAlign, %hscratchNowrap, Hscratch⟩, %hfacts⟩
  isplitl_exacts [Hsource Hscratch]
  iintro Hsource
  iintro Hscratch
  isplitl [Hsource]
  · isplitl_pureexact hsourceAlign
    isplitl_pureexact (by simpa only [serialize_length, hfacts.1] using hsourceNowrap)
    · iexact Hsource
  isplitl [Hscratch]
  · isplitl_pureexact hscratchAlign
    isplitl_pureexact hscratchNowrap
    · iexact Hscratch
  · ipureexact ⟨rfl, by simpa only [hfacts.1] using hfacts.2⟩

private theorem disjoint_prefixes
    (source scratch : UInt32)
    (left right scratchLeft scratchRight : List UInt32)
    (hfull : MemRegion.Disjoint
      ⟨source, 4 * (left ++ right).length⟩
      ⟨scratch, 4 * (scratchLeft ++ scratchRight).length⟩) :
    MemRegion.Disjoint
      ⟨source, 4 * left.length⟩
      ⟨scratch, 4 * scratchLeft.length⟩ := by
  unfold MemRegion.Disjoint at hfull ⊢
  simp only [List.length_append, Nat.mul_add] at hfull ⊢
  rcases hfull with h | h
  · left
    omega
  · right
    omega

private theorem disjoint_suffixes
    (source scratch : UInt32)
    (left right scratchLeft scratchRight : List UInt32)
    (hsourceOffset :
      (source + 4 * UInt32.ofNat left.length).toNat =
        source.toNat + 4 * left.length)
    (hscratchOffset :
      (scratch + 4 * UInt32.ofNat scratchLeft.length).toNat =
        scratch.toNat + 4 * scratchLeft.length)
    (hfull : MemRegion.Disjoint
      ⟨source, 4 * (left ++ right).length⟩
      ⟨scratch, 4 * (scratchLeft ++ scratchRight).length⟩) :
    MemRegion.Disjoint
      ⟨source + 4 * UInt32.ofNat left.length, 4 * right.length⟩
      ⟨scratch + 4 * UInt32.ofNat scratchLeft.length,
        4 * scratchRight.length⟩ := by
  unfold MemRegion.Disjoint at hfull ⊢
  simp only [List.length_append, Nat.mul_add] at hfull ⊢
  rw [hsourceOffset, hscratchOffset]
  rcases hfull with h | h
  · left
    omega
  · right
    omega

/-- Split and recombine both arrays at the same logical boundary.  The full
cross-buffer disjointness fact is retained explicitly because it is needed to
reassemble the caller after framing one half across a recursive call. -/
theorem SortBuffers_append {host : Type} [WasmHeapGS host]
    (source scratch : UInt32)
    (left right scratchLeft scratchRight : List UInt32)
    (hleftLength : left.length = scratchLeft.length)
    (hrightLength : right.length = scratchRight.length) :
    SortBuffers (host := host) source scratch
        (left ++ right) (scratchLeft ++ scratchRight) ⊣⊢
      iprop(
        SortBuffers source scratch left scratchLeft ∗
        SortBuffers
          (source + 4 * UInt32.ofNat left.length)
          (scratch + 4 * UInt32.ofNat scratchLeft.length)
          right scratchRight ∗
        ⌜MemRegion.Disjoint
          ⟨source, 4 * (left ++ right).length⟩
          ⟨scratch, 4 * (scratchLeft ++ scratchRight).length⟩⌝) := by
  constructor
  · iintro Hbuffers
    isimp only [SortBuffers] at Hbuffers
    icases Hbuffers with ⟨Hsource, Hscratch, %hfacts⟩
    ihave ⟨Hsource, %hsourceFacts⟩ :=
      WordSlice_facts source (left ++ right) $$ Hsource
    ihave ⟨Hscratch, %hscratchFacts⟩ :=
      WordSlice_facts scratch (scratchLeft ++ scratchRight) $$ Hscratch
    icases (WordSlice_append source left right).mp $$ Hsource with
      ⟨HsourceLeft, HsourceRight⟩
    icases (WordSlice_append scratch scratchLeft scratchRight).mp $$ Hscratch with
      ⟨HscratchLeft, HscratchRight⟩
    have hsourcePrefix :
        source.toNat + 4 * left.length < UInt32.size := by
      simp only [List.length_append, Nat.mul_add] at hsourceFacts
      omega
    have hscratchPrefix :
        scratch.toNat + 4 * scratchLeft.length < UInt32.size := by
      simp only [List.length_append, Nat.mul_add] at hscratchFacts
      omega
    have hsourceOffset :=
      wordOffset_toNat source left.length hsourcePrefix
    have hscratchOffset :=
      wordOffset_toNat scratch scratchLeft.length hscratchPrefix
    have hleftDisjoint := disjoint_prefixes source scratch left right
      scratchLeft scratchRight hfacts.2
    have hrightDisjoint := disjoint_suffixes source scratch left right
      scratchLeft scratchRight hsourceOffset hscratchOffset hfacts.2
    isplitl [HsourceLeft HscratchLeft]
    · unfold SortBuffers
      iframe
      ipureexact ⟨hleftLength, hleftDisjoint⟩
    isplitl [HsourceRight HscratchRight]
    · unfold SortBuffers
      iframe
      ipureexact ⟨hrightLength, hrightDisjoint⟩
    · ipureexact hfacts.2
  · iintro ⟨Hleft, Hright, %hfull⟩
    isimp only [SortBuffers] at Hleft Hright
    icases Hleft with ⟨HsourceLeft, HscratchLeft, %_hleftFacts⟩
    icases Hright with ⟨HsourceRight, HscratchRight, %_hrightFacts⟩
    unfold SortBuffers
    isplitl [HsourceLeft HsourceRight]
    · iapply_frame (WordSlice_append source left right).mpr
    isplitl [HscratchLeft HscratchRight]
    · iapply_frame (WordSlice_append scratch scratchLeft scratchRight).mpr
    · ipureexact ⟨by
        simp only [List.length_append, hleftLength, hrightLength], hfull⟩

/-! ## Allocator vocabulary and ownership -/

/-- Canonical address of the generated bump cursor. -/
def allocatorCursor : UInt32 := 1049492

/-- First address which the generated bump allocator may commit. -/
def heapBase : UInt32 := 1049536

/-- Initial shadow-stack top and the generated driver's two frame boundaries. -/
def entryStackTop : UInt32 := 1048576
def driverBase : UInt32 := entryStackTop - 272
def entryStackLow : UInt32 := entryStackTop - 288
def reserveBase : UInt32 := driverBase - 16

structure AllocLayout where
  size : Nat
  alignment : Nat
  deriving Repr, DecidableEq

def AllocLayout.Valid (layout : AllocLayout) : Prop :=
  0 < layout.size ∧
  0 < layout.alignment ∧
  (∃ exponent, layout.alignment = 2 ^ exponent) ∧
  layout.alignment ≤ 2147483648 ∧
  layout.size ≤ 2147483648 - layout.alignment ∧
  layout.size < UInt32.size ∧
  layout.alignment < UInt32.size

def AllocLayout.Matches (layout : AllocLayout)
    (wasmSize wasmAlignment : UInt32) : Prop :=
  wasmSize.toNat = layout.size ∧
  wasmAlignment.toNat = layout.alignment

inductive BumpDecision where
  | success (base finish : UInt32)
  | oom
  deriving Repr, DecidableEq

/-- Exact classification of the allocator's two checked additions, alignment
mask, and signed-end guard. -/
def classifyBump (frontier : Nat) (layout : AllocLayout) : BumpDecision :=
  let sum := frontier + (layout.alignment - 1)
  if _hsum : sum < UInt32.size then
    let sumWord := UInt32.ofNat sum
    let alignmentWord := UInt32.ofNat layout.alignment
    let base := sumWord &&& (0 - alignmentWord)
    let finish := base.toNat + layout.size
    if finish < UInt32.size ∧ finish < 2147483648 then
      .success base (UInt32.ofNat finish)
    else
      .oom
  else
    .oom

private theorem align1_mask (x : UInt32) :
    x &&& (0 - 1) = x := by
  simp

private theorem align4_mask_toNat (x : UInt32) :
    (x &&& (0 - 4)).toNat = x.toNat - x.toNat % 4 := by
  change (x.toBitVec &&& ((0 - 4 : UInt32).toBitVec)).toNat =
    x.toBitVec.toNat - x.toBitVec.toNat % 4
  have hmask :
      ((0 - 4 : UInt32).toBitVec) = BitVec.allOnes 32 <<< 2 := by
    decide
  rw [hmask, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  have hdiv : x.toBitVec.toNat / 4 * 4 =
      x.toBitVec.toNat - x.toBitVec.toNat % 4 := by
    omega
  have hbound : x.toBitVec.toNat / 4 * 4 < 4294967296 := by
    have hx := x.toBitVec.isLt
    omega
  change (x.toBitVec.toNat / 4 * 4) % 4294967296 =
    x.toBitVec.toNat - x.toBitVec.toNat % 4
  rw [Nat.mod_eq_of_lt hbound]
  exact hdiv

/-- The exact arithmetic facts exposed by a successful bump classification. -/
theorem classifyBump_success_facts
    (frontier : Nat) (layout : AllocLayout) (base finish : UInt32)
    (h : classifyBump frontier layout = .success base finish) :
    let sum := frontier + (layout.alignment - 1)
    sum < UInt32.size ∧
    base = (UInt32.ofNat sum &&&
      (0 - UInt32.ofNat layout.alignment)) ∧
    base.toNat + layout.size < UInt32.size ∧
    base.toNat + layout.size < 2147483648 ∧
    finish.toNat = base.toNat + layout.size := by
  let sum := frontier + (layout.alignment - 1)
  change (if _hsum : sum < UInt32.size then
      let sumWord := UInt32.ofNat sum
      let alignmentWord := UInt32.ofNat layout.alignment
      let base := sumWord &&& (0 - alignmentWord)
      let finish := base.toNat + layout.size
      if finish < UInt32.size ∧ finish < 2147483648 then
        BumpDecision.success base (UInt32.ofNat finish)
      else BumpDecision.oom
    else BumpDecision.oom) = BumpDecision.success base finish at h
  split at h
  · rename_i hsum
    dsimp only at h
    split at h
    · rename_i hend
      injection h with hbase hfinish
      subst base
      subst finish
      dsimp only at hend ⊢
      exact ⟨hsum, rfl, hend.1, hend.2,
        UInt32.toNat_ofNat_of_lt' hend.1⟩
    · contradiction
  · contradiction

inductive AllocationStatus where
  | live
  | retired
  deriving Repr, DecidableEq

structure AllocationRecord where
  allocationId : Nat
  ptr : UInt32
  layout : AllocLayout
  status : AllocationStatus
  deriving Repr, DecidableEq

def AllocationStatus.toMetaStatus : AllocationStatus → AllocationMetaStatus
  | .live => .live
  | .retired => .retired

def AllocationRecord.toMeta (record : AllocationRecord) : AllocationMeta :=
  { ptr := record.ptr
    size := record.layout.size
    alignment := record.layout.alignment
    status := record.status.toMetaStatus }

/-- The metadata value created for a new live allocation. -/
def liveMeta (ptr : UInt32) (layout : AllocLayout) : AllocationMeta :=
  { ptr := ptr
    size := layout.size
    alignment := layout.alignment
    status := .live }

/-- The metadata value retained after the no-op Wasm deallocator is called. -/
def retiredMeta (ptr : UInt32) (layout : AllocLayout) : AllocationMeta :=
  { ptr := ptr
    size := layout.size
    alignment := layout.alignment
    status := .retired }

def allocationLayout (metadata : AllocationMeta) : AllocLayout :=
  { size := metadata.size, alignment := metadata.alignment }

def allocationEndExclusive (metadata : AllocationMeta) : Nat :=
  metadata.ptr.toNat + metadata.size

def AllocationMetaValid (metadata : AllocationMeta) : Prop :=
  (allocationLayout metadata).Valid ∧
    metadata.ptr ≠ 0 ∧
    metadata.ptr.toNat % metadata.alignment = 0

/-- At the two alignments used by reachable merge-sort allocations, a
successful classification yields a fresh, non-null, aligned range and valid
metadata.  This is the pure arithmetic bridge used by allocator call specs. -/
theorem classifyBump_success_reachable
    (frontier : Nat) (layout : AllocLayout) (base finish : UInt32)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish) :
    frontier ≤ base.toNat ∧
    base ≠ 0 ∧
    base.toNat % layout.alignment = 0 ∧
    base.toNat + layout.size < UInt32.size ∧
    base.toNat + layout.size < 2147483648 ∧
    finish.toNat = base.toNat + layout.size ∧
    AllocationMetaValid (liveMeta base layout) := by
  have hraw :=
    classifyBump_success_facts frontier layout base finish hclassify
  dsimp only at hraw
  rcases hraw with ⟨hsum, hbase, hendWord, hendSigned, hfinish⟩
  have hheapBasePositive : 0 < heapBase.toNat := by decide
  rcases halignment with halignment | halignment
  · have hsum' : frontier < UInt32.size := by
      simpa only [halignment, Nat.reduceSubDiff, Nat.add_zero] using hsum
    have hbase' :
        base = UInt32.ofNat frontier &&& (0 - 1) := by
      norm_num [halignment] at hbase ⊢
      exact hbase
    rw [align1_mask] at hbase'
    have hbaseNat : base.toNat = frontier := by
      rw [hbase', UInt32.toNat_ofNat_of_lt' hsum']
    have hnonnull : base ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero
      simp only [UInt32.toNat_zero] at hzeroNat
      rw [hbaseNat] at hzeroNat
      omega
    have haligned : base.toNat % layout.alignment = 0 := by
      rw [halignment]
      exact Nat.mod_one _
    refine ⟨?_, hnonnull, haligned, hendWord, hendSigned, hfinish, ?_⟩
    · omega
    · exact ⟨hvalid, hnonnull, haligned⟩
  · have hsum' : frontier + 3 < UInt32.size := by
      norm_num [halignment] at hsum ⊢
      exact hsum
    have hbase' :
        base = UInt32.ofNat (frontier + 3) &&& (0 - 4) := by
      norm_num [halignment] at hbase ⊢
      exact hbase
    have hsumWord :
        (UInt32.ofNat (frontier + 3)).toNat = frontier + 3 := by
      exact UInt32.toNat_ofNat_of_lt' hsum'
    have hbaseNat :
        base.toNat = (frontier + 3) - (frontier + 3) % 4 := by
      rw [hbase', align4_mask_toNat, hsumWord]
    have hrem : (frontier + 3) % 4 < 4 :=
      Nat.mod_lt _ (by decide)
    have hstart : frontier ≤ base.toNat := by omega
    have hmod4 : base.toNat % 4 = 0 := by
      rw [hbaseNat]
      exact Nat.mod_eq_zero_of_dvd
        (Nat.dvd_sub_mod (n := 4) (frontier + 3))
    have hnonnull : base ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero
      simp only [UInt32.toNat_zero] at hzeroNat
      rw [hzeroNat] at hstart
      omega
    have haligned : base.toNat % layout.alignment = 0 := by
      simpa only [halignment] using hmod4
    exact ⟨hstart, hnonnull, haligned, hendWord, hendSigned, hfinish,
      hvalid, hnonnull, haligned⟩

/-- Alignment-one bump allocation is exact: no padding is introduced, so the
returned pointer is the old frontier and the returned cursor is that frontier
plus the requested size. -/
theorem classifyBump_success_align1
    (frontier size : Nat) (base finish : UInt32)
    (hclassify :
      classifyBump frontier { size := size, alignment := 1 } =
        .success base finish) :
    frontier < UInt32.size ∧
      base = UInt32.ofNat frontier ∧
      base.toNat = frontier ∧
      base.toNat + size < UInt32.size ∧
      base.toNat + size < 2147483648 ∧
      finish.toNat = frontier + size := by
  have hraw :=
    classifyBump_success_facts frontier
      { size := size, alignment := 1 } base finish hclassify
  dsimp only at hraw
  rcases hraw with ⟨hsum, hbase, hendWord, hendSigned, hfinish⟩
  have hfrontier : frontier < UInt32.size := by
    norm_num at hsum ⊢
    exact hsum
  have hbase' : base = UInt32.ofNat frontier := by
    norm_num at hbase
    exact hbase
  have hbaseNat : base.toNat = frontier := by
    rw [hbase', UInt32.toNat_ofNat_of_lt' hfrontier]
  exact ⟨hfrontier, hbase', hbaseNat, hendWord, hendSigned, by
    rw [hfinish, hbaseNat]⟩

/-! ## Allocator memory-growth arithmetic -/

/-- The exact page target computed by the three reachable bump-allocation
paths after their signed-end guard. -/
def allocatorRequiredPages (finish : UInt32) : UInt32 :=
  (finish + 65535) >>> (16 : UInt32)

/-- Below the allocator's signed-end limit, its generated shift computes the
ordinary ceiling page count without wrapping the preceding addition. -/
theorem allocatorRequiredPages_toNat (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    (allocatorRequiredPages finish).toNat =
      (finish.toNat + 65535) / 65536 := by
  have hsum : finish.toNat + 65535 < 2 ^ 32 := by omega
  unfold allocatorRequiredPages
  rw [UInt32.toNat_shiftRight,
    show (16 : UInt32).toNat % 32 = 16 by decide,
    Nat.shiftRight_eq_div_pow]
  norm_num
  rw [show (65535 : UInt32).toNat = 65535 by decide]
  norm_num at hsum
  rw [Nat.mod_eq_of_lt hsum]

/-- The generated ceiling page count physically covers every byte through the
accepted allocation finish. -/
theorem allocatorRequiredPages_covers (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    finish.toNat ≤ (allocatorRequiredPages finish).toNat * 65536 := by
  rw [allocatorRequiredPages_toNat finish hfinish]
  have hself : (finish.toNat + 65535) / 65536 ≤
      (finish.toNat + 65535) / 65536 := Nat.le_refl _
  have hceil :=
    (Nat.div_le_iff_le_mul (by norm_num : 0 < 65536)).mp hself
  omega

/-- A successful signed-end check bounds the allocator's target by 2 GiB, or
32768 Wasm pages.  This also justifies that the `finish + 65535` computation
used for ceiling division cannot wrap. -/
theorem allocatorRequiredPages_le_signedLimit (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    (allocatorRequiredPages finish).toNat ≤ 32768 := by
  have hsum : finish.toNat + 65535 < 2 ^ 32 := by omega
  have hquot :
      (finish.toNat + 65535) / 65536 < 32769 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 65536)]
    omega
  have hquotle :
      (finish.toNat + 65535) / 65536 ≤ 32768 := by omega
  unfold allocatorRequiredPages
  rw [UInt32.toNat_shiftRight,
    show (16 : UInt32).toNat % 32 = 16 by decide,
    Nat.shiftRight_eq_div_pow]
  norm_num
  rw [show (65535 : UInt32).toNat = 65535 by decide]
  norm_num at hsum
  rw [Nat.mod_eq_of_lt hsum]
  exact hquotle

/-- At a cap large enough for the target, growing by the exact difference
returns the old page count and installs the target page count. -/
theorem memoryGrow_to_pages (memory : Mem) (target cap : Nat)
    (hle : memory.pages ≤ target)
    (hcap : target ≤ cap)
    (htarget : target < UInt32.size) :
    memory.grow (UInt32.ofNat (target - memory.pages)) cap =
      some ({ memory with pages := target }, memory.pages) := by
  have hdiff : target - memory.pages < UInt32.size := by omega
  simp [Mem.grow, UInt32.toNat_ofNat_of_lt' hdiff,
    Nat.add_sub_of_le hle, hcap]

/-- Once `memory.size < requiredPages`, the exact subtraction emitted by the
allocator grows successfully at the Wasm i32 hard cap. -/
theorem allocatorMemoryGrow_succeeds (memory : Mem) (finish : UInt32)
    (hfinish : finish.toNat < 2147483648)
    (hneed : memory.pages < (allocatorRequiredPages finish).toNat) :
    memory.grow
      (allocatorRequiredPages finish - UInt32.ofNat memory.pages)
      Module.memoryHardCap =
      some ({ memory with pages :=
        (allocatorRequiredPages finish).toNat }, memory.pages) := by
  have htarget :=
    allocatorRequiredPages_le_signedLimit finish hfinish
  have hpages : memory.pages < UInt32.size := by
    norm_num [UInt32.size] at htarget ⊢
    omega
  have hpagesWord :
      (UInt32.ofNat memory.pages).toNat = memory.pages :=
    UInt32.toNat_ofNat_of_lt' hpages
  have hleWords :
      UInt32.ofNat memory.pages ≤ allocatorRequiredPages finish := by
    rw [UInt32.le_iff_toNat_le_toNat, hpagesWord]
    omega
  have hdelta :
      (allocatorRequiredPages finish -
        UInt32.ofNat memory.pages).toNat =
      (allocatorRequiredPages finish).toNat - memory.pages := by
    rw [UInt32.toNat_sub_of_le _ _ hleWords, hpagesWord]
  unfold Mem.grow
  simp only [hdelta, Nat.add_sub_of_le (Nat.le_of_lt hneed)]
  norm_num [Module.memoryHardCap]
  omega

/-- The frozen module declares no maximum, so its declaration-level cap is
the interpreter's i32 hard cap. -/
theorem module_memoryCap :
    Project.Mergesort.module.memoryCap = Module.memoryHardCap := by
  rfl

/-- Instantiation materializes that declaration-level cap in memory-resource
metadata.  A modular allocator proof still needs a state-linked invariant
showing that this immutable field remains the current store's metadata. -/
theorem initialStore_memoryCaps :
    (Project.Mergesort.module.initialStore
      (α := Universal.State)).memoryCaps = [Module.memoryHardCap] := by
  rfl

theorem initialStore_memoryCap :
    (Project.Mergesort.module.initialStore
      (α := Universal.State)).memoryCap Project.Mergesort.module 0 =
      Module.memoryHardCap := by
  rfl

/-- Map-native allocation history.  `nextId` makes freshness explicit; the
map itself is exactly the value stored in ghost authority. -/
structure AllocationHistory where
  records : WasmAllocationMap AllocationMeta
  nextId : Nat

def AllocationHistory.empty : AllocationHistory :=
  { records := ∅, nextId := 0 }

def AllocationHistory.allocate (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout) : AllocationHistory :=
  { records := insert history.records history.nextId (liveMeta ptr layout)
    nextId := history.nextId + 1 }

def AllocationHistory.retire (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32)
    (layout : AllocLayout) : AllocationHistory :=
  { records := insert history.records allocationId (retiredMeta ptr layout)
    nextId := history.nextId }

/-- The metadata transition performed by the reachable reallocator: append
the fresh live block, then retain the old allocation as retired metadata. -/
def AllocationHistory.reallocate (history : AllocationHistory)
    (oldId : Nat) (oldPtr : UInt32) (oldLayout : AllocLayout)
    (newPtr : UInt32) (newLayout : AllocLayout) : AllocationHistory :=
  (history.allocate newPtr newLayout).retire oldId oldPtr oldLayout

def AllocMetaAuth {host : Type} (heapId : GName)
    (history : AllocationHistory) : IProp (WasmHeapGF host) :=
  ghost_map_auth heapId (DFrac.own 1) history.records

/-- Exclusive live-allocation handle.  Its value contains the complete
pointer/layout/status tuple, so agreement with `AllocMetaAuth` rules out using
one allocation identifier for two blocks. -/
def AllocToken {host : Type} (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) : IProp (WasmHeapGF host) :=
  ghost_map_elem heapId (DFrac.own 1) allocationId (liveMeta ptr layout)

/-- Complete ownership of one live allocation. -/
def LiveBlock {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) (bytes : List UInt8) :
    IProp (WasmHeapGF host) := iprop%
  AllocToken heapId allocationId ptr layout ∗
    ByteSlice ptr bytes ∗
    ⌜bytes.length = layout.size ∧
      ptr ≠ 0 ∧
      ptr.toNat % layout.alignment = 0⌝

/-- The deliberately transparent open/reseal law for a complete live block. -/
theorem LiveBlock_open {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock (host := host) heapId allocationId ptr layout bytes ⊣⊢
      iprop(AllocToken heapId allocationId ptr layout ∗
        ByteSlice ptr bytes ∗
        ⌜bytes.length = layout.size ∧ ptr ≠ 0 ∧
          ptr.toNat % layout.alignment = 0⌝) :=
  .rfl

/-- Temporarily expose all physical bytes of a live allocation while framing
its exclusive allocation token.  Any same-sized replacement bytes reseal the
same live allocation. -/
theorem LiveBlock_bytesFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) (oldBytes : List UInt8) :
    LiveBlock (host := host) heapId allocationId ptr layout oldBytes ⊢
      iprop(ByteSlice ptr oldBytes ∗
        (∀ newBytes : List UInt8,
          ⌜newBytes.length = layout.size⌝ -∗
          ByteSlice ptr newBytes -∗
          LiveBlock heapId allocationId ptr layout newBytes)) := by
  unfold LiveBlock
  iintro ⟨Htoken, Hbytes, %hfacts⟩
  isplitl_exact Hbytes
  · iintro %newBytes
    iintro %hnewLength
    iintro HnewBytes
    iframe Htoken HnewBytes
    ipureexact ⟨hnewLength, hfacts.2.1, hfacts.2.2⟩

/-- A complete live allocation viewed as canonical little-endian words.  The
token and word bytes are a single owner, not overlapping views. -/
def LiveWordBlock {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (values : List UInt32) :
    IProp (WasmHeapGF host) := iprop%
  AllocToken heapId allocationId ptr
      { size := 4 * values.length, alignment := 4 } ∗
    WordSlice ptr values ∗
    ⌜ptr ≠ 0⌝

/-- The word view and byte view of a live four-aligned allocation are the same
physical resource. -/
theorem LiveWordBlock_as_liveBlock {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (values : List UInt32) :
  LiveWordBlock (host := host) heapId allocationId ptr values ⊣⊢
      LiveBlock heapId allocationId ptr
        { size := 4 * values.length, alignment := 4 } (serialize values) := by
  unfold LiveWordBlock LiveBlock WordSlice ByteSlice
  simp only [serialize_length]
  constructor
  · iintro ⟨Htoken, ⟨%halign, %hnowrap, Hbytes⟩, %hnonnull⟩
    iframe Htoken Hbytes
    ipureexact ⟨hnowrap, trivial, hnonnull, halign⟩
  · iintro ⟨Htoken, ⟨%hnowrap, Hbytes⟩, %hfacts⟩
    iframe Htoken Hbytes
    ipureexact ⟨⟨hfacts.2.2, hnowrap⟩, hfacts.2.1⟩

/-- The reachable zeroing allocator result, specialized to a whole number of
words, is the canonical live word-array representation expected by `func2`. -/
theorem zeroLiveBlock_as_liveWordBlock {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId count : Nat) (ptr : UInt32) :
    LiveBlock (host := host) heapId allocationId ptr
        { size := 4 * count, alignment := 4 }
        (List.replicate (4 * count) 0) ⊣⊢
      LiveWordBlock heapId allocationId ptr (List.replicate count 0) := by
  rw [← serialize_replicate_zero]
  simpa using (LiveWordBlock_as_liveBlock heapId allocationId ptr
    (List.replicate count 0)).symm

/-- A normally allocated arbitrary four-aligned block has a canonical initial
word-array view of the requested length.  This is the exact starting state for
the driver's decode-copy loop. -/
theorem LiveBlock_as_decodedWordBlock {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId count : Nat)
    (ptr : UInt32) (bytes : List UInt8)
    (hlength : bytes.length = 4 * count) :
    LiveBlock (host := host) heapId allocationId ptr
        { size := 4 * count, alignment := 4 } bytes ⊣⊢
      LiveWordBlock heapId allocationId ptr (decodeWords bytes) := by
  have hdecode := serialize_decodeWords_of_length bytes count hlength
  simpa only [hdecode.1, hdecode.2] using
    (LiveWordBlock_as_liveBlock heapId allocationId ptr
      (decodeWords bytes)).symm

/-- Frame both live allocation tokens around a `func2` call.  Equal-length
sorted results can be resealed as complete live word blocks for later
deallocation without recreating or duplicating either token. -/
theorem LiveWordBlocks_sortFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (sourceId scratchId : Nat)
    (source scratch : UInt32)
    (input scratchInput : List UInt32)
    (hlength : input.length = scratchInput.length)
    (hdisjoint : MemRegion.Disjoint
      ⟨source, 4 * input.length⟩
      ⟨scratch, 4 * scratchInput.length⟩) :
    LiveWordBlock (host := host) heapId sourceId source input ∗
      LiveWordBlock heapId scratchId scratch scratchInput ⊢
      iprop(SortBuffers source scratch input scratchInput ∗
        (∀ output : List UInt32, ∀ scratchResult : List UInt32,
          ⌜output.length = input.length ∧
            scratchResult.length = scratchInput.length⌝ -∗
          SortBuffers source scratch output scratchResult -∗
          LiveWordBlock heapId sourceId source output ∗
            LiveWordBlock heapId scratchId scratch scratchResult)) := by
  iintro ⟨Hsource, Hscratch⟩
  isimp only [LiveWordBlock] at Hsource Hscratch
  icases Hsource with
    ⟨HsourceToken, HsourceWords, %hsourceNonzero⟩
  icases Hscratch with
    ⟨HscratchToken, HscratchWords, %hscratchNonzero⟩
  isplitl [HsourceWords HscratchWords]
  · unfold SortBuffers
    iframe
    ipureexact ⟨hlength, hdisjoint⟩
  · iintro %output
    iintro %scratchResult
    iintro %hresultLengths
    iintro Hbuffers
    isimp only [SortBuffers] at Hbuffers
    icases Hbuffers with
      ⟨HsourceWords, HscratchWords, %_hbufferFacts⟩
    ihave HsourceToken' : AllocToken heapId sourceId source
        { size := 4 * output.length, alignment := 4 } $$ [HsourceToken]
    · irw_exact [hresultLengths.1] with HsourceToken
    ihave HscratchToken' : AllocToken heapId scratchId scratch
        { size := 4 * scratchResult.length, alignment := 4 } $$
        [HscratchToken]
    · irw_exact [hresultLengths.2] with HscratchToken
    isplitl [HsourceToken' HsourceWords]
    · unfold LiveWordBlock
      iframe
      ipureexact hsourceNonzero
    · unfold LiveWordBlock
      iframe
      ipureexact hscratchNonzero

/-- Pure chronological invariants shared by every allocator contract.  The
map is complete below `nextId`, contains nothing at or above it, and numeric
allocation order is physical non-overlap order. -/
def HistoryWellFormed (frontier : Nat)
    (history : AllocationHistory) : Prop :=
  (∀ allocationId, allocationId < history.nextId →
      ∃ metadata, get? history.records allocationId = some metadata) ∧
  (∀ allocationId metadata,
      get? history.records allocationId = some metadata →
      allocationId < history.nextId ∧
      AllocationMetaValid metadata ∧
      allocationEndExclusive metadata ≤ frontier) ∧
  (∀ earlierId laterId earlier later,
      earlierId < laterId →
      get? history.records earlierId = some earlier →
      get? history.records laterId = some later →
      allocationEndExclusive earlier ≤ later.ptr.toNat) ∧
  get? history.records history.nextId = none ∧
  ((history.nextId = 0 ∧ frontier = heapBase.toNat) ∨
    (0 < history.nextId ∧
      ∃ last, get? history.records (history.nextId - 1) = some last ∧
        allocationEndExclusive last = frontier))

/-- Appending a valid block at or after the old frontier preserves the full
chronological invariant. -/
theorem HistoryWellFormed.allocate
    (frontier : Nat) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : AllocationMetaValid (liveMeta ptr layout))
    (hstart : frontier ≤ ptr.toNat) :
    HistoryWellFormed (ptr.toNat + layout.size)
      (history.allocate ptr layout) := by
  rcases hwf with ⟨hcomplete, hrecords, hordered, hfresh, hlast⟩
  simp only [HistoryWellFormed, AllocationHistory.allocate] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro allocationId hid
    by_cases heq : allocationId = history.nextId
    · subst allocationId
      exact ⟨liveMeta ptr layout, get?_insert_eq rfl⟩
    · have hlt : allocationId < history.nextId := by omega
      obtain ⟨metadata, hmetadata⟩ := hcomplete allocationId hlt
      exact ⟨metadata, (get?_insert_ne (Ne.symm heq)).trans hmetadata⟩
  · intro allocationId metadata hmetadata
    by_cases heq : history.nextId = allocationId
    · subst allocationId
      rw [get?_insert_eq rfl] at hmetadata
      injection hmetadata with hmetadata
      subst metadata
      exact ⟨by omega, hvalid, by
        simp [allocationEndExclusive, liveMeta]⟩
    · rw [get?_insert_ne heq] at hmetadata
      obtain ⟨hid, hvalidOld, hend⟩ :=
        hrecords allocationId metadata hmetadata
      exact ⟨by omega, hvalidOld, by omega⟩
  · intro earlierId laterId earlier later hid hearlier hlater
    by_cases hlaterId : history.nextId = laterId
    · subst laterId
      rw [get?_insert_eq rfl] at hlater
      injection hlater with hlater
      subst later
      have hne : history.nextId ≠ earlierId := by omega
      rw [get?_insert_ne hne] at hearlier
      have hend := (hrecords earlierId earlier hearlier).2.2
      simpa [liveMeta] using _root_.le_trans hend hstart
    · rw [get?_insert_ne hlaterId] at hlater
      by_cases hearlierId : history.nextId = earlierId
      · subst earlierId
        have hlaterLt := (hrecords laterId later hlater).1
        omega
      · rw [get?_insert_ne hearlierId] at hearlier
        exact hordered earlierId laterId earlier later hid hearlier hlater
  · have hnone : get? history.records (history.nextId + 1) = none := by
      cases hget : get? history.records (history.nextId + 1) with
      | none => rfl
      | some metadata =>
          have hlt := (hrecords (history.nextId + 1) metadata hget).1
          omega
    exact (get?_insert_ne (by omega)).trans hnone
  · right
    refine ⟨by omega, liveMeta ptr layout, ?_, ?_⟩
    · simpa using (get?_insert_eq (m := history.records)
        (v := liveMeta ptr layout) rfl)
    · simp [allocationEndExclusive, liveMeta]

/-- Changing a live entry to retired preserves every layout, range, and
chronological fact. -/
theorem HistoryWellFormed.retire
    (frontier : Nat) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (hwf : HistoryWellFormed frontier history)
    (hlookup : get? history.records allocationId =
      some (liveMeta ptr layout)) :
    HistoryWellFormed frontier
      (history.retire allocationId ptr layout) := by
  rcases hwf with ⟨hcomplete, hrecords, hordered, hfresh, hlast⟩
  have hlive := hrecords allocationId (liveMeta ptr layout) hlookup
  have recover :
      ∀ key metadata,
        get? (insert history.records allocationId (retiredMeta ptr layout))
            key = some metadata →
        ∃ oldMetadata,
          get? history.records key = some oldMetadata ∧
          allocationEndExclusive oldMetadata =
            allocationEndExclusive metadata ∧
          oldMetadata.ptr = metadata.ptr := by
    intro key metadata hmetadata
    by_cases hkey : allocationId = key
    · subst key
      rw [get?_insert_eq rfl] at hmetadata
      injection hmetadata with hmetadata
      subst metadata
      exact ⟨liveMeta ptr layout, hlookup, by
        simp [allocationEndExclusive, liveMeta, retiredMeta], by
        simp [liveMeta, retiredMeta]⟩
    · rw [get?_insert_ne hkey] at hmetadata
      exact ⟨metadata, hmetadata, rfl, rfl⟩
  simp only [HistoryWellFormed, AllocationHistory.retire] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro key hkeyLt
    by_cases hkey : allocationId = key
    · subst key
      exact ⟨retiredMeta ptr layout, get?_insert_eq rfl⟩
    · obtain ⟨metadata, hmetadata⟩ := hcomplete key hkeyLt
      exact ⟨metadata, (get?_insert_ne hkey).trans hmetadata⟩
  · intro key metadata hmetadata
    by_cases hkey : allocationId = key
    · subst key
      rw [get?_insert_eq rfl] at hmetadata
      injection hmetadata with hmetadata
      subst metadata
      refine ⟨hlive.1, ?_, ?_⟩
      · simpa [AllocationMetaValid, allocationLayout, liveMeta, retiredMeta]
          using hlive.2.1
      · simpa [allocationEndExclusive, liveMeta, retiredMeta]
          using hlive.2.2
    · rw [get?_insert_ne hkey] at hmetadata
      exact hrecords key metadata hmetadata
  · intro earlierId laterId earlier later hid hearlier hlater
    obtain ⟨oldEarlier, holdEarlier, hendEarlier, _hptrEarlier⟩ :=
      recover earlierId earlier hearlier
    obtain ⟨oldLater, holdLater, _hendLater, hptrLater⟩ :=
      recover laterId later hlater
    calc
      allocationEndExclusive earlier =
          allocationEndExclusive oldEarlier := hendEarlier.symm
      _ ≤ oldLater.ptr.toNat :=
        hordered earlierId laterId oldEarlier oldLater hid
          holdEarlier holdLater
      _ = later.ptr.toNat := congrArg UInt32.toNat hptrLater
  · have hne : allocationId ≠ history.nextId := by omega
    exact (get?_insert_ne hne).trans hfresh
  · rcases hlast with hzero | hpositive
    · exfalso
      omega
    · right
      rcases hpositive with ⟨hnext, last, hlastLookup, hlastEnd⟩
      refine ⟨hnext, ?_⟩
      by_cases hidLast : allocationId = history.nextId - 1
      · refine ⟨retiredMeta ptr layout, get?_insert_eq hidLast, ?_⟩
        have heq : liveMeta ptr layout = last := by
          apply Option.some.inj
          exact hlookup.symm.trans (hidLast ▸ hlastLookup)
        calc
          allocationEndExclusive (retiredMeta ptr layout) =
              allocationEndExclusive (liveMeta ptr layout) := by rfl
          _ = allocationEndExclusive last :=
            congrArg allocationEndExclusive heq
          _ = frontier := hlastEnd
      · exact ⟨last, (get?_insert_ne hidLast).trans hlastLookup,
          hlastEnd⟩

/-- Physical ownership retained by the no-op deallocator.  Live entries
contribute `emp`; retired entries own both their exclusive retired fragment
and their complete bytes exactly once. -/
def RetiredEntry {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (metadata : AllocationMeta) : IProp (WasmHeapGF host) :=
  match metadata.status with
  | .live => iprop(emp)
  | .retired => iprop(
      ghost_map_elem heapId (DFrac.own 1) allocationId metadata ∗
      ∃ bytes : List UInt8,
        ⌜bytes.length = metadata.size⌝ ∗ ByteSlice metadata.ptr bytes)

def RetiredBytes {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory) :
    IProp (WasmHeapGF host) :=
  iprop([∗map] allocationId ↦ metadata ∈ history.records,
    RetiredEntry heapId allocationId metadata)

/-- Complete bump-allocator authority.  Live bytes remain with clients through
`LiveBlock`; this predicate owns only cursor/frontier/metadata authority and
bytes whose records are retired. -/
def BumpHeap {host : Type} [WasmHeapGS host] [WasmHeapDomainGS host]
    [WasmMemoryPagesGS host]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) : IProp (WasmHeapGF host) := iprop%
  pointsTo_u32 0 allocatorCursor storedCursor ∗
    heapFrontierOwn frontier ∗
    AllocMetaAuth heapId history ∗
    RetiredBytes heapId history ∗
    ∃ ownedPages : Nat,
      memoryPagesOwn ownedPages ∗
      ⌜heapBase.toNat ≤ frontier ∧
        frontier < 2147483648 ∧
        (storedCursor = 0 ↔
          history.nextId = 0 ∧ frontier = heapBase.toNat) ∧
        (storedCursor ≠ 0 → storedCursor.toNat = frontier) ∧
        HistoryWellFormed frontier history ∧
        frontier ≤ ownedPages * 65536⌝

/-- Expose every component of `BumpHeap` without changing ownership. -/
theorem BumpHeap_open {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) :
    BumpHeap (host := host) heapId storedCursor frontier history ⊣⊢
      iprop(pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗
        AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗
        ∃ ownedPages : Nat,
          memoryPagesOwn ownedPages ∗
          ⌜heapBase.toNat ≤ frontier ∧
            frontier < 2147483648 ∧
            (storedCursor = 0 ↔
              history.nextId = 0 ∧ frontier = heapBase.toNat) ∧
            (storedCursor ≠ 0 → storedCursor.toNat = frontier) ∧
            HistoryWellFormed frontier history ∧
            frontier ≤ ownedPages * 65536⌝) :=
  .rfl

/-- Allocate empty metadata authority; its ghost name is the logical heap
identity threaded through every block and allocator contract. -/
theorem AllocMetaAuth_alloc_empty {host : Type} :
    ⊢@{IProp (WasmHeapGF host)} |==>
      ∃ heapId : GName, AllocMetaAuth heapId AllocationHistory.empty := by
  imod (ghost_map_alloc_empty (GF := WasmHeapGF host) (K := Nat)
      (V := AllocationMeta) (H := WasmAllocationMap)) with
    ⟨%heapId, Hauth⟩
  imodintro
  iexists heapId
  unfold AllocMetaAuth AllocationHistory.empty
  iexact Hauth

theorem historyWellFormed_empty :
    HistoryWellFormed heapBase.toNat AllocationHistory.empty := by
  simp [HistoryWellFormed, AllocationHistory.empty,
    LawfulPartialMap.get?_empty]

/-- Assemble the initial allocator authority from the physical zero cursor,
the tight frontier fragment, and empty metadata. -/
theorem BumpHeap_empty {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (ownedPages : Nat)
    (hphysical : heapBase.toNat ≤ ownedPages * 65536) :
    pointsTo_u32 0 allocatorCursor 0 ∗
      heapFrontierOwn heapBase.toNat ∗
      AllocMetaAuth heapId AllocationHistory.empty ∗
      memoryPagesOwn ownedPages ⊢
      BumpHeap (host := host) heapId 0 heapBase.toNat
        AllocationHistory.empty := by
  unfold BumpHeap RetiredBytes
  simp only [AllocationHistory.empty, BI.BigSepM.bigSepM_empty.to_eq]
  iintro ⟨Hcursor, Hfrontier, Hmetadata, Hpages⟩
  iframe Hcursor Hfrontier Hmetadata
  isplitl []
  · itrivial
  · iexists ownedPages
    iframe Hpages
    ipureexact ⟨Nat.le_refl _, by decide, by decide, by decide,
      historyWellFormed_empty, hphysical⟩

/-- A token agrees with the unique live metadata entry in the named heap. -/
theorem AllocMetaAuth_token_agree {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout) :
    AllocMetaAuth (host := host) heapId history ∗
      AllocToken heapId allocationId ptr layout ⊢
      iprop(⌜get? history.records allocationId =
        some (liveMeta ptr layout)⌝) := by
  unfold AllocMetaAuth AllocToken
  iintro ⟨Hauth, Htoken⟩
  iapply ghost_map_lookup $$ Hauth Htoken

/-- Extend metadata at `nextId` and return the new exclusive live token. -/
theorem AllocMetaAuth_insert {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hfresh : get? history.records history.nextId = none) :
    AllocMetaAuth (host := host) heapId history ==∗
      AllocMetaAuth heapId (history.allocate ptr layout) ∗
      AllocToken heapId history.nextId ptr layout := by
  unfold AllocMetaAuth AllocToken
  iintro Hauth
  imod ghost_map_insert history.nextId (liveMeta ptr layout) hfresh $$ Hauth with
    ⟨Hauth, Htoken⟩
  imodintro
  isimp only [AllocationHistory.allocate]
  iframe

/-- Atomically change one live metadata entry to retired.  The returned
fragment is linear and must be placed in `RetiredBytes` with the block bytes. -/
theorem AllocMetaAuth_retire {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout) :
    AllocMetaAuth (host := host) heapId history ∗
      AllocToken heapId allocationId ptr layout ==∗
      AllocMetaAuth heapId (history.retire allocationId ptr layout) ∗
      ghost_map_elem heapId (DFrac.own 1) allocationId
        (retiredMeta ptr layout) := by
  unfold AllocMetaAuth AllocToken
  iintro ⟨Hauth, Htoken⟩
  imod ghost_map_update (retiredMeta ptr layout) $$ Hauth Htoken with
    ⟨Hauth, Htoken⟩
  imodintro
  isimp only [AllocationHistory.retire]
  iframe

/-- A fresh live entry contributes `emp`, so allocation preserves all retired
storage ownership. -/
theorem RetiredBytes_insert_live {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hfresh : get? history.records history.nextId = none) :
    RetiredBytes (host := host) heapId history ⊢
      RetiredBytes heapId (history.allocate ptr layout) := by
  unfold RetiredBytes
  change ([∗map] allocationId ↦ metadata ∈ history.records,
      RetiredEntry heapId allocationId metadata) ⊢
    [∗map] allocationId ↦ metadata ∈
      insert history.records history.nextId (liveMeta ptr layout),
      RetiredEntry heapId allocationId metadata
  rw [(BI.BigSepM.bigSepM_insert hfresh).to_eq]
  unfold RetiredEntry liveMeta
  iintro Hretired
  isplitl []
  · itrivial
  · iexact Hretired

/-- Move the fragment returned by `AllocMetaAuth_retire` and the entire live
byte range into the retired-resource map. -/
theorem RetiredBytes_retire {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8)
    (hlookup : get? history.records allocationId =
      some (liveMeta ptr layout)) :
    RetiredBytes (host := host) heapId history ∗
      ghost_map_elem heapId (DFrac.own 1) allocationId
        (retiredMeta ptr layout) ∗
      ByteSlice ptr bytes ∗
      ⌜bytes.length = layout.size⌝ ⊢
      RetiredBytes heapId (history.retire allocationId ptr layout) := by
  unfold RetiredBytes
  isimp only [AllocationHistory.retire]
  iintro ⟨Hretired, Hfragment, Hbytes, %hlen⟩
  ihave ⟨Hold, Hclose⟩ :=
    BI.BigSepM.bigSepM_insert_acc hlookup $$ Hretired
  isimp only [RetiredEntry, liveMeta] at Hold
  iclear Hold
  ispecialize Hclose $$ %(retiredMeta ptr layout)
  iapply Hclose
  unfold RetiredEntry retiredMeta
  isplitl_exact Hfragment
  · iexists bytes
    iframe Hbytes
    ipureintro
    simpa [retiredMeta] using hlen

/-- The complete metadata-side allocation transition.  Physical fresh-byte
ownership is deliberately supplied separately by `stateInterp_alloc_freshRange`. -/
theorem AllocatorResources_insert {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hfresh : get? history.records history.nextId = none) :
    AllocMetaAuth (host := host) heapId history ∗
      RetiredBytes heapId history ==∗
      AllocMetaAuth heapId (history.allocate ptr layout) ∗
      RetiredBytes heapId (history.allocate ptr layout) ∗
      AllocToken heapId history.nextId ptr layout := by
  iintro ⟨Hauth, Hretired⟩
  imod AllocMetaAuth_insert heapId history ptr layout hfresh $$ Hauth with
    ⟨Hauth, Htoken⟩
  ihave HretiredNew := RetiredBytes_insert_live heapId history ptr layout
    hfresh $$ Hretired
  imodintro
  iframe

/-- Assemble the allocator's exact post-commit resources.  The caller supplies
the cursor word and frontier fragment *after* the Wasm store and sparse-range
state update; this lemma performs only the metadata update and representation
reassembly. -/
theorem BumpHeap_commit {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (frontier : Nat) (history : AllocationHistory)
    (base finish : UInt32) (layout : AllocLayout) (bytes : List UInt8)
    (ownedPages : Nat)
    (hheapBase : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hbytesLength : bytes.length = layout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    pointsTo_u32 0 allocatorCursor finish ∗
      heapFrontierOwn finish.toNat ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      ByteSlice base bytes ==∗
      BumpHeap heapId finish finish.toNat
          (history.allocate base layout) ∗
        LiveBlock heapId history.nextId base layout bytes := by
  rcases classifyBump_success_reachable frontier layout base finish
      hheapBase hvalid halignment hclassify with
    ⟨hstart, hnonnull, haligned, _hendWord, hendSigned,
      hfinish, hmetadata⟩
  have hfresh : get? history.records history.nextId = none :=
    hwf.2.2.2.1
  have hwfNew :
      HistoryWellFormed finish.toNat (history.allocate base layout) := by
    rw [hfinish]
    exact HistoryWellFormed.allocate frontier history base layout hwf
      hmetadata hstart
  have hbaseNatNe : base.toNat ≠ 0 := by
    intro hzero
    apply hnonnull
    apply UInt32.toNat_inj.mp
    simpa using hzero
  have hfinishPositive : 0 < finish.toNat := by
    rw [hfinish]
    omega
  have hfinishSigned : finish.toNat < 2147483648 := by
    rw [hfinish]
    exact hendSigned
  have hfinishNonzero : finish ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    simp only [UInt32.toNat_zero] at hzeroNat
    omega
  iintro ⟨Hcursor, Hfrontier, Hauth, Hretired, Hpages, Hbytes⟩
  imod AllocatorResources_insert heapId history base layout hfresh $$
      [Hauth Hretired] with ⟨Hauth, Hretired, Htoken⟩
  · iframe
  imodintro
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe
    ipureintro
    refine ⟨by omega, hfinishSigned, ?_, ?_, hwfNew, hphysical⟩
    · constructor
      · intro hzero
        exact (hfinishNonzero hzero).elim
      · intro hzero
        simp only [AllocationHistory.allocate] at hzero
        omega
    · intro _hnonzero
      rfl
  · unfold LiveBlock
    iframe Htoken Hbytes
    ipureexact ⟨hbytesLength, hnonnull, haligned⟩

/-- Retirement with the agreement fact needed to update pure history. -/
theorem AllocMetaAuth_retire_with_lookup {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout) :
    AllocMetaAuth (host := host) heapId history ∗
      AllocToken heapId allocationId ptr layout ==∗
      AllocMetaAuth heapId (history.retire allocationId ptr layout) ∗
      ghost_map_elem heapId (DFrac.own 1) allocationId
        (retiredMeta ptr layout) ∗
      ⌜get? history.records allocationId =
        some (liveMeta ptr layout)⌝ := by
  iintro ⟨Hauth, Htoken⟩
  ihave %hlookup : ⌜get? history.records allocationId =
      some (liveMeta ptr layout)⌝ $$ [Hauth Htoken]
  · iapply_frame AllocMetaAuth_token_agree
  imod AllocMetaAuth_retire heapId history allocationId ptr layout $$
      [Hauth Htoken] with ⟨Hauth, Hfragment⟩
  · iframe
  imodintro
  iframe
  ipureexact hlookup

/-- The no-op physical deallocator consumes a complete live block and moves
its bytes and exclusive metadata fragment into allocator-owned retired state. -/
theorem AllocatorResources_retire {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8) :
    AllocMetaAuth (host := host) heapId history ∗
      RetiredBytes heapId history ∗
      LiveBlock heapId allocationId ptr layout bytes ==∗
      AllocMetaAuth heapId (history.retire allocationId ptr layout) ∗
      RetiredBytes heapId (history.retire allocationId ptr layout) := by
  unfold LiveBlock
  iintro ⟨Hauth, Hretired, Htoken, Hbytes, %hfacts⟩
  icombine Hauth Htoken as Hmetadata
  imod AllocMetaAuth_retire_with_lookup heapId history allocationId ptr
      layout $$ Hmetadata with ⟨Hauth, Hfragment, %hlookup⟩
  ihave HretiredNew := RetiredBytes_retire heapId history allocationId ptr
      layout bytes hlookup $$ [Hretired Hfragment Hbytes]
  · iframe
    ipureexact hfacts.1
  imodintro
  iframe

/-- The complete logical effect of the generated no-op deallocator: cursor
and frontier stay fixed, while the live token and bytes move exactly once into
the retired portion of `BumpHeap`. -/
theorem BumpHeap_retire {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8) :
    BumpHeap (host := host) heapId storedCursor frontier history ∗
      LiveBlock heapId allocationId ptr layout bytes ==∗
      BumpHeap heapId storedCursor frontier
        (history.retire allocationId ptr layout) := by
  iintro ⟨Hbump, Hblock⟩
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hblock⟩
  ihave %hlookup : ⌜get? history.records allocationId =
      some (liveMeta ptr layout)⌝ $$ [Hauth Htoken]
  · iapply_frame AllocMetaAuth_token_agree
  have hwfNew := HistoryWellFormed.retire frontier history allocationId ptr
    layout hheap.2.2.2.2.1 hlookup
  imod AllocatorResources_retire heapId history allocationId ptr layout bytes
      $$ [Hauth Hretired Htoken Hbytes] with ⟨Hauth, Hretired⟩
  · unfold LiveBlock
    iframe
    ipureexact hblock
  imodintro
  unfold BumpHeap
  iframe
  ipureexact ⟨hheap.1, hheap.2.1, by
      simpa only [AllocationHistory.retire] using hheap.2.2.1,
    hheap.2.2.2.1, hwfNew, hheap.2.2.2.2.2⟩

/-! ## Stack, host, and runtime ownership -/

/-- Ownership of mutable Wasm global zero, the Rust shadow-stack pointer. -/
def StackPointer [WasmGlobalGS Universal.State]
    (sp : UInt32) : IProp (WasmHeapGF Universal.State) :=
  globalPointsToAt 0 0 (.i32 sp)

/-- A raw initialized stack region. -/
abbrev StackRegion [WasmHeapGS Universal.State]
    (low : UInt32) (bytes : List UInt8) : IProp (WasmHeapGF Universal.State) :=
  ByteSlice low bytes

/-- The 272-byte raw export frame before its structured fields are opened. -/
def RawExportRegion [WasmHeapGS Universal.State]
    (base : UInt32) : IProp (WasmHeapGF Universal.State) :=
  OwnedRegion base 272

/-- The sixteen bytes used by `func1` below the driver's visible frame. -/
def StackReserve [WasmHeapGS Universal.State]
    (low : UInt32) (bytes : List UInt8) : IProp (WasmHeapGF Universal.State) :=
  iprop(⌜bytes.length = 16⌝ ∗ ByteSlice low bytes)

/-- The exact four-byte prefix and twelve-byte result area used by `func1`
after decrementing the shadow-stack pointer. -/
theorem StackReserve_split
    [WasmHeapGS Universal.State]
    (low : UInt32) (bytes : List UInt8) :
    StackReserve low bytes ⊣⊢
      iprop(∃ headBytes : List UInt8, ∃ growBefore : List UInt8,
        ⌜bytes = headBytes ++ growBefore ∧
          headBytes.length = 4 ∧ growBefore.length = 12⌝ ∗
        ByteSlice low headBytes ∗
        ByteSlice (low + UInt32.ofNat headBytes.length) growBefore) := by
  constructor
  · iintro Hreserve
    isimp only [StackReserve] at Hreserve
    icases Hreserve with ⟨%hlength, Hbytes⟩
    let headBytes := bytes.take 4
    let growBefore := bytes.drop 4
    have hdecompose : bytes = headBytes ++ growBefore := by
      dsimp only [headBytes, growBefore]
      exact (List.take_append_drop 4 bytes).symm
    have hheadLength : headBytes.length = 4 := by
      simp [headBytes, hlength]
    have hgrowLength : growBefore.length = 12 := by
      simp [growBefore, hlength]
    ihave Hsplit : ByteSlice low (headBytes ++ growBefore) $$ [Hbytes]
    · irw_exact [← hdecompose] with Hbytes
    icases (ByteSlice_append low headBytes growBefore).mp $$ Hsplit with
      ⟨Hhead, Hgrow⟩
    iexists headBytes, growBefore
    isplitr_pureexact ⟨hdecompose, hheadLength, hgrowLength⟩
    · iframe
  · iintro ⟨%headBytes, %growBefore, %hfacts, Hhead, Hgrow⟩
    unfold StackReserve
    isplitl []
    · ipureintro
      rw [hfacts.1, List.length_append, hfacts.2.1, hfacts.2.2]
    · rw [hfacts.1]
      iapply_frame (ByteSlice_append low headBytes growBefore).mpr

/-- Reversible split of the exported function's full 288-byte entry stack
ownership into the 16-byte reserve and 272-byte visible driver frame. -/
theorem EntryStack_split
    [WasmHeapGS Universal.State]
    (bytes : List UInt8) :
    iprop(StackRegion entryStackLow bytes ∗ ⌜bytes.length = 288⌝) ⊣⊢
      iprop(∃ reserveBytes : List UInt8, ∃ frameBytes : List UInt8,
        ⌜bytes = reserveBytes ++ frameBytes ∧
          reserveBytes.length = 16 ∧ frameBytes.length = 272⌝ ∗
        StackReserve reserveBase reserveBytes ∗
        ByteSlice driverBase frameBytes) := by
  have hlow : entryStackLow = reserveBase := by decide
  have hboundary :
      entryStackLow + UInt32.ofNat 16 = driverBase := by decide
  constructor
  · iintro ⟨Hstack, %hlength⟩
    let reserveBytes := bytes.take 16
    let frameBytes := bytes.drop 16
    have hdecompose : bytes = reserveBytes ++ frameBytes := by
      dsimp only [reserveBytes, frameBytes]
      exact (List.take_append_drop 16 bytes).symm
    have hreserveLength : reserveBytes.length = 16 := by
      simp [reserveBytes, hlength]
    have hframeLength : frameBytes.length = 272 := by
      simp [frameBytes, hlength]
    ihave Hsplit :
        ByteSlice entryStackLow (reserveBytes ++ frameBytes) $$ [Hstack]
    · irw_exact [← hdecompose] with Hstack
    icases (ByteSlice_append entryStackLow reserveBytes frameBytes).mp $$
        Hsplit with ⟨Hreserve, Hframe⟩
    ihave Hreserve' : StackReserve reserveBase reserveBytes $$ [Hreserve]
    · unfold StackReserve
      isplitl_pureexact hreserveLength
      · irw_exact [← hlow] with Hreserve
    ihave Hframe' : ByteSlice driverBase frameBytes $$ [Hframe]
    · irw_exact [← hboundary, hreserveLength] with Hframe
    iexists reserveBytes, frameBytes
    isplitr_pureexact ⟨hdecompose, hreserveLength, hframeLength⟩
    · iframe
  · iintro ⟨%reserveBytes, %frameBytes, %hfacts, Hreserve, Hframe⟩
    isimp only [StackReserve] at Hreserve
    icases Hreserve with ⟨%hreserveLength, Hreserve⟩
    ihave Hreserve' : ByteSlice entryStackLow reserveBytes $$ [Hreserve]
    · irw_exact [hlow] with Hreserve
    ihave Hframe' :
        ByteSlice (entryStackLow + UInt32.ofNat reserveBytes.length)
          frameBytes $$ [Hframe]
    · irw_exact [hreserveLength, hboundary] with Hframe
    isplitl [Hreserve' Hframe']
    · rw [hfacts.1]
      iapply_frame (ByteSlice_append entryStackLow reserveBytes frameBytes).mpr
    · ipureintro
      rw [hfacts.1, List.length_append, hfacts.2.1, hfacts.2.2]

/-- Reassemble the driver's raw entry-stack ownership after its structured
frame resources have been reduced back to bytes. -/
theorem StackReserve_combineFrame
    [WasmHeapGS Universal.State]
    (reserveBytes frameBytes : List UInt8)
    (hframeLength : frameBytes.length = 272) :
    StackReserve reserveBase reserveBytes ∗
      ByteSlice driverBase frameBytes ⊢
      iprop(StackRegion entryStackLow (reserveBytes ++ frameBytes) ∗
        ⌜(reserveBytes ++ frameBytes).length = 288⌝) := by
  iintro ⟨Hreserve, Hframe⟩
  isimp only [StackReserve] at Hreserve
  icases Hreserve with ⟨%hreserveLength, HreserveBytes⟩
  ihave Hreserve : StackReserve reserveBase reserveBytes $$ [HreserveBytes]
  · unfold StackReserve
    isplitl_pureexact hreserveLength
    · iexact HreserveBytes
  iapply (EntryStack_split (reserveBytes ++ frameBytes)).mpr
  iexists reserveBytes, frameBytes
  isplitr_pureexact ⟨rfl, hreserveLength, hframeLength⟩
  · iframe

/-- Reversible byte-level layout of the visible 272-byte driver frame: the
three-word Vec header, 256-byte read buffer, and four-byte output slot. -/
theorem DriverFrame_split
    [WasmHeapGS Universal.State]
    (bytes : List UInt8) (hlength : bytes.length = 272) :
    ByteSlice driverBase bytes ⊣⊢
      iprop(∃ headerBytes : List UInt8, ∃ chunkBytes : List UInt8,
        ∃ outputBytes : List UInt8,
        ⌜bytes = headerBytes ++ chunkBytes ++ outputBytes ∧
          headerBytes.length = 12 ∧ chunkBytes.length = 256 ∧
          outputBytes.length = 4⌝ ∗
        ByteSlice driverBase headerBytes ∗
        ByteSlice (driverBase + 12) chunkBytes ∗
        ByteSlice (driverBase + 268) outputBytes) := by
  have hchunkBase :
      driverBase + UInt32.ofNat 12 = driverBase + 12 := by decide
  have houtputBase :
      (driverBase + UInt32.ofNat 12) + UInt32.ofNat 256 =
        driverBase + 268 := by decide
  constructor
  · iintro Hbytes
    let headerBytes := bytes.take 12
    let rest := bytes.drop 12
    let chunkBytes := rest.take 256
    let outputBytes := rest.drop 256
    have hheaderRest : bytes = headerBytes ++ rest := by
      dsimp only [headerBytes, rest]
      exact (List.take_append_drop 12 bytes).symm
    have hchunkOutput : rest = chunkBytes ++ outputBytes := by
      dsimp only [chunkBytes, outputBytes]
      exact (List.take_append_drop 256 rest).symm
    have hheaderLength : headerBytes.length = 12 := by
      simp [headerBytes, hlength]
    have hrestLength : rest.length = 260 := by
      simp [rest, hlength]
    have hchunkLength : chunkBytes.length = 256 := by
      simp [chunkBytes, hrestLength]
    have houtputLength : outputBytes.length = 4 := by
      simp [outputBytes, hrestLength]
    ihave Hfirst : ByteSlice driverBase (headerBytes ++ rest) $$ [Hbytes]
    · irw_exact [← hheaderRest] with Hbytes
    icases (ByteSlice_append driverBase headerBytes rest).mp $$ Hfirst with
      ⟨Hheader, Hrest⟩
    ihave Hrest' : ByteSlice
        (driverBase + UInt32.ofNat 12) (chunkBytes ++ outputBytes) $$
        [Hrest]
    · irw_exact [← hheaderLength, ← hchunkOutput] with Hrest
    icases (ByteSlice_append (driverBase + UInt32.ofNat 12)
        chunkBytes outputBytes).mp $$ Hrest' with
      ⟨Hchunk, Houtput⟩
    ihave Hchunk' : ByteSlice (driverBase + 12) chunkBytes $$ [Hchunk]
    · irw_exact [← hchunkBase] with Hchunk
    ihave Houtput' : ByteSlice (driverBase + 268) outputBytes $$ [Houtput]
    · irw_exact [← houtputBase, hchunkLength] with Houtput
    iexists headerBytes, chunkBytes, outputBytes
    isplitr_pureexact ⟨by rw [hheaderRest, hchunkOutput, List.append_assoc],
        hheaderLength, hchunkLength, houtputLength⟩
    · iframe
  · iintro ⟨%headerBytes, %chunkBytes, %outputBytes, %hfacts,
        Hheader, Hchunk, Houtput⟩
    ihave Hchunk' : ByteSlice
        (driverBase + UInt32.ofNat headerBytes.length) chunkBytes $$ [Hchunk]
    · irw_exact [hfacts.2.1, hchunkBase] with Hchunk
    ihave Houtput' : ByteSlice
        ((driverBase + UInt32.ofNat headerBytes.length) +
          UInt32.ofNat chunkBytes.length) outputBytes $$ [Houtput]
    · irw_exact [hfacts.2.1, hfacts.2.2.1, houtputBase] with Houtput
    ihave Hrest : ByteSlice
        (driverBase + UInt32.ofNat headerBytes.length)
          (chunkBytes ++ outputBytes) $$ [Hchunk' Houtput']
    · iapply (ByteSlice_append
        (driverBase + UInt32.ofNat headerBytes.length)
        chunkBytes outputBytes).mpr
      iframe
    rw [hfacts.1]
    rw [List.append_assoc]
    iapply (ByteSlice_append driverBase headerBytes
      (chunkBytes ++ outputBytes)).mpr
    iframe

/-- The two-word RawVec header.  The length word at `header + 8` belongs to
`VecU8`, not to this view. -/
def RawVecHeader {host : Type} [WasmHeapGS host]
    (header capacity ptr : UInt32) : IProp (WasmHeapGF host) :=
  iprop(pointsTo_u32 0 header capacity ∗
    pointsTo_u32 0 (header + 4) ptr)

/-- Complete capacity storage independently of the three-word Vec header. -/
def VecStorage {host : Type} [WasmHeapGS host]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) : IProp (WasmHeapGF host) := iprop%
  (⌜capacity = 0 ∧ ptr = 1 ∧ initialized = []⌝) ∨
  (∃ allocationId : Nat, ∃ allBytes spare : List UInt8,
      ⌜0 < capacity.toNat ∧
        initialized.length ≤ capacity.toNat ∧
        allBytes = initialized ++ spare ∧
        spare.length = capacity.toNat - initialized.length⌝ ∗
      LiveBlock heapId allocationId ptr
        { size := capacity.toNat, alignment := 1 } allBytes)

/-- Package a freshly allocated complete byte block as Vec capacity storage
once the allocator has established the initialized-prefix copy. -/
theorem LiveBlock_to_VecStorage {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (capacity ptr : UInt32) (initialized allBytes : List UInt8)
    (hcapacity : 0 < capacity.toNat)
    (hprefix : allBytes.take initialized.length = initialized) :
    LiveBlock (host := host) heapId allocationId ptr
        { size := capacity.toNat, alignment := 1 } allBytes ⊢
      VecStorage heapId capacity ptr initialized := by
  unfold LiveBlock
  iintro ⟨Htoken, Hbytes, %hblock⟩
  have htakeLength := congrArg List.length hprefix
  simp only [List.length_take] at htakeLength
  have hinitialized : initialized.length ≤ allBytes.length := by omega
  let spare := allBytes.drop initialized.length
  have hdecompose : allBytes = initialized ++ spare := by
    calc
      allBytes = allBytes.take initialized.length ++
          allBytes.drop initialized.length :=
        (List.take_append_drop initialized.length allBytes).symm
      _ = initialized ++ spare := by rw [hprefix]
  have hspareLength :
      spare.length = capacity.toNat - initialized.length := by
    simp [spare, hblock.1]
  unfold VecStorage
  iright
  iexists allocationId, allBytes, spare
  isplitr_pureexact ⟨hcapacity, by simpa [hblock.1] using hinitialized,
      hdecompose, hspareLength⟩
  · unfold LiveBlock
    iframe Htoken Hbytes
    ipureexact hblock

/-- Focus the initialized prefix of a nonempty Vec allocation while retaining
the token and spare suffix needed to close the same storage afterwards. -/
theorem VecStorage_initializedFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) (hinitialized : 0 < initialized.length) :
    VecStorage (host := host) heapId capacity ptr initialized ⊢
      iprop(ByteSlice ptr initialized ∗
        (ByteSlice ptr initialized -∗
          VecStorage heapId capacity ptr initialized)) := by
  unfold VecStorage
  iintro (%hempty | Hallocated)
  · rcases hempty with ⟨_hcapacity, _hptr, rfl⟩
    simp at hinitialized
  · icases Hallocated with
      ⟨%allocationId, %allBytes, %spare, %hstorage, Hblock⟩
    isimp only [LiveBlock] at Hblock
    icases Hblock with ⟨Htoken, HallBytes, %hblock⟩
    ihave HallBytes' : ByteSlice ptr (initialized ++ spare) $$ [HallBytes]
    · irw_exact [← hstorage.2.2.1] with HallBytes
    icases (ByteSlice_append ptr initialized spare).mp $$ HallBytes' with
      ⟨Hinitialized, Hspare⟩
    isplitl_exact Hinitialized
    · iintro Hinitialized
      ihave HallBytes : ByteSlice ptr (initialized ++ spare) $$
          [Hinitialized Hspare]
      · iapply_frame (ByteSlice_append ptr initialized spare).mpr
      iright
      iexists allocationId, initialized ++ spare, spare
      isplitr_pureexact ⟨hstorage.1, hstorage.2.1, rfl, hstorage.2.2.2⟩
      · unfold LiveBlock
        iframe Htoken HallBytes
        ipureexact ⟨by
          simp only [List.length_append, hstorage.2.2.2]
          omega, hblock.2.1, hblock.2.2⟩

/-- Focus exactly the spare-capacity subrange filled by the driver's append
copy.  Returning the current chunk reassembles the same live allocation with
the longer initialized prefix and unchanged trailing spare ownership. -/
theorem VecStorage_appendFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized current : List UInt8)
    (hcurrent : 0 < current.length)
    (hfits : current.length ≤ capacity.toNat - initialized.length) :
    VecStorage (host := host) heapId capacity ptr initialized ⊢
      iprop(∃ oldChunk : List UInt8,
        ⌜oldChunk.length = current.length⌝ ∗
        ByteSlice (ptr + UInt32.ofNat initialized.length) oldChunk ∗
        (ByteSlice (ptr + UInt32.ofNat initialized.length) current -∗
          VecStorage heapId capacity ptr (initialized ++ current))) := by
  unfold VecStorage
  iintro (%hempty | Hallocated)
  · rcases hempty with ⟨rfl, _hptr, rfl⟩
    simp only [UInt32.toNat_zero, Nat.zero_sub] at hfits
    omega
  · icases Hallocated with
      ⟨%allocationId, %allBytes, %spare, %hstorage, Hblock⟩
    isimp only [LiveBlock] at Hblock
    icases Hblock with ⟨Htoken, HallBytes, %hblock⟩
    let oldChunk := spare.take current.length
    let tail := spare.drop current.length
    have hchunkLength : oldChunk.length = current.length := by
      simp [oldChunk, hstorage.2.2.2, hfits]
    have hdecompose : spare = oldChunk ++ tail := by
      dsimp only [oldChunk, tail]
      exact (List.take_append_drop current.length spare).symm
    have htailLength :
        tail.length = capacity.toNat -
          (initialized.length + current.length) := by
      simp [tail, hstorage.2.2.2]
      omega
    ihave HallBytes' : ByteSlice ptr (initialized ++ spare) $$ [HallBytes]
    · irw_exact [← hstorage.2.2.1] with HallBytes
    icases (ByteSlice_append ptr initialized spare).mp $$ HallBytes' with
      ⟨Hinitialized, Hspare⟩
    ihave Hspare' : ByteSlice
        (ptr + UInt32.ofNat initialized.length) (oldChunk ++ tail) $$
        [Hspare]
    · irw_exact [← hdecompose] with Hspare
    icases (ByteSlice_append
        (ptr + UInt32.ofNat initialized.length) oldChunk tail).mp $$
        Hspare' with ⟨Hchunk, Htail⟩
    iexists oldChunk
    isplitr_pureexact hchunkLength
    isplitl_exact Hchunk
    iintro Hcurrent
    ihave Htail' : ByteSlice
        ((ptr + UInt32.ofNat initialized.length) +
          UInt32.ofNat current.length) tail $$ [Htail]
    · irw_exact [← hchunkLength] with Htail
    ihave HspareNew : ByteSlice
        (ptr + UInt32.ofNat initialized.length) (current ++ tail) $$
        [Hcurrent Htail']
    · iapply (ByteSlice_append
        (ptr + UInt32.ofNat initialized.length) current tail).mpr
      iframe
    ihave HallBytesNew :
        ByteSlice ptr (initialized ++ current ++ tail) $$
        [Hinitialized HspareNew]
    · rw [List.append_assoc]
      iapply_frame (ByteSlice_append ptr initialized (current ++ tail)).mpr
    have hnewLength :
        (initialized ++ current ++ tail).length = capacity.toNat := by
      simp only [List.length_append]
      omega
    have hnewInitialized :
        (initialized ++ current).length ≤ capacity.toNat := by
      simp only [List.length_append] at hnewLength ⊢
      omega
    iright
    iexists allocationId, initialized ++ current ++ tail, tail
    isplitr_pureexact ⟨hstorage.1, hnewInitialized, rfl, by
        simpa only [List.length_append] using htailLength⟩
    · unfold LiveBlock
      iframe Htoken HallBytesNew
      ipureexact ⟨hnewLength, hblock.2.1, hblock.2.2⟩

/-- Complete three-word byte Vec plus its whole live allocation. -/
def VecU8 {host : Type} [WasmHeapGS host]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8) : IProp (WasmHeapGF host) := iprop%
  RawVecHeader header capacity ptr ∗
    pointsTo_u32 0 (header + 8) (UInt32.ofNat initialized.length) ∗
    VecStorage heapId capacity ptr initialized

/-- Canonical bytes of the three Vec fields owned in the driver frame. -/
def vecHeaderBytes (capacity ptr : UInt32)
    (initialized : List UInt8) : List UInt8 :=
  serialize [capacity, ptr, UInt32.ofNat initialized.length]

@[simp] theorem vecHeaderBytes_length
    (capacity ptr : UInt32) (initialized : List UInt8) :
    (vecHeaderBytes capacity ptr initialized).length = 12 := by
  unfold vecHeaderBytes
  rw [serialize_length]
  norm_num

/-- Reversible split between the Vec's three stack-resident words and its
allocation storage.  This is the ownership boundary used when `func3`
deallocates only the storage and later restores the raw stack frame. -/
theorem VecU8_as_headerBytes_storage {host : Type} [WasmHeapGS host]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8)
    (hheader : header.toNat + 12 < UInt32.size) :
    VecU8 heapId header capacity ptr initialized ⊣⊢
      iprop(ByteSlice header (vecHeaderBytes capacity ptr initialized) ∗
        VecStorage heapId capacity ptr initialized) := by
  have haddress : (header + 4) + 4 = header + 8 := by
    bv_decide
  constructor
  · iintro Hvec
    isimp only [VecU8, RawVecHeader] at Hvec
    icases Hvec with
      ⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩
    ihave Hlength' : pointsTo_u32 0 ((header + 4) + 4)
        (UInt32.ofNat initialized.length) $$ [Hlength]
    · irw_exact [haddress] with Hlength
    ihave Harray : arrayAt 0 header
        [capacity, ptr, UInt32.ofNat initialized.length] $$
        [Hcapacity Hpointer Hlength']
    · isimp only [arrayAt]
      iframe
    ihave Hbytes : WordCells header
        [capacity, ptr, UInt32.ofNat initialized.length] $$ [Harray]
    · iapply (arrayAt_eq_wordCells header
          [capacity, ptr, UInt32.ofNat initialized.length]).mp
      iexact Harray
    isplitl [Hbytes]
    · unfold ByteSlice
      isplitl []
      · ipureintro
        unfold vecHeaderBytes
        rw [serialize_length]
        norm_num
        exact hheader
      · unfold vecHeaderBytes
        iexact Hbytes
    · iexact Hstorage
  · iintro ⟨Hheader, Hstorage⟩
    isimp only [ByteSlice, vecHeaderBytes] at Hheader
    icases Hheader with ⟨%_hnowrap, Hbytes⟩
    ihave Harray : arrayAt 0 header
        [capacity, ptr, UInt32.ofNat initialized.length] $$ [Hbytes]
    · iapply (arrayAt_eq_wordCells header
          [capacity, ptr, UInt32.ofNat initialized.length]).mpr
      iexact Hbytes
    isimp only [arrayAt] at Harray
    icases Harray with ⟨Hcapacity, Hpointer, Hlength⟩
    icases Hlength with ⟨Hlength, _Hemp⟩
    ihave Hlength' : pointsTo_u32 0 (header + 8)
        (UInt32.ofNat initialized.length) $$ [Hlength]
    · irw_exact [← haddress] with Hlength
    unfold VecU8 RawVecHeader
    iframe

/-- Deliberately transparent decomposition used by reserve, append, and
deallocation call sites. -/
theorem VecU8_open {host : Type} [WasmHeapGS host]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8) :
    VecU8 (host := host) heapId header capacity ptr initialized ⊣⊢
      iprop(RawVecHeader header capacity ptr ∗
        pointsTo_u32 0 (header + 8) (UInt32.ofNat initialized.length) ∗
        VecStorage heapId capacity ptr initialized) :=
  .rfl

/-- Driver copy-source view of a nonempty Vec: expose only its initialized
prefix and close back to the identical complete `VecU8`. -/
theorem VecU8_initializedFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8) (hinitialized : 0 < initialized.length) :
    VecU8 (host := host) heapId header capacity ptr initialized ⊢
      iprop(ByteSlice ptr initialized ∗
        (ByteSlice ptr initialized -∗
          VecU8 heapId header capacity ptr initialized)) := by
  unfold VecU8
  iintro ⟨Hheader, Hlength, Hstorage⟩
  ihave ⟨Hinitialized, Hclose⟩ := VecStorage_initializedFocus heapId capacity ptr initialized
    hinitialized $$ Hstorage
  isplitl_exact Hinitialized
  · iintro Hinitialized
    ihave Hstorage := Hclose $$ Hinitialized
    iframe

/-- Driver-side append view: focus the spare bytes and Vec length word, then
reassemble the exact longer `VecU8` after the copy and length store. -/
theorem VecU8_appendFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized current : List UInt8)
    (hcurrent : 0 < current.length)
    (hfits : current.length ≤ capacity.toNat - initialized.length) :
    VecU8 (host := host) heapId header capacity ptr initialized ⊢
      iprop(∃ oldChunk : List UInt8,
        ⌜oldChunk.length = current.length⌝ ∗
        ByteSlice (ptr + UInt32.ofNat initialized.length) oldChunk ∗
        pointsTo_u32 0 (header + 8) (UInt32.ofNat initialized.length) ∗
        (ByteSlice (ptr + UInt32.ofNat initialized.length) current -∗
         pointsTo_u32 0 (header + 8)
            (UInt32.ofNat (initialized ++ current).length) -∗
          VecU8 heapId header capacity ptr (initialized ++ current))) := by
  unfold VecU8
  iintro ⟨Hheader, Hlength, Hstorage⟩
  ihave ⟨%oldChunk, %hchunkLength, Hchunk, Hclose⟩ := VecStorage_appendFocus heapId capacity ptr
    initialized current hcurrent hfits $$ Hstorage
  iexists oldChunk
  isplitr_pureexact hchunkLength
  isplitl_exacts [Hchunk Hlength]
  iintro Hcurrent
  iintro Hlength
  ihave Hstorage := Hclose $$ Hcurrent
  iframe

/-- Exact bytes installed by the driver's initial three Vec-field stores. -/
def emptyVecHeaderBytes : List UInt8 := serialize [0, 1, 0]

/-- Turn those three initialized words into the canonical empty Vec
representation; no allocation token or heap bytes are invented. -/
theorem emptyVecHeaderBytes_to_VecU8 {host : Type} [WasmHeapGS host]
    (heapId : GName) :
    ByteSlice (host := host) driverBase emptyVecHeaderBytes ⊢
      VecU8 heapId driverBase 0 1 [] := by
  unfold ByteSlice emptyVecHeaderBytes
  iintro ⟨%_hnowrap, Hbytes⟩
  ihave Harray : arrayAt 0 driverBase [0, 1, 0] $$ [Hbytes]
  · iapply (arrayAt_eq_wordCells driverBase [0, 1, 0]).mpr
    iexact Hbytes
  isimp only [arrayAt] at Harray
  icases Harray with ⟨Hcapacity, Hpointer, Hlength⟩
  icases Hlength with ⟨Hlength, _Hemp⟩
  ihave Hlength' : pointsTo_u32 0 (driverBase + 8) 0 $$ [Hlength]
  · have haddress : (driverBase + 4) + 4 = driverBase + 8 := by decide
    irw_exact [← haddress] with Hlength
  unfold VecU8 RawVecHeader
  isplitl [Hcapacity Hpointer]
  · iframe
  isplitl_exact Hlength'
  · unfold VecStorage
    ileft
    ipureexact ⟨rfl, rfl, rfl⟩

/-- Driver-frame ownership after initialization.  Its three parts are
disjoint by separation and together cover exactly the visible 272 bytes. -/
def ExportFrame [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized chunkBytes outputBytes : List UInt8) :
    IProp (WasmHeapGF Universal.State) := iprop%
  VecU8 heapId driverBase capacity ptr initialized ∗
    ByteSlice (driverBase + 12) chunkBytes ∗
    ByteSlice (driverBase + 268) outputBytes ∗
    ⌜chunkBytes.length = 256 ∧ outputBytes.length = 4⌝

/-- Focus a completed nonempty input Vec as its canonical source word array
without losing the allocation token, spare capacity, header, chunk, or output
slot needed to reseal the exact `ExportFrame`. -/
theorem ExportFrame_completedWordsFocus
    [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (original : List UInt32) (chunkBytes outputBytes : List UInt8)
    (horiginal : original ≠ []) (halign : ptr.toNat % 4 = 0) :
    ExportFrame heapId capacity ptr (serialize original) chunkBytes
        outputBytes ⊢
      iprop(WordSlice ptr original ∗
        (WordSlice ptr original -∗
          ExportFrame heapId capacity ptr (serialize original) chunkBytes
            outputBytes)) := by
  have hpositive : 0 < (serialize original).length := by
    rw [serialize_length]
    have := List.length_pos_iff_ne_nil.mpr horiginal
    omega
  unfold ExportFrame
  iintro ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
  ihave ⟨Hbytes, Hclose⟩ := VecU8_initializedFocus heapId driverBase capacity ptr
    (serialize original) hpositive $$ Hvec
  ihave Hwords := (ByteSlice_serialize_as_WordSlice ptr original halign).mp $$
    Hbytes
  isplitl_exact Hwords
  · iintro Hwords
    ihave Hbytes := (ByteSlice_serialize_as_WordSlice ptr original halign).mpr $$
      Hwords
    ihave Hvec := Hclose $$ Hbytes
    iframe Hvec Hchunk Houtput
    ipureexact hframeLengths

/-- Exact raw byte list left in the visible driver frame once the Vec's
separate allocation-storage ownership is removed. -/
def exportFrameBytes (capacity ptr : UInt32)
    (initialized chunkBytes outputBytes : List UInt8) : List UInt8 :=
  vecHeaderBytes capacity ptr initialized ++ chunkBytes ++ outputBytes

/-- Release only the Vec allocation-storage component while retaining every
stack-resident byte of the initialized driver frame.  The storage may then be
passed to `func7`; the raw frame bytes remain available for stack restoration. -/
theorem ExportFrame_releaseStorage [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized chunkBytes outputBytes : List UInt8) :
    ExportFrame heapId capacity ptr initialized chunkBytes outputBytes ⊢
      iprop(VecStorage heapId capacity ptr initialized ∗
        ByteSlice driverBase
          (exportFrameBytes capacity ptr initialized chunkBytes outputBytes) ∗
        ⌜(exportFrameBytes capacity ptr initialized chunkBytes outputBytes).length =
          272⌝) := by
  have hheader : driverBase.toNat + 12 < UInt32.size := by decide
  unfold ExportFrame
  iintro ⟨Hvec, Hchunk, Houtput, %hframeParts⟩
  icases (VecU8_as_headerBytes_storage heapId driverBase capacity ptr
      initialized hheader).mp $$ Hvec with ⟨Hheader, Hstorage⟩
  have hframeLength :
      (exportFrameBytes capacity ptr initialized chunkBytes outputBytes).length =
        272 := by
    simp [exportFrameBytes, hframeParts.1, hframeParts.2]
  ihave Hframe : ByteSlice driverBase
      (exportFrameBytes capacity ptr initialized chunkBytes outputBytes) $$
      [Hheader Hchunk Houtput]
  · iapply (DriverFrame_split
      (exportFrameBytes capacity ptr initialized chunkBytes outputBytes)
      hframeLength).mpr
    iexists vecHeaderBytes capacity ptr initialized, chunkBytes, outputBytes
    isplitr_pureexact ⟨rfl, vecHeaderBytes_length capacity ptr initialized,
        hframeParts.1, hframeParts.2⟩
    · iframe
  iframe Hstorage Hframe
  ipureexact hframeLength

/-- Assemble the initialized driver frame from its exact three disjoint byte
regions. -/
theorem ExportFrame_empty [WasmHeapGS Universal.State]
    (heapId : GName) (chunkBytes outputBytes : List UInt8)
    (hchunk : chunkBytes.length = 256)
    (houtput : outputBytes.length = 4) :
    ByteSlice driverBase emptyVecHeaderBytes ∗
      ByteSlice (driverBase + 12) chunkBytes ∗
      ByteSlice (driverBase + 268) outputBytes ⊢
      ExportFrame heapId 0 1 [] chunkBytes outputBytes := by
  iintro ⟨Hheader, Hchunk, Houtput⟩
  ihave Hvec := emptyVecHeaderBytes_to_VecU8 heapId $$ Hheader
  unfold ExportFrame
  iframe
  ipureexact ⟨hchunk, houtput⟩

/-! ## Pure Vec-growth lineage -/

def selectedCapacity (length additional capacity : Nat) : Nat :=
  max (length + additional) (max (2 * capacity) 8)

def vectorBlockBase (exponent : Nat) : Nat :=
  heapBase.toNat + (2 ^ exponent - 256)

def geometricMetadata (topExponent allocationId : Nat) : AllocationMeta :=
  let exponent := allocationId + 8
  { ptr := UInt32.ofNat (vectorBlockBase exponent)
    size := 2 ^ exponent
    alignment := 1
    status := if exponent = topExponent then .live else .retired }

def geometricRecords (topExponent : Nat) :
    WasmAllocationMap AllocationMeta :=
  (List.range (topExponent - 7)).foldl
    (fun records allocationId =>
      insert records allocationId
        (geometricMetadata topExponent allocationId))
    (∅ : WasmAllocationMap AllocationMeta)

def geometricHistory (topExponent : Nat) : AllocationHistory :=
  { records := geometricRecords topExponent
    nextId := topExponent - 7 }

def shortHistory (capacity : Nat) : AllocationHistory :=
  { records := insert (∅ : WasmAllocationMap AllocationMeta) 0
      (liveMeta heapBase { size := capacity, alignment := 1 })
    nextId := 1 }

/-- Pure metadata relation exposed by the successful reachable `func1`
specialization.  The empty Vec allocates its first block; a nonempty Vec
reallocates whichever live block its linear ownership identifies. -/
def VecReserveHistory (history finalHistory : AllocationHistory)
    (oldCapacity oldPtr newPtr : UInt32)
    (newLayout : AllocLayout) : Prop :=
  if oldCapacity = 0 then
    finalHistory = history.allocate newPtr newLayout
  else
    ∃ oldId,
      get? history.records oldId = some
        (liveMeta oldPtr
          { size := oldCapacity.toNat, alignment := 1 }) ∧
      finalHistory = history.reallocate oldId oldPtr
        { size := oldCapacity.toNat, alignment := 1 } newPtr newLayout

private theorem foldl_insert_congr
    {V : Type} (xs : List Nat)
    (f g : Nat → V)
    (hfg : ∀ x, x ∈ xs → f x = g x)
    (initial : WasmAllocationMap V) :
    xs.foldl (fun records x => insert records x (f x)) initial =
      xs.foldl (fun records x => insert records x (g x)) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [hfg x (by simp)]
      apply ih
      intro y hy
      exact hfg y (by simp [hy])

private theorem insert_overwrite_commute
    {V : Type} (records : WasmAllocationMap V)
    (n : Nat) (old new retired : V) :
    insert (insert (insert records n old) (n + 1) new) n retired =
      insert (insert records n retired) (n + 1) new := by
  apply equiv_iff_eq.mp
  intro key
  simp only [LawfulPartialMap.get?_insert]
  by_cases hn : n = key
  · subst key
    simp
  · by_cases hnext : n + 1 = key
    · subst key
      simp
    · simp [hn, hnext]

private theorem foldl_insert_range_lookup
    {V : Type} (n key : Nat) (f : Nat → V) :
    get? ((List.range n).foldl
      (fun records allocationId =>
        insert records allocationId (f allocationId))
      (∅ : WasmAllocationMap V)) key =
      if key < n then some (f key) else none := by
  induction n with
  | zero => simp [LawfulPartialMap.get?_empty]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hkey : n = key
      · subst key
        rw [get?_insert_eq rfl]
        simp
      · rw [get?_insert_ne hkey, ih]
        by_cases hlt : key < n
        · have hsucc : key < n + 1 := by omega
          simp [hlt, hsucc]
        · have hge : n < key := by omega
          simp [hlt, hge]

/-- Exact lookup formula for the canonical geometric allocation map. -/
theorem geometricRecords_lookup (topExponent allocationId : Nat) :
    get? (geometricRecords topExponent) allocationId =
      if allocationId < topExponent - 7 then
        some (geometricMetadata topExponent allocationId)
      else none := by
  unfold geometricRecords
  exact foldl_insert_range_lookup _ _ _

/-- In the canonical geometric lineage, the only live record for the current
block is the most recently allocated one. -/
theorem geometricHistory_live_unique
    (exponent oldId : Nat) (hexponent : 8 ≤ exponent)
    (hlookup :
      get? (geometricHistory exponent).records oldId =
        some (liveMeta (UInt32.ofNat (vectorBlockBase exponent))
          { size := 2 ^ exponent, alignment := 1 })) :
    oldId = exponent - 8 := by
  unfold geometricHistory at hlookup
  rw [geometricRecords_lookup] at hlookup
  split at hlookup
  · rename_i hlt
    injection hlookup with hmetadata
    have hstatus := congrArg AllocationMeta.status hmetadata
    simp only [geometricMetadata, liveMeta] at hstatus
    split at hstatus
    · rename_i heq
      omega
    · cases hstatus
  · contradiction

/-- The exact live-record lookup used when the Vec reallocates a geometric
block. -/
theorem geometricHistory_live_lookup
    (exponent : Nat) (hexponent : 8 ≤ exponent) :
    get? (geometricHistory exponent).records (exponent - 8) =
      some (liveMeta (UInt32.ofNat (vectorBlockBase exponent))
        { size := 2 ^ exponent, alignment := 1 }) := by
  have hexp : exponent = (exponent - 8) + 8 := by omega
  conv_lhs => rw [hexp]
  conv_rhs => rw [hexp]
  unfold geometricHistory geometricRecords
  have hrange :
      List.range (exponent - 8 + 8 - 7) =
        List.range (exponent - 8) ++ [exponent - 8] := by
    rw [show exponent - 8 + 8 - 7 = (exponent - 8) + 1 by omega]
    simpa only [Nat.succ_eq_add_one] using
      (List.range_succ (n := exponent - 8))
  rw [hrange, List.foldl_append]
  simp [geometricMetadata, liveMeta, get?_insert_eq]

/-- Appending and retiring one block advances the canonical geometric
allocation history by one exponent. -/
private theorem geometricHistory_reallocate_from_eight (n : Nat) :
    (geometricHistory (n + 8)).reallocate n
      (UInt32.ofNat (vectorBlockBase (n + 8)))
      { size := 2 ^ (n + 8), alignment := 1 }
      (UInt32.ofNat (vectorBlockBase (n + 9)))
      { size := 2 ^ (n + 9), alignment := 1 } =
      geometricHistory (n + 9) := by
  have hsub8 : n + 8 - 7 = n + 1 := by omega
  have hsub9 : n + 9 - 7 = n + 2 := by omega
  have hrange1 : List.range (n + 1) = List.range n ++ [n] := by
    simpa only [Nat.succ_eq_add_one] using (List.range_succ (n := n))
  have hrange2 :
      List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by
    simpa only [Nat.succ_eq_add_one] using
      (List.range_succ (n := n + 1))
  unfold AllocationHistory.reallocate geometricHistory geometricRecords
    AllocationHistory.allocate AllocationHistory.retire
  rw [hsub8, hsub9, hrange2, hrange1,
    List.foldl_append, List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hfold :
      (List.range n).foldl
          (fun records allocationId =>
            insert records allocationId
              (geometricMetadata (n + 8) allocationId))
          (∅ : WasmAllocationMap AllocationMeta) =
        (List.range n).foldl
          (fun records allocationId =>
            insert records allocationId
              (geometricMetadata (n + 9) allocationId))
          (∅ : WasmAllocationMap AllocationMeta) := by
    apply foldl_insert_congr
    intro allocationId hid
    have hlt : allocationId < n := List.mem_range.mp hid
    simp [geometricMetadata, show allocationId ≠ n by omega,
      show allocationId ≠ n + 1 by omega]
  rw [hfold]
  congr 1
  simp only [geometricMetadata,
    show ¬n + 8 = n + 9 by omega, if_false,
    liveMeta, retiredMeta]
  norm_num
  apply insert_overwrite_commute

theorem geometricHistory_reallocate
    (exponent : Nat) (hexponent : 8 ≤ exponent) :
    (geometricHistory exponent).reallocate (exponent - 8)
      (UInt32.ofNat (vectorBlockBase exponent))
      { size := 2 ^ exponent, alignment := 1 }
      (UInt32.ofNat (vectorBlockBase (exponent + 1)))
      { size := 2 ^ (exponent + 1), alignment := 1 } =
      geometricHistory (exponent + 1) := by
  have hexp : exponent = (exponent - 8) + 8 := by omega
  conv_lhs => rw [hexp]
  conv_rhs => rw [hexp]
  simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] using
    geometricHistory_reallocate_from_eight (exponent - 8)

theorem vectorBlockBase_succ (exponent : Nat) (h : 8 ≤ exponent) :
    vectorBlockBase exponent + 2 ^ exponent =
      vectorBlockBase (exponent + 1) := by
  unfold vectorBlockBase
  rw [pow_succ]
  have hp : 256 ≤ 2 ^ exponent := by
    rw [show 256 = 2 ^ 8 by norm_num]
    exact Nat.pow_le_pow_right (by decide) h
  omega

theorem selectedCapacity_geometric
    (length current exponent : Nat)
    (hexponent : 8 ≤ exponent)
    (hlength : length ≤ 2 ^ exponent)
    (hcurrent : current ≤ 256) :
    selectedCapacity length current (2 ^ exponent) =
      2 ^ (exponent + 1) := by
  have hpow : 256 ≤ 2 ^ exponent := by
    rw [show 256 = 2 ^ 8 by norm_num]
    exact Nat.pow_le_pow_right (by decide) hexponent
  have hlower : length + current ≤ 2 * 2 ^ exponent := by omega
  have h8 : 8 ≤ 2 * 2 ^ exponent := by omega
  unfold selectedCapacity
  rw [max_eq_left h8, max_eq_right hlower, pow_succ]
  omega

/-- Exact public-input Vec lineage used to eliminate both RawVec panic edges.
`totalBytes = length + remaining` in every active state. -/
def GeometricVecFacts
    (totalBytes length remaining : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory) : Prop :=
  (capacity = 0 ∧ ptr = 1 ∧ length = 0 ∧ remaining = totalBytes ∧
      frontier = heapBase.toNat ∧ history = AllocationHistory.empty) ∨
  (remaining = 0 ∧ length = totalBytes ∧ totalBytes < 256 ∧
      capacity.toNat = max totalBytes 8 ∧ ptr = heapBase ∧
      frontier = heapBase.toNat + capacity.toNat ∧
      history = shortHistory capacity.toNat) ∨
  (∃ exponent,
      8 ≤ exponent ∧ exponent ≤ 29 ∧
      capacity.toNat = 2 ^ exponent ∧
      length ≤ capacity.toNat ∧
      totalBytes = length + remaining ∧
      ptr.toNat = vectorBlockBase exponent ∧
      frontier = vectorBlockBase exponent + 2 ^ exponent ∧
      history = geometricHistory exponent)

/-- A normally completed public read loop has a byte length below the signed
address boundary.  Larger geometric Vec executions reach the allocator's OOM
classification before they can complete. -/
theorem GeometricVecFacts.completed_lt_signed
    (totalBytes length remaining : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (hgeo : GeometricVecFacts totalBytes length remaining
      capacity ptr frontier history)
    (hremaining : remaining = 0) :
    totalBytes < 2147483648 := by
  rcases hgeo with hinitial | hshort | hlarge
  · omega
  · omega
  · rcases hlarge with
      ⟨exponent, _hexponentLower, hexponentUpper, hcapacity,
        hlength, htotal, _hptr, _hfrontier, _hhistory⟩
    have hpow : 2 ^ exponent ≤ 2 ^ 29 :=
      Nat.pow_le_pow_right (by decide) hexponentUpper
    rw [hremaining, Nat.add_zero] at htotal
    rw [hcapacity] at hlength
    norm_num at hpow ⊢
    omega

/-- Every nonempty completed public Vec has a four-aligned data pointer, even
though its Rust allocation layout requests only byte alignment.  This follows
from the concrete short pointer and geometric power-of-two lineage. -/
theorem GeometricVecFacts.completed_ptr_align4
    (totalBytes length remaining : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (hgeo : GeometricVecFacts totalBytes length remaining
      capacity ptr frontier history)
    (hremaining : remaining = 0) (hpositive : 0 < totalBytes) :
    ptr.toNat % 4 = 0 := by
  rcases hgeo with hinitial | hshort | hlarge
  · omega
  · rw [hshort.2.2.2.2.1]
    decide
  · rcases hlarge with
      ⟨exponent, hexponentLower, _hexponentUpper, _hcapacity,
        _hlength, _htotal, hptr, _hfrontier, _hhistory⟩
    rw [hptr]
    unfold vectorBlockBase
    have hpow256 : 256 ≤ 2 ^ exponent := by
      rw [show 256 = 2 ^ 8 by norm_num]
      exact Nat.pow_le_pow_right (by decide) hexponentLower
    have hdiv : 4 ∣ 2 ^ exponent := by
      simpa using Nat.pow_dvd_pow 2 (by omega : 2 ≤ exponent)
    have hpowMod : 2 ^ exponent % 4 = 0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    have hbaseMod : heapBase.toNat % 4 = 0 := by decide
    omega

/-- Establish the two word-array views used by the generated decode loop.
The source remains focused out of the completed `ExportFrame`, while the
arbitrary fresh values allocation becomes the canonical decoded initial word
list with its allocation token retained. -/
theorem DriverDecodeBuffers_open
    [WasmHeapGS Universal.State]
    (heapId : GName) (capacity source valuesPtr : UInt32)
    (valuesId : Nat) (original : List UInt32)
    (chunkBytes outputBytes bytes : List UInt8)
    (frontier : Nat) (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hgeo : GeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity source frontier history) :
    ExportFrame heapId capacity source (serialize original) chunkBytes
        outputBytes ∗
      LiveBlock heapId valuesId valuesPtr
        { size := 4 * original.length, alignment := 4 } bytes ⊢
      iprop(WordSlice source original ∗
        (WordSlice source original -∗
          ExportFrame heapId capacity source (serialize original) chunkBytes
            outputBytes) ∗
        LiveWordBlock heapId valuesId valuesPtr (decodeWords bytes)) := by
  iintro ⟨Hframe, Hblock⟩
  have hpositive : 0 < (serialize original).length := by
    rw [serialize_length]
    have := List.length_pos_iff_ne_nil.mpr horiginal
    omega
  have hsourceAlign := GeometricVecFacts.completed_ptr_align4
    (serialize original).length (serialize original).length 0 capacity source
    frontier history hgeo rfl hpositive
  ihave ⟨Hsource, HcloseSource⟩ := ExportFrame_completedWordsFocus heapId capacity source
    original chunkBytes outputBytes horiginal hsourceAlign $$ Hframe
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hblockFacts⟩
  ihave Hblock : LiveBlock heapId valuesId valuesPtr
      { size := 4 * original.length, alignment := 4 } bytes $$
      [Htoken Hbytes]
  · unfold LiveBlock
    iframe
    ipureexact hblockFacts
  ihave Hvalues := (LiveBlock_as_decodedWordBlock heapId valuesId
    original.length valuesPtr bytes hblockFacts.1).mp $$ Hblock
  iframe

/-- The driver's second `0x7ffffffc` use computes the largest four-word
prefix of the decoded element count.  The remaining `count % 4` words are
handled by the generated tail loop. -/
theorem bulk4_signedMask_eq (count : Nat)
    (hbound : count < 2147483648) :
    (UInt32.ofNat count &&& (2147483644 : UInt32)) =
      UInt32.ofNat (4 * (count / 4)) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_and]
  have hcountWord : (UInt32.ofNat count).toNat = count := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size] at hbound ⊢
    omega
  rw [hcountWord]
  have hmaskWord : (2147483644 : UInt32).toNat = 2147483644 := by
    decide
  rw [hmaskWord]
  have hbulkLe : 4 * (count / 4) ≤ count := by
    have hmod := Nat.mod_add_div count 4
    omega
  have hbulkBound : 4 * (count / 4) < UInt32.size := by
    norm_num [UInt32.size] at hbound ⊢
    omega
  rw [UInt32.toNat_ofNat_of_lt' hbulkBound]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  have hbulk :
      (4 * (count / 4)).testBit i =
        (decide (2 ≤ i) && count.testBit i) := by
    rw [show 4 * (count / 4) = 2 ^ 2 * (count / 2 ^ 2) by norm_num]
    rw [Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
    by_cases hi : 2 ≤ i
    · simp only [hi, decide_true, Bool.true_and]
      congr 1
      omega
    · simp only [hi, decide_false, Bool.false_and]
  rw [hbulk]
  cases hnbit : count.testBit i with
  | false => simp
  | true =>
      by_cases hi2 : 2 ≤ i
      · have hi31 : i < 31 := by
          by_contra hnot
          have hp : 2 ^ 31 ≤ 2 ^ i :=
            Nat.pow_le_pow_right (by decide) (by omega)
          have hnlt : count < 2 ^ i := by
            norm_num at hp
            omega
          have hfalse := Nat.testBit_eq_false_of_lt hnlt
          rw [hnbit] at hfalse
          contradiction
        have h3 : (3 : Nat).testBit i = false := by
          apply Nat.testBit_eq_false_of_lt
          have hp : 2 ^ 2 ≤ 2 ^ i :=
            Nat.pow_le_pow_right (by decide) hi2
          norm_num at hp ⊢
          omega
        have hmask : 2147483644 = 2 ^ 31 - (3 + 1) := by norm_num
        rw [hmask,
          Nat.testBit_two_pow_sub_succ (by norm_num : 3 < 2 ^ 31), h3]
        simp [hi2, hi31]
      · have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;>
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

/-- Exact split between the four-word bulk loop and its zero-to-three-word
tail. -/
theorem bulk4_add_tail (count : Nat) :
    4 * (count / 4) + count % 4 = count := by
  have h := Nat.mod_add_div count 4
  omega

theorem bulk4_tail_lt (count : Nat) :
    count % 4 < 4 := by
  omega

/-- Every four-store iteration stays strictly inside the decoded array and
advances no farther than the bulk boundary. -/
theorem bulk4_step_bounds (count iteration : Nat)
    (hstep : 4 * iteration < 4 * (count / 4)) :
    4 * iteration + 3 < count ∧
      4 * (iteration + 1) ≤ 4 * (count / 4) := by
  have hdecompose := Nat.mod_add_div count 4
  have htail := Nat.mod_lt count (by decide : 0 < 4)
  constructor <;> omega

/-- Exact arithmetic performed by the driver's first `0x7ffffffc` mask.  The
complete byte length is already four-aligned, so the bulk-prefix result is the
whole byte length. -/
theorem align4_signedMask_eq (byteLength : Nat)
    (hbound : byteLength < 2147483648)
    (halign : byteLength % 4 = 0) :
    (UInt32.ofNat byteLength &&& (2147483644 : UInt32)) =
      UInt32.ofNat byteLength := by
  rw [bulk4_signedMask_eq byteLength hbound]
  congr 1
  have hmod := Nat.mod_add_div byteLength 4
  omega

/-- A positive four-aligned size below the signed address boundary is a valid
layout for the generated values and scratch allocators.  Four-alignment is
what sharpens the strict signed bound to the allocator's `2^31 - 4` limit. -/
theorem align4Layout_valid_of_bounds (size : Nat)
    (hpositive : 0 < size) (hbound : size < 2147483648)
    (halign : size % 4 = 0) :
    ({ size := size, alignment := 4 } : AllocLayout).Valid := by
  unfold AllocLayout.Valid
  dsimp only
  refine ⟨hpositive, by decide, ⟨2, by norm_num⟩, by norm_num, ?_, ?_,
    by norm_num⟩
  · omega
  · norm_num [UInt32.size] at hbound ⊢
    omega

private theorem align1Layout_valid_of_bounds (size : Nat)
    (hsizeLower : 8 ≤ size) (hsizeUpper : size ≤ 1073741824) :
    ({ size := size, alignment := 1 } : AllocLayout).Valid := by
  unfold AllocLayout.Valid
  dsimp only
  refine ⟨by omega, by decide, ⟨0, by decide⟩, by decide, ?_, ?_,
    by decide⟩
  · omega
  · norm_num [UInt32.size]
    omega

/-- The public read-loop lineage supplies all arithmetic needed by the valid
`func1` specialization.  In particular the checked addition cannot wrap and
the selected RawVec layout remains valid even on the final attempt that the
bump allocator classifies as OOM. -/
theorem GeometricVecFacts.reserveLayout
    (total length remaining current : Nat)
    (capacity ptr : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (hgeo : GeometricVecFacts total length remaining
      capacity ptr frontier history)
    (hread : current = min 256 remaining)
    (hcurrent : 0 < current) :
    let newCapacity := selectedCapacity length current capacity.toNat
    let newLayout : AllocLayout :=
      { size := newCapacity, alignment := 1 }
    length + current < UInt32.size ∧
      newCapacity < UInt32.size ∧
      newLayout.Valid := by
  have hcurrentBound : current ≤ 256 := by
    rw [hread]
    exact min_le_left _ _
  rcases hgeo with hempty | hshort | hlarge
  · rcases hempty with
      ⟨rfl, rfl, rfl, _hremaining, _hfrontier, _hhistory⟩
    dsimp only [selectedCapacity]
    have hnewLower :
        8 ≤ max (0 + current) (max (2 * (0 : UInt32).toNat) 8) := by
      norm_num
    have hnewUpper :
        max (0 + current) (max (2 * (0 : UInt32).toNat) 8) ≤
          1073741824 := by
      norm_num
      omega
    exact ⟨by
      norm_num [UInt32.size]
      omega, by
      norm_num [UInt32.size]
      omega, align1Layout_valid_of_bounds _ hnewLower hnewUpper⟩
  · rcases hshort with
      ⟨hremaining, _hlength, _htotal, _hcapacity, _hptr,
        _hfrontier, _hhistory⟩
    rw [hremaining] at hread
    simp at hread
    omega
  · rcases hlarge with
      ⟨exponent, _hexponentLower, hexponentUpper, hcapacity,
        hlength, _htotal, _hptr, _hfrontier, _hhistory⟩
    have hcapacityUpper : capacity.toNat ≤ 2 ^ 29 := by
      rw [hcapacity]
      exact Nat.pow_le_pow_right (by decide) hexponentUpper
    have hnewLower :
        8 ≤ selectedCapacity length current capacity.toNat := by
      unfold selectedCapacity
      omega
    have hnewUpper :
        selectedCapacity length current capacity.toNat ≤ 1073741824 := by
      unfold selectedCapacity
      norm_num
      omega
    exact ⟨by
      norm_num [UInt32.size]
      omega, by
      norm_num [UInt32.size]
      omega, align1Layout_valid_of_bounds _ hnewLower hnewUpper⟩

/-- When the generated capacity test says that the new chunk fits, appending
it preserves the current large-input lineage without touching allocation
metadata.  The empty and completed-short variants cannot satisfy this premise
for a nonempty chunk. -/
theorem GeometricVecFacts.appendWithoutReserve
    (total length current remaining : Nat)
    (capacity ptr : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (hgeo : GeometricVecFacts total length (current + remaining)
      capacity ptr frontier history)
    (hcurrent : 0 < current)
    (hfits : current ≤ capacity.toNat - length) :
    GeometricVecFacts total (length + current) remaining
      capacity ptr frontier history := by
  rcases hgeo with hempty | hshort | hlarge
  · rcases hempty with
      ⟨rfl, _hptr, rfl, _hremaining, _hfrontier, _hhistory⟩
    simp only [UInt32.toNat_zero, Nat.zero_sub] at hfits
    omega
  · rcases hshort with
      ⟨hremaining, _hlength, _htotal, _hcapacity, _hptr,
        _hfrontier, _hhistory⟩
    omega
  · right
    right
    rcases hlarge with
      ⟨exponent, hexponentLower, hexponentUpper, hcapacity,
        hlength, htotal, hptr, hfrontier, hhistory⟩
    refine ⟨exponent, hexponentLower, hexponentUpper, hcapacity,
      ?_, ?_, hptr, hfrontier, hhistory⟩
    · omega
    · omega

/-- A normal successful `func1` growth step preserves the exact public-input
Vec lineage.  This is the caller-side obligation that makes both generated
RawVec panic edges unreachable: the short terminal form cannot reserve a
nonempty chunk, and every large allocation advances exactly one exponent. -/
theorem GeometricVecFacts.reserveSuccess
    (total length current remaining : Nat)
    (capacity ptr newPtr finish : UInt32)
    (frontier : Nat) (history finalHistory : AllocationHistory)
    (hgeo : GeometricVecFacts total length (current + remaining)
      capacity ptr frontier history)
    (hread : current = min 256 (current + remaining))
    (hcurrent : 0 < current)
    (hclassify :
      classifyBump frontier
        { size := selectedCapacity length current capacity.toNat,
          alignment := 1 } = .success newPtr finish)
    (hreserveHistory :
      VecReserveHistory history finalHistory capacity ptr newPtr
        { size := selectedCapacity length current capacity.toNat,
          alignment := 1 }) :
    GeometricVecFacts total (length + current) remaining
      (UInt32.ofNat (selectedCapacity length current capacity.toNat))
      newPtr finish.toNat finalHistory := by
  have hcurrentBound : current ≤ 256 := by
    rw [hread]
    exact min_le_left _ _
  have halloc := classifyBump_success_align1 frontier
    (selectedCapacity length current capacity.toNat) newPtr finish hclassify
  rcases halloc with
    ⟨hfrontierWord, hnewPtr, hnewPtrNat, hendWord, hendSigned, hfinish⟩
  have hcapacityWord :
      selectedCapacity length current capacity.toNat < UInt32.size := by
    omega
  have hcapacityNat :
      (UInt32.ofNat
        (selectedCapacity length current capacity.toNat)).toNat =
        selectedCapacity length current capacity.toNat :=
    UInt32.toNat_ofNat_of_lt' hcapacityWord
  rcases hgeo with hempty | hshort | hlarge
  · rcases hempty with
      ⟨rfl, rfl, rfl, hremaining, rfl, rfl⟩
    simp only [UInt32.toNat_zero] at *
    have hnewPtrBase : newPtr = heapBase := by
      rw [hnewPtr]
      exact UInt32.ofNat_toNat
    have hselected :
        selectedCapacity 0 current 0 = max current 8 := by
      simp [selectedCapacity]
    simp [VecReserveHistory] at hreserveHistory
    by_cases htotal : total < 256
    · have hmin :
          min 256 (current + remaining) = current + remaining :=
        min_eq_right (by omega)
      rw [hmin] at hread
      have hcurrentTotal : current = total := by omega
      have hremainingZero : remaining = 0 := by omega
      subst current
      subst remaining
      right
      left
      refine ⟨rfl, by omega, htotal, ?_, hnewPtrBase, ?_, ?_⟩
      · rw [hcapacityNat, hselected]
      · rw [hfinish, hcapacityNat]
      · rw [hreserveHistory, hnewPtrBase, hcapacityNat, hselected]
        rfl
    · have hmin : min 256 (current + remaining) = 256 :=
        min_eq_left (by omega)
      rw [hmin] at hread
      have hcurrent256 : current = 256 := hread
      subst current
      right
      right
      refine ⟨8, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcapacityNat]
        norm_num [selectedCapacity]
      · rw [hcapacityNat]
        norm_num [selectedCapacity]
      · omega
      · rw [hnewPtrNat]
        norm_num [vectorBlockBase]
      · rw [hfinish]
        norm_num [selectedCapacity, vectorBlockBase]
      · rw [hreserveHistory, hnewPtrBase]
        norm_num [selectedCapacity]
        rfl
  · rcases hshort with
      ⟨hremaining, _hlength, _htotal, _hcapacity, _hptr,
        _hfrontier, _hhistory⟩
    rw [hremaining] at hread
    simp at hread
    omega
  · rcases hlarge with
      ⟨exponent, hexponentLower, hexponentUpper, hcapacity,
        hlength, htotal, hptr, hfrontier, hgeoHistory⟩
    have hlength' : length ≤ 2 ^ exponent := by
      rw [← hcapacity]
      exact hlength
    have hselected :
        selectedCapacity length current capacity.toNat =
          2 ^ (exponent + 1) := by
      rw [hcapacity]
      exact selectedCapacity_geometric length current exponent
        hexponentLower hlength' hcurrentBound
    have hselected' :
        selectedCapacity length current (2 ^ exponent) =
          2 ^ (exponent + 1) := by
      rw [← hcapacity]
      exact hselected
    have hpow : 256 ≤ 2 ^ exponent := by
      rw [show 256 = 2 ^ 8 by norm_num]
      exact Nat.pow_le_pow_right (by decide) hexponentLower
    have hfrontierNext : frontier = vectorBlockBase (exponent + 1) := by
      rw [hfrontier]
      exact vectorBlockBase_succ exponent hexponentLower
    have hptrExact :
        ptr = UInt32.ofNat (vectorBlockBase exponent) := by
      rw [← UInt32.ofNat_toNat (x := ptr), hptr]
    have hnewPtrExact :
        newPtr = UInt32.ofNat (vectorBlockBase (exponent + 1)) := by
      rw [hnewPtr, hfrontierNext]
    have hcapacityNe : capacity ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero
      simp only [UInt32.toNat_zero] at hzeroNat
      have hpowPositive : 0 < 2 ^ exponent := Nat.pow_pos (by omega)
      rw [hcapacity] at hzeroNat
      omega
    unfold VecReserveHistory at hreserveHistory
    rw [if_neg hcapacityNe] at hreserveHistory
    rcases hreserveHistory with ⟨oldId, holdLookup, hfinalHistory⟩
    have holdId : oldId = exponent - 8 := by
      apply geometricHistory_live_unique exponent oldId hexponentLower
      simpa only [hgeoHistory, hptrExact, hcapacity] using holdLookup
    have hfinal :
        finalHistory = geometricHistory (exponent + 1) := by
      rw [hfinalHistory, hgeoHistory, holdId, hptrExact, hcapacity,
        hnewPtrExact, hselected',
        geometricHistory_reallocate exponent hexponentLower]
    have hexponentNextUpper : exponent + 1 ≤ 29 := by
      by_contra hnot
      have heq : exponent = 29 := by omega
      rw [hnewPtrNat, hfrontierNext, hselected] at hendSigned
      subst exponent
      norm_num [vectorBlockBase, heapBase, UInt32.toNat] at hendSigned
    right
    right
    refine ⟨exponent + 1, by omega, hexponentNextUpper, ?_, ?_, ?_,
      ?_, ?_, hfinal⟩
    · rw [hcapacityNat, hselected]
    · rw [hcapacityNat, hselected, pow_succ]
      omega
    · omega
    · rw [hnewPtrNat, hfrontierNext]
    · rw [hfinish, hfrontierNext, hselected]

/-- Complete ownership of the Universal host state, existentially hiding the
unused random-host component while fixing both streams and the OOM marker. -/
def Streams [WasmHostStateGS Universal.State]
    (input output : List UInt8) (raised : Bool) :
    IProp (WasmHeapGF Universal.State) :=
  iprop(∃ random : Random.State,
    hostStateOwn
      ({ stdio := { input := input, output := output }
         random := random
         oom := { raised := raised } } : Universal.State))

/-- Runtime identity for a running expression.  This includes the exclusive
current-instance token, so normal returns restore it while terminal host traps
consume it.  No mutable host state, global, heap, or stack ownership is hidden
here. -/
def RuntimeContext [WasmRuntimeModuleGS Universal.State]
    [WasmInstanceGS Universal.State] [WasmHostEnvGS Universal.State] :
    IProp (WasmHeapGF Universal.State) :=
  iprop(runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
    hostEnvOwn 0 (Universal.envFor Project.Mergesort.module))

/-- Open the module and host-environment resources carried by a merge-sort
runtime context. -/
macro "iopen_runtime " runtime:ident " with " pattern:icasesPat : tactic => do
  let selected ← `(selPat| $runtime:ident)
  let resource ← `(pmTerm| $runtime:ident)
  `(tactic|
    (isimp only [Project.Mergesort.Representations.RuntimeContext] at $selected
     icases $resource with $pattern))

/-- Reassemble a merge-sort runtime context from its two resources. -/
macro "iclose_runtime " runtime:ident " with " moduleOwn:ident hostEnv:ident : tactic => do
  let runtimePattern ← `(icasesPat| $runtime:ident)
  let moduleFrame ← `(frameIdent| $moduleOwn:ident)
  let hostFrame ← `(frameIdent| $hostEnv:ident)
  let moduleSelected ← `(selPat| $moduleOwn:ident)
  let hostSelected ← `(selPat| $hostEnv:ident)
  `(tactic|
    (ihave $runtimePattern : RuntimeContext $$ [$moduleFrame $hostFrame]
     · unfold RuntimeContext
       iframe $moduleSelected $hostSelected))

def AllRetired (history : AllocationHistory) : Prop :=
  ∀ allocationId metadata,
    get? history.records allocationId = some metadata →
    metadata.status = .retired

inductive DriverOOMPhase where
  | reserve
  | values
  | scratch
  deriving Repr, DecidableEq

/-- Resources returned by the normal driver outcome. -/
def DriverSuccess [WasmHeapGS Universal.State]
    [WasmHeapDomainGS Universal.State]
    [WasmMemoryPagesGS Universal.State]
    [WasmGlobalGS Universal.State]
    [WasmHostStateGS Universal.State]
    (heapId : GName) (original : List UInt32) :
    IProp (WasmHeapGF Universal.State) := iprop%
  ∃ sorted : List UInt32, ∃ stackBytes : List UInt8,
  ∃ storedCursor : UInt32, ∃ frontier : Nat,
  ∃ history : AllocationHistory,
    ⌜SortedPermutation original sorted ∧
      stackBytes.length = 288 ∧ AllRetired history⌝ ∗
    StackPointer entryStackTop ∗
    StackRegion entryStackLow stackBytes ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams [] (serialize sorted) false

/-- Exact reserve-phase OOM resources.  The just-read nonempty chunk is still
in the frame and has already been removed from the host input. -/
def DriverReserveOOM [WasmHeapGS Universal.State]
    [WasmHeapDomainGS Universal.State]
    [WasmMemoryPagesGS Universal.State]
    [WasmGlobalGS Universal.State]
    [WasmHostStateGS Universal.State]
    (heapId : GName) (original : List UInt32) :
    IProp (WasmHeapGF Universal.State) := iprop%
  ∃ capacity ptr : UInt32,
  ∃ appended current remaining chunkTail outputBytes shadow : List UInt8,
  ∃ storedCursor : UInt32, ∃ frontier : Nat,
  ∃ history : AllocationHistory,
    ⌜serialize original = appended ++ current ++ remaining ∧
      0 < current.length ∧
      current.length % 4 = 0 ∧
      current.length = min 256 (current.length + remaining.length) ∧
      (current ++ chunkTail).length = 256 ∧
      GeometricVecFacts (serialize original).length appended.length
        (current.length + remaining.length) capacity ptr frontier history⌝ ∗
    StackPointer reserveBase ∗
    StackReserve reserveBase shadow ∗
    ExportFrame heapId capacity ptr appended
      (current ++ chunkTail) outputBytes ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams remaining [] true

/-- Exact values-allocation OOM resources. -/
def DriverValuesOOM [WasmHeapGS Universal.State]
    [WasmHeapDomainGS Universal.State]
    [WasmMemoryPagesGS Universal.State]
    [WasmGlobalGS Universal.State]
    [WasmHostStateGS Universal.State]
    (heapId : GName) (original : List UInt32) :
    IProp (WasmHeapGF Universal.State) := iprop%
  ∃ capacity ptr : UInt32,
  ∃ chunkBytes outputBytes shadow : List UInt8,
  ∃ storedCursor : UInt32, ∃ frontier : Nat,
  ∃ history : AllocationHistory,
    ⌜0 < original.length ∧
      GeometricVecFacts (serialize original).length
        (serialize original).length 0 capacity ptr frontier history⌝ ∗
    StackPointer driverBase ∗
    StackReserve reserveBase shadow ∗
    ExportFrame heapId capacity ptr (serialize original)
      chunkBytes outputBytes ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams [] [] true

/-- Exact scratch-allocation OOM resources.  The decoded values allocation is
still live; no scratch allocation has been committed. -/
def DriverScratchOOM [WasmHeapGS Universal.State]
    [WasmHeapDomainGS Universal.State]
    [WasmMemoryPagesGS Universal.State]
    [WasmGlobalGS Universal.State]
    [WasmHostStateGS Universal.State]
    (heapId : GName) (original : List UInt32) :
    IProp (WasmHeapGF Universal.State) := iprop%
  ∃ capacity ptr valuesPtr : UInt32,
  ∃ valuesId : Nat,
  ∃ chunkBytes outputBytes shadow : List UInt8,
  ∃ storedCursor : UInt32, ∃ frontier : Nat,
  ∃ history : AllocationHistory,
    ⌜0 < original.length⌝ ∗
    StackPointer driverBase ∗
    StackReserve reserveBase shadow ∗
    ExportFrame heapId capacity ptr (serialize original)
      chunkBytes outputBytes ∗
    LiveWordBlock heapId valuesId valuesPtr original ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams [] [] true

def DriverOOMState [WasmHeapGS Universal.State]
    [WasmHeapDomainGS Universal.State]
    [WasmMemoryPagesGS Universal.State]
    [WasmGlobalGS Universal.State]
    [WasmHostStateGS Universal.State]
    (heapId : GName) (original : List UInt32) :
    DriverOOMPhase → IProp (WasmHeapGF Universal.State)
  | .reserve => DriverReserveOOM heapId original
  | .values => DriverValuesOOM heapId original
  | .scratch => DriverScratchOOM heapId original

end Project.Mergesort.Representations
