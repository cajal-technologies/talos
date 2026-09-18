import Project.RustHashMap.LookupPures
import Project.RustHashMap.MapOpContracts
import Project.RustHashMap.EntriesContracts
import Project.RustHashMap.ContainsKeyTailProof

/-!
# The pure lemmas of the `map_remove` driver tail

`map_remove` is absolute `func 9`.  Its tail calls three bodies in a row:
absolute `func 11` removes the key, absolute `func 7` sorts the entries
that are left, and absolute `func 8` writes the reply.  The contracts of
the three are `Project.RustHashMap.MapOpContracts.Func8Spec`,
`Project.RustHashMap.EntriesContracts.Func4Spec` and
`Project.RustHashMap.EntriesContracts.Func5Spec`.

This file holds the facts that the tail needs and that say nothing about
the compiled state.  `Project.RustHashMap.LookupPures` is the template:
the two files share `acceptedEntries`, `keyAndMap_of_accepts` and
`keyAndMap_eq_none_of_not_accepts`.

## The four groups

* The answer slot.  The tail loads the eight bytes of the `Option<u32>`
  answer with one `i64.load offset=64` and stores the same word back with
  one `i64.store offset=64`.  `optionU32At_bytes` is the byte view of the
  slot and `optionU32At_as_u64` is the round trip itself.
* The entry bound.  `acceptedEntries_le_max` bounds the entry count of an
  accepted input by `67108863`.  Eight bytes carry one pair, the input
  vector holds at most `536870912` bytes, and the header of an accepted
  input names every pair.
* The accepted output.  `removeOutput_of_accepts` names
  `Project.RustHashMap.Spec.removeOutput` in the shape that the two
  contracts hand out.
* The rejected output.  `removeOutput_of_not_accepts` gives the empty
  answer on the three shapes that the key decoder rejects.

## Why the bound is `67108863` and not `2 ^ 30`

`Project.RustHashMap.ContainsKeyTailProof.acceptedEntries_bound` reads the
entry count against `UInt32.size` alone, which is enough for the table
model.  The remove tail also needs `Func14ResizeSpec`, which rejects a
capacity above `Project.RustHashMap.EntryContracts.maxTableCapacity`.
`Project.RustHashMap.VecGrow.PushVecFacts.capacity_le` bounds the input
vector, so the tighter bound comes from the read phase and not from the
address space.
-/

namespace Project.RustHashMap.RemovePures

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.LookupPures
open Project.RustHashMap.VecGrow

/-! ## The byte view of the answer slot -/

/-- What the eight raw bytes of an `Option<u32>` out-parameter say.  The
first word is the discriminant.  The second word is the payload of a
`some`, and a `none` leaves it free, because absolute `func 18` writes a
leftover address there. -/
def optionDecodes (bs : List UInt8) (o : Option UInt32) : Prop :=
  match o with
  | none => WordCodec.decodeU32 (bs.take 4) = 0
  | some v =>
      WordCodec.decodeU32 (bs.take 4) = 1 ∧
        WordCodec.decodeU32 (bs.drop 4) = v

section Memory

variable {α : Type} [WasmHeapGS α]

/-- Two adjacent owned words are eight owned bytes, and the bytes decode
back to the two words. -/
theorem words_as_bytes (memId : Nat) (p : UInt32) (w0 w1 : UInt32)
    (hnowrap : p.toNat + 8 < UInt32.size) :
    iprop(pointsTo_u32 (α := α) memId p w0 ∗
        pointsTo_u32 memId (p + 4) w1) ⊣⊢
      iprop(∃ bs : List UInt8, Slices.ByteSlice memId p bs ∗
        ⌜bs.length = 8 ∧ WordCodec.decodeU32 (bs.take 4) = w0 ∧
          WordCodec.decodeU32 (bs.drop 4) = w1⌝) := by
  have hstep : (p + 4).toNat = p.toNat + 4 := by
    simpa using Slices.byteOffset_toNat p 4 (by omega)
  have hlen0 : (WordCodec.encodeU32 w0).length = 4 := rfl
  have hlen1 : (WordCodec.encodeU32 w1).length = 4 := rfl
  have hdec0 : WordCodec.decodeU32 (WordCodec.encodeU32 w0) = w0 :=
    WordCodec.u32le.decode_encode w0
  have hdec1 : WordCodec.decodeU32 (WordCodec.encodeU32 w1) = w1 :=
    WordCodec.u32le.decode_encode w1
  have hfour : (UInt32.ofNat 4 : UInt32) = 4 := rfl
  constructor
  · iintro ⟨H0, H1⟩
    iexists (WordCodec.encodeU32 w0 ++ WordCodec.encodeU32 w1)
    ihave Hslice : Slices.ByteSlice memId p
        (WordCodec.encodeU32 w0 ++ WordCodec.encodeU32 w1) $$ [H0 H1]
    · iapply (Slices.ByteSlice_append memId p (WordCodec.encodeU32 w0)
        (WordCodec.encodeU32 w1)).mpr
      isimp only [hlen0, hfour]
      isplitl [H0]
      · iapply (Slices.ByteSlice_four_as_word memId p
          (WordCodec.encodeU32 w0) hlen0 (by omega)).mpr
        irw_exact [hdec0] with H0
      · iapply (Slices.ByteSlice_four_as_word memId (p + 4)
          (WordCodec.encodeU32 w1) hlen1 (by omega)).mpr
        irw_exact [hdec1] with H1
    iframe_pureexact (by
      refine ⟨by rw [List.length_append, hlen0, hlen1], ?_, ?_⟩
      · rw [List.take_left' hlen0]; exact hdec0
      · rw [List.drop_left' hlen0]; exact hdec1)
  · iintro ⟨%bs, Hslice, %hfacts⟩
    obtain ⟨hlength, htake, hdrop⟩ := hfacts
    subst htake
    subst hdrop
    have htakeLen : (bs.take 4).length = 4 := by
      rw [List.length_take]; omega
    have hdropLen : (bs.drop 4).length = 4 := by
      rw [List.length_drop]; omega
    ihave Hcat : Slices.ByteSlice memId p (bs.take 4 ++ bs.drop 4) $$
        [Hslice]
    · irw_exact [List.take_append_drop] with Hslice
    ihave ⟨Htake, Hdrop⟩ :=
      (Slices.ByteSlice_append memId p (bs.take 4) (bs.drop 4)).mp $$ Hcat
    isimp only [htakeLen, hfour] at Hdrop
    isplitl [Htake]
    · iapply (Slices.ByteSlice_four_as_word memId p (bs.take 4) htakeLen
        (by omega)).mp
      iexact Htake
    · iapply (Slices.ByteSlice_four_as_word memId (p + 4) (bs.drop 4)
        hdropLen (by omega)).mp
      iexact Hdrop

/-- The answer slot as eight raw bytes.  A `none` slot keeps its payload
word, so the bytes are not the same on the two arms, but the fact that
they decode is. -/
theorem optionU32At_bytes (memId : Nat) (p : UInt32) (o : Option UInt32)
    (hnowrap : p.toNat + 8 < UInt32.size) :
    Table.optionU32At (α := α) memId p o ⊣⊢
      iprop(∃ bs : List UInt8, Slices.ByteSlice memId p bs ∗
        ⌜bs.length = 8 ∧ optionDecodes bs o⌝) := by
  cases o with
  | none =>
    constructor
    · iintro Hopt
      isimp only [Table.optionU32At] at Hopt
      icases Hopt with ⟨%pad, Htag, Hpad⟩
      ihave Hwords : iprop(pointsTo_u32 memId p 0 ∗
          pointsTo_u32 memId (p + 4) pad) $$ [Htag Hpad]
      · iframe Htag Hpad
      ihave ⟨%bs, Hslice, %hfacts⟩ :=
        (words_as_bytes memId p 0 pad hnowrap).mp $$ Hwords
      iexists bs
      iframe_pureexact ⟨hfacts.1, hfacts.2.1⟩
    · iintro ⟨%bs, Hslice, %hfacts⟩
      ihave Hwords :
          iprop(pointsTo_u32 memId p 0 ∗
            pointsTo_u32 memId (p + 4)
              (WordCodec.decodeU32 (bs.drop 4))) $$ [Hslice]
      · iapply (words_as_bytes memId p 0
          (WordCodec.decodeU32 (bs.drop 4)) hnowrap).mpr
        iexists bs
        iframe_pureexact ⟨hfacts.1, hfacts.2, rfl⟩
      icases Hwords with ⟨Htag, Hpad⟩
      isimp only [Table.optionU32At]
      iexists (WordCodec.decodeU32 (bs.drop 4))
      iframe Htag Hpad
  | some v =>
    refine (Table.optionU32At_some memId p v).trans ?_
    refine (words_as_bytes memId p 1 v hnowrap).trans ?_
    constructor
    · iintro ⟨%bs, Hslice, %hfacts⟩
      iexists bs
      iframe_pureexact ⟨hfacts.1, hfacts.2.1, hfacts.2.2⟩
    · iintro ⟨%bs, Hslice, %hfacts⟩
      iexists bs
      iframe_pureexact ⟨hfacts.1, hfacts.2.1, hfacts.2.2⟩

/-- The load and store round trip of the tail.  One `i64.load offset=64`
takes the answer slot out as a single word and one `i64.store offset=64`
puts the same word back, which rebuilds the slot. -/
theorem optionU32At_as_u64 (memId : Nat) (p : UInt32)
    (o : Option UInt32) :
    Table.optionU32At (α := α) memId p o ⊢
      iprop(∃ v : UInt64, pointsTo_u64 memId p v ∗
        (pointsTo_u64 memId p v -∗ Table.optionU32At memId p o)) := by
  cases o with
  | none =>
    iintro Hopt
    isimp only [Table.optionU32At] at Hopt
    icases Hopt with ⟨%pad, Htag, Hpad⟩
    iexists (wordPair 0 pad)
    ihave Hcell : pointsTo_u64 memId p (wordPair 0 pad) $$ [Htag Hpad]
    · iapply (pointsTo_u32_pair_as_groupWord memId p 0 pad).mp
      iframe Htag Hpad
    iframe Hcell
    iintro Hback
    ihave ⟨Htag, Hpad⟩ :=
      (pointsTo_u32_pair_as_groupWord memId p 0 pad).mpr $$ Hback
    isimp only [Table.optionU32At]
    iexists pad
    iframe Htag Hpad
  | some v =>
    iintro Hopt
    isimp only [Table.optionU32At] at Hopt
    icases Hopt with ⟨Htag, Hpay⟩
    iexists (wordPair 1 v)
    ihave Hcell : pointsTo_u64 memId p (wordPair 1 v) $$ [Htag Hpay]
    · iapply (pointsTo_u32_pair_as_groupWord memId p 1 v).mp
      iframe Htag Hpay
    iframe Hcell
    iintro Hback
    ihave ⟨Htag, Hpay⟩ :=
      (pointsTo_u32_pair_as_groupWord memId p 1 v).mpr $$ Hback
    isimp only [Table.optionU32At]
    iframe Htag Hpay

end Memory

/-! ## The entry bound of an accepted input -/

/-- An accepted input holds at most `67108863` pairs.  The read phase puts
the input in a vector whose capacity is at most `536870912` bytes, the
input is no longer than that capacity, and an accepted input spends four
bytes on the key and four more on the pair header, so eight bytes of the
capacity are not pairs. -/
theorem acceptedEntries_le_max (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : KeyDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedEntries input).length ≤ 67108863 := by
  obtain ⟨hfour, _hdec, hexact⟩ := haccept
  have hcap := hfacts.capacity_le
  have hmap : (mapBytes input).length = input.length - 4 := by
    unfold mapBytes
    rw [List.length_drop]
  rw [ContainsKeyTailProof.acceptedEntries_length]
  omega

/-- The bound that the resize edge asks for.  Absolute `func 14` rejects a
capacity above `maxTableCapacity`, and an accepted input never reaches
it. -/
theorem acceptedEntries_le_maxTable (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : KeyDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedEntries input).length ≤ EntryContracts.maxTableCapacity := by
  have h := acceptedEntries_le_max input capacity ptr frontier haccept
    hfacts hfits
  rw [EntryContracts.maxTableCapacity_eq]
  omega

/-- The bound that the table model asks for. -/
theorem acceptedEntries_le_model (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : KeyDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedEntries input).length ≤ 2 ^ 30 := by
  have h := acceptedEntries_le_max input capacity ptr frontier haccept
    hfacts hfits
  have hpow : (2 : Nat) ^ 30 = 1073741824 := by norm_num
  omega

/-! ## The output bytes -/

/-- The output of `map_remove` on an accepted input, in the shape that the
tail holds after its two calls.  The first half is the answer that
`Project.RustHashMap.MapOpContracts.Func8Spec` leaves at `out`, at the
line `HashMap.Table.optionU32At 0 out (HashMap.Table.remove ... key).1`.
The second half is the pair list that
`Project.RustHashMap.EntriesContracts.Func4Spec` leaves in the pair
vector, at the line
`PairVecAt heapId allocationId capacity.toNat ptr
(HashMap.sortByKey (HashMap.Table.toList t))`, and that
`Project.RustHashMap.EntriesContracts.Func5Spec` writes with
`HashMap.serializeEntries`. -/
theorem removeOutput_of_accepts (bytes : List UInt8) (k0 k1 : UInt64)
    (haccept : KeyDecodeAccepts bytes)
    (hn : (acceptedEntries bytes).length ≤ 2 ^ 30) :
    Spec.removeOutput bytes =
      Borsh.option Borsh.u32
          (Table.remove (SipHash.hashU32 k0 k1)
            (Table.ofEntries (SipHash.hashU32 k0 k1)
              (acceptedEntries bytes)) (leadingKey bytes)).1 ++
        HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
          (HashMap.sortByKey (Table.toList
            (Table.remove (SipHash.hashU32 k0 k1)
              (Table.ofEntries (SipHash.hashU32 k0 k1)
                (acceptedEntries bytes)) (leadingKey bytes)).2)) := by
  obtain ⟨hone, htwo⟩ :=
    Table.remove_ofEntries_u32 k0 k1 (acceptedEntries bytes) hn
      (leadingKey bytes)
  unfold Spec.removeOutput
  rw [keyAndMap_of_accepts bytes haccept]
  simp only [Borsh.hashMap, hone, htwo]

/-- The output of `map_remove` on a rejected input.  The three shapes that
reject are a short input, a payload that stops before the header says, and
a payload with bytes left over. -/
theorem removeOutput_of_not_accepts (bytes : List UInt8)
    (hreject : ¬ KeyDecodeAccepts bytes) : Spec.removeOutput bytes = [] := by
  unfold Spec.removeOutput
  rw [keyAndMap_eq_none_of_not_accepts bytes hreject]

end Project.RustHashMap.RemovePures
