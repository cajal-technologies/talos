import Project.RustHashMap.RemovePures
import Project.RustHashMap.MapOpContracts
import Project.RustHashMap.EntriesContracts

/-!
# The pure lemmas of the `map_insert` driver tail

`map_insert` is absolute `func 3`.  Its tail calls three bodies in a
row: absolute `func 6` inserts the pair, absolute `func 7` sorts the
entries that stay, and absolute `func 8` writes the reply.  The
contracts of the three are
`Project.RustHashMap.MapOpContracts.Func3Spec`,
`Project.RustHashMap.EntriesContracts.Func4Spec` and
`Project.RustHashMap.EntriesContracts.Func5Spec`.

This file holds the facts that the tail needs and that say nothing
about the compiled state.  `Project.RustHashMap.RemovePures` is the
template.  The one difference is the input shape: `map_remove` reads
`key ++ map` and `map_insert` reads `key ++ value ++ map`, so every
name here reads the map from `bytes.drop 8` and not from
`bytes.drop 4`.

## The four groups

* The input model.  `InsertDecodeAccepts` is the accepting test of the
  read phase.  `leadingValue` and `acceptedInsertEntries` name the two
  parts that the key decoder of `map_remove` does not have.
* The entry bound.  `acceptedInsertEntries_le_max` bounds the entry
  count of an accepted input by `67108862`.  Eight bytes carry one
  pair, the input vector holds at most `536870912` bytes, and an
  accepted input spends four bytes on the key, four on the value and
  four on the pair header.
* The output bytes.  `insertOutput_of_accepts` names
  `Project.RustHashMap.Spec.insertOutput` in the shape that the two
  contracts hand out, and `insertOutput_of_not_accepts` gives the empty
  answer on the shapes that the read phase rejects.
* The table facts.  `Func3Spec` asks for `t.items < maxTableCapacity`,
  `t.buckets <= 2 ^ 27` and `t.growthLeft < UInt32.size`.  The four
  lemmas of the last section give the three from the well-formedness of
  the decoded table, and `buckets_insert_le` carries the bucket bound
  through the insertion to the sort that follows it.

## Why the bound is `67108862` and not `67108863`

`Project.RustHashMap.RemovePures.acceptedEntries_le_max` reads an input
that spends eight bytes before the pairs.  An insert input spends
twelve, because the value sits between the key and the map header.  The
extra four bytes take one pair off the bound.
-/

namespace Project.RustHashMap.InsertPures

open Wasm Wasm.RustStd
open Wasm.RustStd.HashMap
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.LookupPures
open Project.RustHashMap.VecGrow

/-! ## The model of an insert input -/

/-- The bytes that the map decoder reads.  The key takes the first four
bytes and the value the four behind it. -/
def insertMapBytes (bytes : List UInt8) : List UInt8 := bytes.drop 8

/-- The value of an input shaped `key ++ value ++ map`.  A borsh tuple
has no framing of its own, so the value is the second word. -/
def leadingValue (bytes : List UInt8) : UInt32 :=
  WordCodec.decodeU32 ((bytes.drop 4).take 4)

/-- The pair count that the map header names. -/
def insertPairCount (bytes : List UInt8) : UInt32 :=
  headerWord (insertMapBytes bytes)

/-- The read phase accepts the input when a key and a value fit in
front, the map decoder accepts the rest, and the map decoder consumes
the rest exactly.  The first conjunct is the pair of inline guards at
WAT lines 137 to 140 and 154 to 157, which both test the original
length.  The last conjunct is the trailing-bytes test. -/
def InsertDecodeAccepts (bytes : List UInt8) : Prop :=
  8 ≤ bytes.length ∧ DecodeAccepts (insertMapBytes bytes) ∧
    4 + 8 * (insertPairCount bytes).toNat = (insertMapBytes bytes).length

/-- The map that the model reads from an accepted insert input. -/
def acceptedInsertEntries (bytes : List UInt8) :
    HashMap.Map UInt32 UInt32 :=
  BorshBridge.wireEntries (insertMapBytes bytes)

/-- The entry count of the model list is the header word. -/
theorem acceptedInsertEntries_length (bytes : List UInt8) :
    (acceptedInsertEntries bytes).length =
      (insertPairCount bytes).toNat := by
  unfold acceptedInsertEntries insertPairCount
  exact HashMap.BorshBridge.length_wireEntries _

/-! ## The entry bound of an accepted input -/

/-- An accepted input holds at most `67108862` pairs.  The read phase
puts the input in a vector whose capacity is at most `536870912` bytes,
the input is no longer than that capacity, and an accepted input spends
twelve bytes on the key, the value and the pair header. -/
theorem acceptedInsertEntries_le_max (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : InsertDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedInsertEntries input).length ≤ 67108862 := by
  obtain ⟨height, _hdec, hexact⟩ := haccept
  have hcap := hfacts.capacity_le
  have hmap : (insertMapBytes input).length = input.length - 8 := by
    unfold insertMapBytes
    rw [List.length_drop]
  rw [acceptedInsertEntries_length]
  omega

/-- The bound that the resize edge asks for.  Absolute `func 17`
rejects a capacity above `maxTableCapacity`, and an accepted input
never reaches it. -/
theorem acceptedInsertEntries_le_maxTable (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : InsertDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedInsertEntries input).length ≤
      EntryContracts.maxTableCapacity := by
  have h := acceptedInsertEntries_le_max input capacity ptr frontier
    haccept hfacts hfits
  rw [EntryContracts.maxTableCapacity_eq]
  omega

/-- The strict bound that `Func3Spec` asks for.  The contract takes
`t.items < maxTableCapacity`, and the item count of the decoded table
is at most the entry count of the input. -/
theorem acceptedInsertEntries_lt_maxTable (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : InsertDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedInsertEntries input).length <
      EntryContracts.maxTableCapacity := by
  have h := acceptedInsertEntries_le_max input capacity ptr frontier
    haccept hfacts hfits
  rw [EntryContracts.maxTableCapacity_eq]
  omega

/-- The bound that the table model asks for. -/
theorem acceptedInsertEntries_le_model (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : InsertDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (acceptedInsertEntries input).length ≤ 2 ^ 30 := by
  have h := acceptedInsertEntries_le_max input capacity ptr frontier
    haccept hfacts hfits
  have hpow : (2 : Nat) ^ 30 = 1073741824 := by norm_num
  omega

/-! ## The output bytes -/

/-- The model of an input that the read phase accepts.  The key is the
first four bytes, the value the four behind them, and the map is the
wire pairs of the rest. -/
theorem keyValueAndMap_of_accepts (bytes : List UInt8)
    (haccept : InsertDecodeAccepts bytes) :
    Spec.keyValueAndMap bytes =
      some (leadingKey bytes, leadingValue bytes,
        HashMap.ofEntries (acceptedInsertEntries bytes)) := by
  obtain ⟨height, hdec, hexact⟩ := haccept
  unfold Spec.keyValueAndMap
  rw [if_neg (by omega), Spec.mapOf,
    BorshBridge.hashMap?_eq_some_of_accepts (bytes.drop 8) hdec
      hexact.symm]
  rfl

/-- The model of an input that the read phase rejects.  Three shapes
reject: an input shorter than eight bytes, a payload that stops before
the header says, and a payload with bytes left over. -/
theorem keyValueAndMap_eq_none_of_not_accepts (bytes : List UInt8)
    (hreject : ¬ InsertDecodeAccepts bytes) :
    Spec.keyValueAndMap bytes = none := by
  unfold Spec.keyValueAndMap
  by_cases height : bytes.length < 8
  · rw [if_pos height]
  · rw [if_neg height]
    have hrest : Spec.mapOf (bytes.drop 8) = none := by
      unfold Spec.mapOf
      by_cases hdec : DecodeAccepts (insertMapBytes bytes)
      · refine BorshBridge.hashMap?_eq_none_of_trailing (bytes.drop 8)
          hdec ?_
        intro hlen
        exact hreject ⟨by omega, hdec, hlen.symm⟩
      · exact BorshBridge.hashMap?_eq_none_of_not_accepts (bytes.drop 8)
          hdec
    rw [hrest]
    rfl

/-- The output of `map_insert` on an accepted input, in the shape that
the tail holds after its two calls.  The first half is the answer that
`Project.RustHashMap.MapOpContracts.Func3Spec` leaves at `out`, at the
line `HashMap.Table.optionU32At 0 out (HashMap.Table.insert ... key
value).1`.  The second half is the pair list that
`Project.RustHashMap.EntriesContracts.Func4Spec` leaves in the pair
vector and that
`Project.RustHashMap.EntriesContracts.Func5Spec` writes with
`HashMap.serializeEntries`. -/
theorem insertOutput_of_accepts (bytes : List UInt8) (k0 k1 : UInt64)
    (haccept : InsertDecodeAccepts bytes)
    (hn : (acceptedInsertEntries bytes).length ≤ 2 ^ 30) :
    Spec.insertOutput bytes =
      Borsh.option Borsh.u32
          (Table.insert (SipHash.hashU32 k0 k1)
            (Table.ofEntries (SipHash.hashU32 k0 k1)
              (acceptedInsertEntries bytes)) (leadingKey bytes)
            (leadingValue bytes)).1 ++
        HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
          (HashMap.sortByKey (Table.toList
            (Table.insert (SipHash.hashU32 k0 k1)
              (Table.ofEntries (SipHash.hashU32 k0 k1)
                (acceptedInsertEntries bytes)) (leadingKey bytes)
              (leadingValue bytes)).2)) := by
  obtain ⟨hone, htwo⟩ :=
    Table.insert_ofEntries_u32 k0 k1 (acceptedInsertEntries bytes) hn
      (leadingKey bytes) (leadingValue bytes)
  unfold Spec.insertOutput
  rw [keyValueAndMap_of_accepts bytes haccept]
  simp only [Borsh.hashMap, hone, htwo]

/-- The output of `map_insert` on a rejected input. -/
theorem insertOutput_of_not_accepts (bytes : List UInt8)
    (hreject : ¬ InsertDecodeAccepts bytes) :
    Spec.insertOutput bytes = [] := by
  unfold Spec.insertOutput
  rw [keyValueAndMap_eq_none_of_not_accepts bytes hreject]

/-! ## The table facts of the insertion -/

/-- The bucket count of the table that `collect_entries` builds.  The
sizing reserves the exact entry count, so the table has one bucket or
the bucket count of that capacity.  This repeats the private lemma of
`Project.RustHashMap.RemoveTailProof` and the insert tail imports it
from here. -/
theorem buckets_ofEntries_le {K V : Type} [BEq K] [LawfulBEq K]
    (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30)
    (hmax : es.length ≤ 117440512) :
    (HashMap.Table.ofEntries hash es).buckets ≤ 2 ^ 27 := by
  rw [HashMap.Table.ofEntries_eq]
  have hw0 :
      HashMap.Table.WF hash (HashMap.Table.empty : HashMap.Table K V) :=
    HashMap.Table.wf_newEmpty ⟨0, by omega, by omega, rfl⟩ hash
  have hcl0 : HashMap.Table.Clean
      (HashMap.Table.empty : HashMap.Table K V) :=
    HashMap.Table.clean_newEmpty 1
  have hc : max ((HashMap.Table.empty : HashMap.Table K V).items
      + es.length)
      (HashMap.Table.bucketMaskToCapacity
        ((HashMap.Table.empty : HashMap.Table K V).buckets - 1) + 1)
      * 8 / 7 ≤ 2 ^ 32 := by
    show max (0 + es.length) (0 + 1) * 8 / 7 ≤ 2 ^ 32
    omega
  obtain ⟨hw1, hcl1, hperm1, hg1, hb1⟩ := hw0.reserve hcl0 hc
  have htl : HashMap.Table.toList
      (HashMap.Table.empty : HashMap.Table K V) = [] :=
    HashMap.Table.toList_newEmpty 1
  rw [htl] at hperm1
  obtain ⟨-, -, w3, -⟩ :=
    HashMap.Table.insertAll_inv es []
      (HashMap.Table.reserve hash HashMap.Table.empty es.length) hw1
      hcl1 hperm1 hg1
  rw [w3]
  rcases hb1 with hb1 | hb1
  · rw [hb1]
    show 1 ≤ 2 ^ 27
    omega
  · rw [hb1]
    refine HashMap.Table.capBuckets_le_of_le_max ?_
    show max (0 + es.length) (0 + 1) ≤ 117440512
    omega

/-- A table holds at most one entry for each bucket. -/
theorem items_le_buckets {hash : UInt32 → UInt64}
    {t : HashMap.Table UInt32 UInt32} (hw : HashMap.Table.WF hash t) :
    t.items ≤ t.buckets := by
  rw [hw.items_eq]
  exact HashMap.Table.length_toList_le hw.toLayout

/-- The sorted entry list is as long as the table. -/
theorem sorted_length_le_buckets {hash : UInt32 → UInt64}
    {t : HashMap.Table UInt32 UInt32} (hw : HashMap.Table.WF hash t) :
    (HashMap.sortByKey (HashMap.Table.toList t)).length ≤ t.buckets := by
  rw [(HashMap.sortByKey_perm (HashMap.Table.toList t)).length_eq]
  exact HashMap.Table.length_toList_le hw.toLayout

/-- The room of a clean table fits in a word.  `Func3Spec` takes
`t.growthLeft < UInt32.size`, because the compiled body holds the room
in one `u32`.  A clean table spends its whole capacity on the items and
the room, and the capacity of a bucket count is below that count. -/
theorem growthLeft_lt_of_wf {hash : UInt32 → UInt64}
    {t : HashMap.Table UInt32 UInt32} (hw : HashMap.Table.WF hash t)
    (hcl : HashMap.Table.Clean t) (hb : t.buckets ≤ 2 ^ 27) :
    t.growthLeft < UInt32.size := by
  have hcap := hw.shape.cap_lt
  have hclean := hcl.2
  have hsize : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 27 = 134217728 := by norm_num
  omega

/-- The bucket count after an insertion.  A table with room keeps its
buckets.  A full clean table spends its whole capacity on the items, so
the reservation asks for `items + 1` buckets, and
`maxTableCapacity` bounds that count. -/
theorem buckets_insert_le {hash : UInt32 → UInt64}
    {t : HashMap.Table UInt32 UInt32} (hw : HashMap.Table.WF hash t)
    (hcl : HashMap.Table.Clean t)
    (hitems : t.items < EntryContracts.maxTableCapacity)
    (hb : t.buckets ≤ 2 ^ 27) (k v : UInt32) :
    (HashMap.Table.insert hash t k v).2.buckets ≤ 2 ^ 27 := by
  have hpow : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have hb32 : t.buckets < 2 ^ 32 := by
    have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
    omega
  by_cases hroom : 1 ≤ t.growthLeft
  · obtain ⟨-, -, hbuckets, -, -⟩ := hw.insert_of_growth hcl hroom k v
    rw [hbuckets]
    exact hb
  · have hfull : t.items
        = HashMap.Table.bucketMaskToCapacity (t.buckets - 1) := by
      have := hcl.2
      omega
    obtain ⟨hw', hcl', -, hg, hcase⟩ :=
      hw.reserve hcl (hcl.grow_bound hw.shape hb32)
    rw [HashMap.Table.insert_eq_of_reserve k v hg]
    obtain ⟨-, -, hbuckets, -, -⟩ := hw'.insert_of_growth hcl' hg k v
    rw [hbuckets]
    rcases hcase with hcase | hcase
    · rw [hcase]
      exact hb
    · rw [hcase]
      refine HashMap.Table.capBuckets_le_of_le_max ?_
      rw [← hfull]
      rw [EntryContracts.maxTableCapacity_eq] at hitems
      omega

end Project.RustHashMap.InsertPures
