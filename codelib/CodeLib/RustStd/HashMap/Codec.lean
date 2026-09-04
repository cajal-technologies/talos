import CodeLib.RustStd.HashMap.Basic
import CodeLib.RustStd.Borsh

/-!
# Wire format for `HashMap`

A serialized map is a serialized list of key/value pairs, so this file adds one
thing to `CodeLib.RustStd.Vec.Codec`: a `WordCodec` for pairs.  Everything else
is the `Vec` length-prefixed format applied at the pair type, which is why
`deserializeEntries_serializeEntries` below is a corollary rather than a new
proof.

The entry list is the wire format in *any* order.  Borsh, the format the Talos
stdio programs use, pins the order on the way out: it collects the entries and
sorts them by key, so the bytes depend only on the content of the map and not
on where the hash function put each key.  On the way back it reads a list of
pairs and collects it, so the entries may arrive in any order and a repeated
key keeps its last value.  The `Borsh` section at the end names those two
operations, `hashMap` and `hashMap?`, over `HashMap.sortByKey` and
`HashMap.ofEntries`, the way `Borsh.vec` names `Vec.serialize`.  The sort is
what makes the encoding canonical, and a canonical encoding is what lets a
contract say exactly which bytes an export writes.

Consumer: `Project.RustHashMap.Spec`, whose contracts decode with
`Borsh.hashMap?` and encode with `Borsh.hashMap`, and are read back on
well-formed input through `deserializeEntries_serializeEntries` and
`hashMap?_hashMap`.
-/

namespace Wasm.RustStd.HashMap

open Wasm.RustStd

variable {K V : Type}

/-- Two fixed-width codecs side by side.  The key occupies the first
`kc.width` bytes of each word, the value the remaining `vc.width`. -/
def pairCodec (kc : WordCodec K) (vc : WordCodec V) : WordCodec (K × V) where
  width := kc.width + vc.width
  encode entry := kc.encode entry.1 ++ vc.encode entry.2
  decode bytes :=
    (kc.decode (bytes.take kc.width), vc.decode (bytes.drop kc.width))
  width_pos := by have := kc.width_pos; omega
  encode_length := by
    intro entry
    simp [kc.encode_length, vc.encode_length]
  decode_encode := by
    intro entry
    have hk : (kc.encode entry.1).length = kc.width := kc.encode_length entry.1
    rw [Prod.ext_iff]
    constructor
    · simpa [List.take_left' hk] using kc.decode_encode entry.1
    · simpa [List.drop_left' hk] using vc.decode_encode entry.2

/-- The length-prefixed encoding of an entry list in the order given. -/
def serializeEntries (kc : WordCodec K) (vc : WordCodec V)
    (entries : Map K V) : List UInt8 :=
  Vec.serialize (pairCodec kc vc) entries

/-- Recover the entry list from its length-prefixed encoding. -/
def deserializeEntries (kc : WordCodec K) (vc : WordCodec V)
    (bytes : List UInt8) : Option (Map K V) :=
  Vec.deserialize (pairCodec kc vc) bytes

/-- Round trip, inherited from the `Vec` format at the pair type.

Consumers: `hashMap?_hashMap` below, and `len_on_serialized`,
`insert_on_serialized`, `containsKey_on_serialized`, and
`remove_on_serialized` in `Project.RustHashMap.Spec`. -/
theorem deserializeEntries_serializeEntries (kc : WordCodec K)
    (vc : WordCodec V) (entries : Map K V) (hbound : entries.length < 2 ^ 32) :
    deserializeEntries kc vc (serializeEntries kc vc entries) = some entries :=
  Vec.deserialize_serialize (pairCodec kc vc) entries hbound

/-- A decoded entry list is already short enough for the format that produced
it.  The reader accepts a payload only when its pair count equals the `u32`
header, and a `u32` is below `2 ^ 32`, so the bound every encoding lemma asks
for comes free with the decode.

Consumer: `Project.RustHashMap.Spec.length_of_mapOf`. -/
theorem length_of_deserializeEntries {kc : WordCodec K} {vc : WordCodec V}
    {bytes : List UInt8} {entries : Map K V}
    (h : deserializeEntries kc vc bytes = some entries) :
    entries.length < 2 ^ 32 := by
  rw [deserializeEntries, Vec.deserialize] at h
  split at h
  · simp at h
  · cases hdes : (pairCodec kc vc).deserialize (bytes.drop 4) with
    | none => rw [hdes] at h; simp at h
    | some values =>
        rw [hdes] at h
        dsimp only at h
        split_ifs at h with hcount
        · have hev : values = entries := by simp at h; exact h
          subst hev
          rw [hcount]
          exact (WordCodec.decodeU32 (bytes.take 4)).toNat_lt

end Wasm.RustStd.HashMap

namespace Wasm.RustStd.Borsh

open Wasm.RustStd

variable {K V : Type}

/-- A `HashMap`, as a `u32` little-endian entry count followed by the entries
in key order.  This is `HashMap.serializeEntries` at the sorted list, which
is `vec` at the pair codec. -/
def hashMap [LE K] [DecidableRel (α := K) (· ≤ ·)] (kc : WordCodec K)
    (vc : WordCodec V) (m : HashMap.Map K V) : List UInt8 :=
  HashMap.serializeEntries kc vc (HashMap.sortByKey m)

/-- Read a `HashMap` back.  Borsh decodes the entry list and collects it, so
the entries may arrive in any order and a repeated key keeps its last value;
`HashMap.ofEntries` is that collection.  Every failure mode is `none`, and
an entry count that disagrees with the header is one of them. -/
def hashMap? [BEq K] (kc : WordCodec K) (vc : WordCodec V)
    (bytes : List UInt8) : Option (HashMap.Map K V) :=
  (HashMap.deserializeEntries kc vc bytes).map HashMap.ofEntries

/-- The `HashMap` round trip: a map whose keys do not repeat comes back as its
own entries in key order.  `ofEntries` only ever loses the earlier value of a
repeated key, and a `HashMap` has none.

Consumers: `Project.RustHashMap.Spec.get_on_hashMap`, `mapOf_insert_output`,
and `mapOf_remove_output`. -/
theorem hashMap?_hashMap [BEq K] [LawfulBEq K] [LE K]
    [DecidableRel (α := K) (· ≤ ·)] (kc : WordCodec K) (vc : WordCodec V)
    {m : HashMap.Map K V} (hnodup : HashMap.NodupKeys m)
    (hbound : m.length < 2 ^ 32) :
    hashMap? kc vc (hashMap kc vc m) = some (HashMap.sortByKey m) := by
  have hlen : (HashMap.sortByKey m).length < 2 ^ 32 := by
    rw [(HashMap.sortByKey_perm m).length_eq]
    exact hbound
  simp [hashMap?, hashMap,
    HashMap.deserializeEntries_serializeEntries kc vc _ hlen,
    HashMap.ofEntries_eq_self_of_nodup (HashMap.nodupKeys_sortByKey hnodup)]

end Wasm.RustStd.Borsh
