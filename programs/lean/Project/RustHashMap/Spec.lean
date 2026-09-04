import Project.RustHashMap.Program
import Interpreter.Wasm.Host.Universal
import CodeLib.RustStd.HashMap.Codec
import CodeLib.RustStd.StdioContract

/-!
# Specification for `rust_hash_map`

Five exports, one `HashMap` access pattern each.  The interface is functional:
every export reads one borsh value from standard input, applies one operation,
and writes one borsh value back.  An export that changes the map writes the
changed map, and an export that also produces a value writes the value beside
it.  Each contract is therefore stated against the pure association-list model
in `CodeLib.RustStd.HashMap.Basic` and the layouts in `CodeLib.RustStd.Borsh`
and `CodeLib.RustStd.HashMap.Codec`.

Borsh writes a map as an entry count and then the entries sorted by key, so
the bytes depend only on the content of the map and not on where the hash
function put each key.  That makes the encoding canonical, so the two exports
that write a map back out have exact contracts like the three that write a
scalar.  On the way in, borsh accepts entries in any order and keeps
the last value of a repeated key, so the header count and what `map_len`
writes can differ; `HashMap.ofEntries` is that step in the model.

`borsh::from_slice` rejects trailing bytes, so an input is accepted only when
it is exactly one encoded value.  Every rejection writes nothing.  A `None`
result writes its tag byte `[0]`, so a rejected input and a `None` result stay
distinguishable.  The encode step cannot fail: an allocation failure raises
`talos.oom` rather than an `Err`.

The contracts are partial, not total.  `read_all`, the decoder, and the map
itself all allocate in proportion to the input, so an allocation failure is a
reachable terminal outcome for every one of these exports; the `talos.oom`
host trap is therefore admitted as an alternative to a correct write, in the
shape `Project.Mergesort.Spec` uses.  Fuel, linear memory, and allocator state
stay hidden.
-/

namespace Project.RustHashMap.Spec

open Wasm Wasm.RustStd

/-- The generated module imports standard I/O plus the allocator-private,
terminal OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by
  native_decide

/-- Every import of the generated module is implemented by the universal host. -/
theorem universal_host_covers : Universal.covers «module» = true := by
  native_decide

/-- The name-keyed universal environment satisfies the matching relational
host contract regardless of generated import indices. -/
theorem universal_env_satisfies :
    (Universal.envFor «module»).Satisfies «module» (Universal.specFor «module») :=
  Universal.envFor_satisfies «module»

/-! ## Run shape

Every Talos stdio program shares this shape, so it lives in
`CodeLib.RustStd.StdioContract` rather than here.  The one name below fixes
the module, which is the only part a contract adds. -/

/-- The shared shape of all five contracts: a normal return writes exactly
`output`. -/
def WritesOrOOM (op : String) (input output : List UInt8) : Prop :=
  StdioContract.WritesOrOOM «module» op input output

/-! ## Reading the input -/

/-- The map the export decodes, or `none` when borsh rejects the bytes: a
header shorter than four bytes, a payload with a trailing partial pair, or an
entry count that disagrees with the header.  A repeated key keeps its last
value. -/
def mapOf (bytes : List UInt8) : Option (HashMap.Map UInt32 UInt32) :=
  Borsh.hashMap? WordCodec.u32le WordCodec.u32le bytes

/-- Input shaped `key ++ map`, as `map_get`, `map_contains_key` and
`map_remove` read it.  A borsh tuple has no framing, so the key is simply the
first four bytes. -/
def keyAndMap (bytes : List UInt8) :
    Option (UInt32 × HashMap.Map UInt32 UInt32) :=
  if bytes.length < 4 then none
  else (mapOf (bytes.drop 4)).map fun m =>
    (WordCodec.decodeU32 (bytes.take 4), m)

/-- Input shaped `key ++ value ++ map`, as `map_insert` reads it. -/
def keyValueAndMap (bytes : List UInt8) :
    Option (UInt32 × UInt32 × HashMap.Map UInt32 UInt32) :=
  if bytes.length < 8 then none
  else (mapOf (bytes.drop 8)).map fun m =>
    (WordCodec.decodeU32 (bytes.take 4),
      WordCodec.decodeU32 ((bytes.drop 4).take 4), m)

/-! ## Expected output of each export -/

/-- `map_len`: the entry count as a borsh `u32`; nothing when the input is
rejected.  The map holds at most one entry per wire pair, and the header
already bounds that count below `2 ^ 32`, so the Rust `as u32` cast is
exact. -/
def lenOutput (bytes : List UInt8) : List UInt8 :=
  match mapOf bytes with
  | none => []
  | some m => Borsh.u32 (UInt32.ofNat (HashMap.len m))

/-- `map_get`: the value under the leading key, as a borsh `Option`. -/
def getOutput (bytes : List UInt8) : List UInt8 :=
  match keyAndMap bytes with
  | none => []
  | some (key, m) => Borsh.option Borsh.u32 (HashMap.get m key)

/-- `map_contains_key`: whether the leading key has an entry, as a borsh
`bool`. -/
def containsKeyOutput (bytes : List UInt8) : List UInt8 :=
  match keyAndMap bytes with
  | none => []
  | some (key, m) => Borsh.bool (HashMap.containsKey m key)

/-- `map_insert`: the displaced value beside the map after the insertion, as
a borsh tuple, which has no framing of its own.  The map goes out in key order
whatever order it came in. -/
def insertOutput (bytes : List UInt8) : List UInt8 :=
  match keyValueAndMap bytes with
  | none => []
  | some (key, value, m) =>
      Borsh.option Borsh.u32 (HashMap.insert m key value).1 ++
        Borsh.hashMap WordCodec.u32le WordCodec.u32le
          (HashMap.insert m key value).2

/-- `map_remove`: the removed value beside the map after the removal, as a
borsh tuple. -/
def removeOutput (bytes : List UInt8) : List UInt8 :=
  match keyAndMap bytes with
  | none => []
  | some (key, m) =>
      Borsh.option Borsh.u32 (HashMap.remove m key).1 ++
        Borsh.hashMap WordCodec.u32le WordCodec.u32le
          (HashMap.remove m key).2

/-! ## Contracts -/

/-- `map_len` writes the entry count. -/
@[spec_of "rust-exported-partial" "rust_hash_map::map_len"]
def MapLenSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "map_len" bytes (lenOutput bytes)

/-- `map_get` writes the value under the leading key, and `None` when the key
is absent. -/
@[spec_of "rust-exported-partial" "rust_hash_map::map_get"]
def MapGetSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "map_get" bytes (getOutput bytes)

/-- `map_contains_key` writes whether the leading key has an entry. -/
@[spec_of "rust-exported-partial" "rust_hash_map::map_contains_key"]
def MapContainsKeySpec : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "map_contains_key" bytes (containsKeyOutput bytes)

/-- `map_insert` writes the displaced value beside the map after the
insertion. -/
@[spec_of "rust-exported-partial" "rust_hash_map::map_insert"]
def MapInsertSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "map_insert" bytes (insertOutput bytes)

/-- `map_remove` writes the removed value beside the map after the removal. -/
@[spec_of "rust-exported-partial" "rust_hash_map::map_remove"]
def MapRemoveSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "map_remove" bytes (removeOutput bytes)

/-- Every name the contracts mention starts a call on the generated module.
A misspelt name would make its contract false, not vacuous:
`PartiallyRunsWithOutcome` needs a start configuration. -/
theorem contract_names_start :
    ["map_len", "map_get", "map_contains_key", "map_insert", "map_remove"].all
      (fun op =>
        (startCallConfig? (Universal.envFor «module») «module» op
          (Universal.State.ofInput [])).isSome) = true := by
  native_decide

/-! ## Reading the contracts

Each contract quantifies over raw bytes.  The theorems below read them on
well-formed input, where the round trip of the entry list and
`Borsh.hashMap?_hashMap` turn the byte-level statement into one about the
association-list model.  All five exports have a reader here, so no contract is
stated and then left unapplied.  Together they exercise all three readers
(`mapOf`, `keyAndMap` and `keyValueAndMap`), the decode direction of
`Borsh.u32`, both `Option` tags, the `Borsh.bool` layout, and the map
operations `len`, `insert`, `remove`, `get` and `containsKey`.

The last four go the other way.  They bound the entry count of a decoded map,
show that such a map always has distinct keys whatever bytes arrive, and show
that the map half of what `map_insert` and `map_remove` write reads back as
that map in key order.  The output of one export is therefore well-formed
input to another. -/

/-- A borsh tuple has no framing, so a leading `u32` is the first four bytes
and the rest follows unchanged. -/
private theorem keyAndMap_u32 (key : UInt32) (rest : List UInt8) :
    keyAndMap (Borsh.u32 key ++ rest) = (mapOf rest).map fun m => (key, m) := by
  have hlen : (Borsh.u32 key).length = 4 := WordCodec.u32le_encode_length key
  have hnot : ¬ (Borsh.u32 key ++ rest).length < 4 := by
    rw [List.length_append, hlen]
    omega
  have hword : WordCodec.decodeU32 (Borsh.u32 key) = key :=
    WordCodec.u32le.decode_encode key
  rw [keyAndMap, if_neg hnot, List.take_left' hlen, List.drop_left' hlen, hword]

/-- Two leading `u32` words, then the rest. -/
private theorem keyValueAndMap_u32 (key value : UInt32) (rest : List UInt8) :
    keyValueAndMap (Borsh.u32 key ++ Borsh.u32 value ++ rest)
      = (mapOf rest).map fun m => (key, value, m) := by
  have hlen : (Borsh.u32 key).length = 4 := WordCodec.u32le_encode_length key
  have hlen' : (Borsh.u32 value).length = 4 :=
    WordCodec.u32le_encode_length value
  rw [List.append_assoc]
  have hnot : ¬ (Borsh.u32 key ++ (Borsh.u32 value ++ rest)).length < 8 := by
    rw [List.length_append, List.length_append, hlen, hlen']
    omega
  have hdrop : (Borsh.u32 key ++ (Borsh.u32 value ++ rest)).drop 4
      = Borsh.u32 value ++ rest :=
    List.drop_left' hlen
  have hdrop8 : (Borsh.u32 key ++ (Borsh.u32 value ++ rest)).drop 8 = rest := by
    rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, hdrop]
    exact List.drop_left' hlen'
  have hword : WordCodec.decodeU32 (Borsh.u32 key) = key :=
    WordCodec.u32le.decode_encode key
  have hword' : WordCodec.decodeU32 (Borsh.u32 value) = value :=
    WordCodec.u32le.decode_encode value
  rw [keyValueAndMap, if_neg hnot, List.take_left' hlen, hdrop, hdrop8,
    List.take_left' hlen', hword, hword']

/-- `MapLenSpec` on a serialized entry list: it is always accepted, so the
export writes the number of distinct keys in it. -/
theorem len_on_serialized (entries : HashMap.Map UInt32 UInt32)
    (hbound : entries.length < 2 ^ 32) :
    MapLenSpec →
      WritesOrOOM "map_len"
        (HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        (Borsh.u32 (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries)))) := by
  intro h
  have hout :
      lenOutput (HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        = Borsh.u32 (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries))) := by
    simp [lenOutput, mapOf, Borsh.hashMap?,
      HashMap.deserializeEntries_serializeEntries WordCodec.u32le WordCodec.u32le
        entries hbound]
  have hrun := h (HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
  rwa [hout] at hrun

/-- `MapLenSpec` on a serialized entry list whose keys do not repeat: the
export writes the number of entries.  `ofEntries` only ever loses the earlier
value of a repeated key, so the wire round trip is lossless for a list that
really came from a `HashMap`. -/
theorem len_on_serialized_nodup (entries : HashMap.Map UInt32 UInt32)
    (hnodup : HashMap.NodupKeys entries) (hbound : entries.length < 2 ^ 32) :
    MapLenSpec →
      WritesOrOOM "map_len"
        (HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        (Borsh.u32 (UInt32.ofNat entries.length)) := by
  intro h
  have hrun := len_on_serialized entries hbound h
  rw [HashMap.ofEntries_eq_self_of_nodup hnodup] at hrun
  exact hrun

/-- `MapInsertSpec` on a serialized entry list behind a key and a value: the
export writes the displaced value and the map after the insertion, in key
order.  The two halves of that output are what makes the contract functional
rather than a bare map. -/
theorem insert_on_serialized (key value : UInt32)
    (entries : HashMap.Map UInt32 UInt32) (hbound : entries.length < 2 ^ 32) :
    MapInsertSpec →
      WritesOrOOM "map_insert"
        (Borsh.u32 key ++ Borsh.u32 value ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        (Borsh.option Borsh.u32
            (HashMap.insert (HashMap.ofEntries entries) key value).1 ++
          Borsh.hashMap WordCodec.u32le WordCodec.u32le
            (HashMap.insert (HashMap.ofEntries entries) key value).2) := by
  intro h
  have hout :
      insertOutput (Borsh.u32 key ++ Borsh.u32 value ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        = Borsh.option Borsh.u32
              (HashMap.insert (HashMap.ofEntries entries) key value).1 ++
            Borsh.hashMap WordCodec.u32le WordCodec.u32le
              (HashMap.insert (HashMap.ofEntries entries) key value).2 := by
    rw [insertOutput, keyValueAndMap_u32]
    simp [mapOf, Borsh.hashMap?,
      HashMap.deserializeEntries_serializeEntries WordCodec.u32le WordCodec.u32le
        entries hbound]
  have hrun := h (Borsh.u32 key ++ Borsh.u32 value ++
    HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
  rwa [hout] at hrun

/-- `MapGetSpec` on a borsh map whose keys do not repeat: the export writes
the value under the key.  The map goes in through the canonical encoding, so
the sorted map it decodes to reads as the map itself through
`HashMap.get_sortByKey`. -/
theorem get_on_hashMap (key : UInt32) (m : HashMap.Map UInt32 UInt32)
    (hnodup : HashMap.NodupKeys m) (hbound : m.length < 2 ^ 32) :
    MapGetSpec →
      WritesOrOOM "map_get"
        (Borsh.u32 key ++ Borsh.hashMap WordCodec.u32le WordCodec.u32le m)
        (Borsh.option Borsh.u32 (HashMap.get m key)) := by
  intro h
  have hout :
      getOutput (Borsh.u32 key ++ Borsh.hashMap WordCodec.u32le WordCodec.u32le m)
        = Borsh.option Borsh.u32 (HashMap.get m key) := by
    rw [getOutput, keyAndMap_u32]
    simp [mapOf,
      Borsh.hashMap?_hashMap WordCodec.u32le WordCodec.u32le hnodup hbound,
      HashMap.get_sortByKey hnodup]
  have hrun := h (Borsh.u32 key ++ Borsh.hashMap WordCodec.u32le WordCodec.u32le m)
  rwa [hout] at hrun

/-- `MapGetSpec` on the empty map: the export writes the bare `None` tag. -/
theorem get_on_empty (key : UInt32) :
    MapGetSpec →
      WritesOrOOM "map_get"
        (Borsh.u32 key ++ Borsh.hashMap WordCodec.u32le WordCodec.u32le [])
        (Borsh.option Borsh.u32 none) := by
  simpa [HashMap.get] using
    get_on_hashMap key [] (by simp [HashMap.NodupKeys]) (by simp)

/-- `MapGetSpec` on a one-entry map under that entry's own key: the export
writes the `Some` tag and the value. -/
theorem get_on_singleton (key value : UInt32) :
    MapGetSpec →
      WritesOrOOM "map_get"
        (Borsh.u32 key ++
          Borsh.hashMap WordCodec.u32le WordCodec.u32le [(key, value)])
        (Borsh.option Borsh.u32 (some value)) := by
  simpa [HashMap.get] using
    get_on_hashMap key [(key, value)] (by simp [HashMap.NodupKeys]) (by simp)

/-- `MapContainsKeySpec` on a serialized entry list behind a key: the export
writes the borsh `bool` of whether that key has an entry in the map the list
denotes.  This is the only contract whose output is a `bool`, so it is the
only one that reads the `Borsh.bool` layout back. -/
theorem containsKey_on_serialized (key : UInt32)
    (entries : HashMap.Map UInt32 UInt32) (hbound : entries.length < 2 ^ 32) :
    MapContainsKeySpec →
      WritesOrOOM "map_contains_key"
        (Borsh.u32 key ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        (Borsh.bool (HashMap.containsKey (HashMap.ofEntries entries) key)) := by
  intro h
  have hout :
      containsKeyOutput (Borsh.u32 key ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        = Borsh.bool (HashMap.containsKey (HashMap.ofEntries entries) key) := by
    rw [containsKeyOutput, keyAndMap_u32]
    simp [mapOf, Borsh.hashMap?,
      HashMap.deserializeEntries_serializeEntries WordCodec.u32le WordCodec.u32le
        entries hbound]
  have hrun := h (Borsh.u32 key ++
    HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
  rwa [hout] at hrun

/-- `MapRemoveSpec` on a serialized entry list behind a key: the export writes
the removed value beside the map after the removal, in key order.  The two
halves of that output are what makes the contract functional rather than a
bare map. -/
theorem remove_on_serialized (key : UInt32)
    (entries : HashMap.Map UInt32 UInt32) (hbound : entries.length < 2 ^ 32) :
    MapRemoveSpec →
      WritesOrOOM "map_remove"
        (Borsh.u32 key ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        (Borsh.option Borsh.u32
            (HashMap.remove (HashMap.ofEntries entries) key).1 ++
          Borsh.hashMap WordCodec.u32le WordCodec.u32le
            (HashMap.remove (HashMap.ofEntries entries) key).2) := by
  intro h
  have hout :
      removeOutput (Borsh.u32 key ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
        = Borsh.option Borsh.u32
              (HashMap.remove (HashMap.ofEntries entries) key).1 ++
            Borsh.hashMap WordCodec.u32le WordCodec.u32le
              (HashMap.remove (HashMap.ofEntries entries) key).2 := by
    rw [removeOutput, keyAndMap_u32]
    simp [mapOf, Borsh.hashMap?,
      HashMap.deserializeEntries_serializeEntries WordCodec.u32le WordCodec.u32le
        entries hbound]
  have hrun := h (Borsh.u32 key ++
    HashMap.serializeEntries WordCodec.u32le WordCodec.u32le entries)
  rwa [hout] at hrun

/-- Whatever bytes an export accepts, the map it decodes has distinct keys:
`mapOf` ends in `HashMap.ofEntries`, which inserts.  Every lemma about the wire
format takes key uniqueness as a hypothesis, so this is what lets a contract use
those lemmas at the map it really holds. -/
theorem nodupKeys_of_mapOf {bytes : List UInt8}
    {m : HashMap.Map UInt32 UInt32} (h : mapOf bytes = some m) :
    HashMap.NodupKeys m := by
  rw [mapOf, Borsh.hashMap?, Option.map_eq_some_iff] at h
  obtain ⟨entries, _, hm⟩ := h
  exact hm ▸ HashMap.nodupKeys_ofEntries entries

/-- The map a contract decodes is short enough for the encoding to read back.
The wire carries the entry count in a `u32` header, and `ofEntries` only ever
drops a repeated key, so the bound holds for whatever bytes arrive.  Every
lemma about the wire format asks for this bound, so one derivation is what
lets the two theorems below take the hypothesis a caller really has. -/
theorem length_of_mapOf {bytes : List UInt8}
    {m : HashMap.Map UInt32 UInt32} (h : mapOf bytes = some m) :
    m.length < 2 ^ 32 := by
  rw [mapOf, Borsh.hashMap?, Option.map_eq_some_iff] at h
  obtain ⟨entries, hentries, hm⟩ := h
  exact hm ▸ Nat.lt_of_le_of_lt (HashMap.length_ofEntries_le entries)
    (HashMap.length_of_deserializeEntries hentries)

/-- What `map_insert` writes, another export can read.  The map half of its
output is the canonical encoding of a map with distinct keys, so `mapOf`
recovers that map in key order.

The caller still has to supply room for one more entry.  `length_of_mapOf`
gives `m.length < 2 ^ 32` on its own, but an insert under a fresh key appends,
so at the very top of the range the count would leave what a `u32` header can
carry.  The hypothesis is stated about the decoded map rather than about the
result of the insert, which is the map a caller holds. -/
theorem mapOf_insert_output {bytes : List UInt8}
    {m : HashMap.Map UInt32 UInt32} (h : mapOf bytes = some m)
    (key value : UInt32) (hroom : m.length + 1 < 2 ^ 32) :
    mapOf (Borsh.hashMap WordCodec.u32le WordCodec.u32le
        (HashMap.insert m key value).2)
      = some (HashMap.sortByKey (HashMap.insert m key value).2) :=
  Borsh.hashMap?_hashMap _ _
    (HashMap.nodupKeys_insert (nodupKeys_of_mapOf h) key value)
    (Nat.lt_of_le_of_lt (HashMap.length_insert_le m key value) hroom)

/-- The same for `map_remove`, and with no bound to supply at all: a remove
only ever drops an entry, so `length_of_mapOf` closes it outright. -/
theorem mapOf_remove_output {bytes : List UInt8}
    {m : HashMap.Map UInt32 UInt32} (h : mapOf bytes = some m) (key : UInt32) :
    mapOf (Borsh.hashMap WordCodec.u32le WordCodec.u32le
        (HashMap.remove m key).2)
      = some (HashMap.sortByKey (HashMap.remove m key).2) :=
  Borsh.hashMap?_hashMap _ _
    (HashMap.nodupKeys_remove (nodupKeys_of_mapOf h) key)
    (Nat.lt_of_le_of_lt (HashMap.length_remove_le m key) (length_of_mapOf h))

end Project.RustHashMap.Spec
