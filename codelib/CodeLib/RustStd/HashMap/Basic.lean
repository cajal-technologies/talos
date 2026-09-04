/-!
# A pure model of the safe `HashMap` surface

`std::collections::HashMap` is modelled as an association list.  The list is
the *observable* content of the map: a key/value pair for each live entry.
The hash table, its buckets, its hash function and its capacity are all
absent, exactly as capacity is absent from the `Vec` model in
`CodeLib.RustStd.Vec.Basic`.

Two things the Rust type guarantees are carried explicitly rather than built
into the representation:

* **Key uniqueness** is the predicate `NodupKeys`, not a subtype invariant.  A
  bare `List (K × V)` keeps the model computable and keeps every lemma
  statement free of proof arguments.
* **Order is a property of the operations, not of the list.**  Nothing here
  forces the list into an order, so a model map and a Rust map with the same
  entries are the same value whatever order the list arrived in.  A `HashMap`
  has no specified iteration order, so the wire cannot use that order.  The
  encoder sorts the entries by key instead, which gives one byte string for
  one map.  `sortByKey` is that step, and `CodeLib.RustStd.HashMap.Codec`
  builds the encoding on it.

Like `CodeLib.RustStd.Vec.Basic`, this file is a spec-level model rather than
a wasm-level `_wp` lemma file.  Its consumer is `Project.RustHashMap.Spec`,
which states the contract of each `rust_hash_map` export in these terms.
Lemmas arrive with the first proof that needs them: `ofEntries_eq_self_of_nodup`,
`sortByKey_perm` and `nodupKeys_sortByKey` serve the wire round trip in
`CodeLib.RustStd.HashMap.Codec`, and `get_sortByKey` serves the contract that
reads it back.  `nodupKeys_insert`, `nodupKeys_ofEntries` and `nodupKeys_remove`
discharge the key-uniqueness hypothesis those lemmas take, for the map an export
decodes rather than for an arbitrary list; without them a reader can state the
round trip but cannot apply it.  The algebra of `insert` and `remove` against
`get` waits for a proof that needs it.
-/

namespace Wasm.RustStd.HashMap

variable {K V : Type}

/-- The observable content of a map: one pair per live entry. -/
abbrev Map (K V : Type) := List (K × V)

/-- Every key occurs at most once. -/
def NodupKeys (m : Map K V) : Prop := (m.map Prod.fst).Nodup

/-- The value stored under `key`, if any. -/
def get [BEq K] (m : Map K V) (key : K) : Option V :=
  (m.find? (fun entry => entry.1 == key)).map Prod.snd

/-- Whether `key` has a live entry. -/
def containsKey [BEq K] (m : Map K V) (key : K) : Bool :=
  (m.find? (fun entry => entry.1 == key)).isSome

/-- The number of live entries. -/
def len (m : Map K V) : Nat := m.length

/-- `HashMap::insert`: replace the value under `key` in place when the key is
present, otherwise append a new entry.  Returns the displaced value alongside
the updated map, matching the Rust return type `Option<V>`.

Replacement is in place, so `insert` never reorders live entries.  That is a
property of this model.  A Rust `HashMap` offers no order at all, and
`sortByKey` is where the two agree. -/
def insert [BEq K] (m : Map K V) (key : K) (value : V) : Option V × Map K V :=
  match m.find? (fun entry => entry.1 == key) with
  | none => (none, m ++ [(key, value)])
  | some old =>
      (some old.2,
        m.map (fun entry => if entry.1 == key then (key, value) else entry))

/-- `HashMap::remove`: drop the entry under `key` and return its value. -/
def remove [BEq K] (m : Map K V) (key : K) : Option V × Map K V :=
  (get m key, m.filter (fun entry => !(entry.1 == key)))

/-- `HashMap::from_iter`, which is what `collect::<HashMap<_, _>>()` calls:
insert each entry in turn, so a later value under a key already seen replaces
the earlier one.  The result therefore has one entry per *distinct* key, and
is shorter than `entries` whenever a key repeats.

This is the operation a driver performs when it reads a map off the wire, so
it is what stands between `CodeLib.RustStd.HashMap.Codec` (which decodes a
list of pairs, duplicates and all) and the map the contracts talk about. -/
def ofEntries [BEq K] (entries : List (K × V)) : Map K V :=
  entries.foldl (fun m entry => (insert m entry.1 entry.2).2) []

/-- The entries reordered by the key ordering the caller supplies.  A `HashMap`
has no order of its own, so the encoder picks one and sorts the entries by key.
That is the one order a serialized map can show.  The sort of a map whose keys
do not repeat is a permutation that no operation here observes. -/
def sortByKey [LE K] [DecidableRel (α := K) (· ≤ ·)] (m : Map K V) : Map K V :=
  m.mergeSort (fun a b => decide (a.1 ≤ b.1))

/-- The sort only reorders the entries.

Consumers: `Wasm.RustStd.Borsh.hashMap?_hashMap`, through `nodupKeys_sortByKey`
and the length bound of the entry codec, and `get_sortByKey` below. -/
theorem sortByKey_perm [LE K] [DecidableRel (α := K) (· ≤ ·)] (m : Map K V) :
    (sortByKey m).Perm m :=
  List.mergeSort_perm m _

/-- The sort keeps the keys distinct.

Consumer: `Wasm.RustStd.Borsh.hashMap?_hashMap`. -/
theorem nodupKeys_sortByKey [LE K] [DecidableRel (α := K) (· ≤ ·)] {m : Map K V}
    (h : NodupKeys m) : NodupKeys (sortByKey m) :=
  ((sortByKey_perm m).map Prod.fst).nodup_iff.mpr h

/-- A key with no entry is found by nothing. -/
private theorem find?_eq_none_of_key_not_mem [BEq K] [LawfulBEq K]
    {m : Map K V} {key : K} (h : key ∉ m.map Prod.fst) :
    m.find? (fun entry => entry.1 == key) = none := by
  rw [List.find?_eq_none]
  intro entry hmem hbeq
  have hkey : entry.1 = key := by simpa using hbeq
  exact h (List.mem_map.mpr ⟨entry, hmem, hkey⟩)

/-- An insert of entries whose keys the accumulator does not already hold
just appends them, in order. -/
private theorem foldl_insert_eq_append [BEq K] [LawfulBEq K] :
    ∀ (entries acc : Map K V), NodupKeys entries →
      (∀ entry ∈ entries, entry.1 ∉ acc.map Prod.fst) →
      entries.foldl (fun m entry => (insert m entry.1 entry.2).2) acc
        = acc ++ entries := by
  intro entries
  induction entries with
  | nil => intro acc _ _; simp
  | cons entry rest ih =>
      intro acc hnodup hfresh
      have hstep : (insert acc entry.1 entry.2).2 = acc ++ [entry] := by
        simp [insert, find?_eq_none_of_key_not_mem (hfresh entry (by simp))]
      have hcons : entry.1 ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
        simpa [NodupKeys, List.nodup_cons] using hnodup
      have hfresh' : ∀ x ∈ rest, x.1 ∉ (acc ++ [entry]).map Prod.fst := by
        intro x hx hmem
        simp only [List.map_append, List.mem_append, List.map_cons,
          List.map_nil, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact hfresh x (by simp [hx]) hmem
        · exact hcons.1 (hmem ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
      have := ih (acc ++ [entry]) hcons.2 hfresh'
      simp only [List.foldl_cons, hstep, this, List.append_assoc,
        List.singleton_append]

/-- A map read back from a list whose keys do not repeat is that list
unchanged.  This is what makes a wire round trip lossless for a map that
really came from a `HashMap`: `ofEntries` only ever loses the earlier value of
a repeated key, and a `HashMap` has none.

Consumers: `Wasm.RustStd.Borsh.hashMap?_hashMap` and
`Project.RustHashMap.Spec.len_on_serialized_nodup`. -/
theorem ofEntries_eq_self_of_nodup [BEq K] [LawfulBEq K] {entries : Map K V}
    (h : NodupKeys entries) : ofEntries entries = entries := by
  simpa [ofEntries] using foldl_insert_eq_append entries [] h (by simp)

/-- An insert keeps the keys distinct.  A fresh key is appended once, and a key
already present is replaced in place, which leaves the key list unchanged.

Consumers: `nodupKeys_ofEntries` below, and
`Project.RustHashMap.Spec.mapOf_insert_output`. -/
theorem nodupKeys_insert [BEq K] [LawfulBEq K] {m : Map K V} (h : NodupKeys m)
    (key : K) (value : V) : NodupKeys (insert m key value).2 := by
  unfold insert
  cases hfind : m.find? (fun entry => entry.1 == key) with
  | none =>
    have hnot : key ∉ m.map Prod.fst := by
      intro hmem
      obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hmem
      rw [List.find?_eq_none] at hfind
      exact hfind entry hentry (by simp [hkey])
    simp only [NodupKeys, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton.mp hb] at hab
    exact hnot (hab ▸ ha)
  | some old =>
    have hkeys :
        (m.map (fun entry => if entry.1 == key then (key, value) else entry)).map Prod.fst
          = m.map Prod.fst := by
      rw [List.map_map]
      apply List.map_congr_left
      intro entry _
      by_cases hb : entry.1 == key
      · simp [Function.comp, eq_of_beq hb]
      · simp [Function.comp, hb]
    simpa [NodupKeys, hkeys] using h

/-- Every map read off the wire has distinct keys.  `ofEntries` builds the map
with `insert`, and `insert` keeps the keys distinct, so no contract ever has
to assume the invariant of a decoded map.

Consumer: `Project.RustHashMap.Spec.nodupKeys_of_mapOf`. -/
theorem nodupKeys_ofEntries [BEq K] [LawfulBEq K] (entries : List (K × V)) :
    NodupKeys (ofEntries entries) := by
  have haux : ∀ (es : List (K × V)) (acc : Map K V), NodupKeys acc →
      NodupKeys (es.foldl (fun m entry => (insert m entry.1 entry.2).2) acc) := by
    intro es
    induction es with
    | nil => intro acc hacc; simpa using hacc
    | cons entry rest ih =>
        intro acc hacc
        exact ih _ (nodupKeys_insert hacc entry.1 entry.2)
  exact haux entries [] (by simp [NodupKeys])

/-- A remove keeps the keys distinct.  The filter only drops entries, and a
sublist of a key list without repeats has none either.

Consumer: `Project.RustHashMap.Spec.mapOf_remove_output`. -/
theorem nodupKeys_remove [BEq K] {m : Map K V} (h : NodupKeys m) (key : K) :
    NodupKeys (remove m key).2 :=
  List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) h

/-- With distinct keys, two entries under the same key are the same entry. -/
private theorem eq_of_key_eq_of_nodupKeys :
    ∀ {m : Map K V}, NodupKeys m →
      ∀ {e e' : K × V}, e ∈ m → e' ∈ m → e.1 = e'.1 → e = e'
  | [], _, _, _, he, _, _ => by simp at he
  | x :: rest, hnodup, e, e', he, he', hk => by
      have hcons : x.1 ∉ rest.map Prod.fst ∧ NodupKeys rest := by
        simpa [NodupKeys, List.nodup_cons] using hnodup
      have hhead : ∀ {f : K × V}, f ∈ rest → f.1 = x.1 → False :=
        fun hf hfx => hcons.1 (List.mem_map.mpr ⟨_, hf, hfx⟩)
      rcases List.mem_cons.mp he with he | he <;>
        rcases List.mem_cons.mp he' with he' | he'
      · exact he.trans he'.symm
      · exact (hhead he' (hk.symm.trans (congrArg Prod.fst he))).elim
      · exact (hhead he (hk.trans (congrArg Prod.fst he'))).elim
      · exact eq_of_key_eq_of_nodupKeys hcons.2 he he' hk

/-- The sorted map reads as the map: with distinct keys at most one entry
answers to `key`, and the sort keeps every entry.

Consumer: `Project.RustHashMap.Spec.get_on_hashMap`. -/
theorem get_sortByKey [BEq K] [LawfulBEq K] [LE K] [DecidableRel (α := K) (· ≤ ·)]
    {m : Map K V} (h : NodupKeys m) (key : K) :
    get (sortByKey m) key = get m key := by
  have hperm := sortByKey_perm m
  unfold get
  cases hs : (sortByKey m).find? (fun entry => entry.1 == key) with
  | none =>
    cases hm : m.find? (fun entry => entry.1 == key) with
    | none => rfl
    | some e =>
      exfalso
      have hmem : e ∈ m := List.mem_of_find?_eq_some hm
      have hp := List.find?_some hm
      rw [List.find?_eq_none] at hs
      exact hs e (hperm.mem_iff.mpr hmem) hp
  | some e =>
    cases hm : m.find? (fun entry => entry.1 == key) with
    | none =>
      exfalso
      have hmem : e ∈ sortByKey m := List.mem_of_find?_eq_some hs
      have hp := List.find?_some hs
      rw [List.find?_eq_none] at hm
      exact hm e (hperm.mem_iff.mp hmem) hp
    | some e' =>
      have he : e ∈ m := hperm.mem_iff.mp (List.mem_of_find?_eq_some hs)
      have he' : e' ∈ m := List.mem_of_find?_eq_some hm
      have hk : e.1 = key := by simpa using List.find?_some hs
      have hk' : e'.1 = key := by simpa using List.find?_some hm
      rw [eq_of_key_eq_of_nodupKeys h he he' (hk.trans hk'.symm)]

/-! ## How an operation changes the entry count

The wire format carries the count in a `u32` header, so every lemma about the
encoding needs a bound below `2 ^ 32`.  These three say how far an operation
can move that count, which is what lets a caller carry the bound it already
has across an operation instead of a new proof. -/

/-- An insert adds at most one entry.  A fresh key is appended once, and a key
already present is replaced in place.

Consumers: `length_ofEntries_le` below, and
`Project.RustHashMap.Spec.mapOf_insert_output`. -/
theorem length_insert_le [BEq K] (m : Map K V) (key : K) (value : V) :
    (insert m key value).2.length ≤ m.length + 1 := by
  unfold insert
  split <;> simp

/-- A remove never adds an entry.  It filters, so the result is a sublist.

Consumer: `Project.RustHashMap.Spec.mapOf_remove_output`. -/
theorem length_remove_le [BEq K] (m : Map K V) (key : K) :
    (remove m key).2.length ≤ m.length := by
  unfold remove
  exact List.length_filter_le _ _

/-- `ofEntries` inserts each pair in turn, so it never yields more entries than
it read.  A repeated key makes it yield fewer.

Consumer: `Project.RustHashMap.Spec.length_of_mapOf`. -/
theorem length_ofEntries_le [BEq K] (entries : List (K × V)) :
    (ofEntries entries).length ≤ entries.length := by
  have haux : ∀ (es : List (K × V)) (acc : Map K V),
      (es.foldl (fun m entry => (insert m entry.1 entry.2).2) acc).length
        ≤ acc.length + es.length := by
    intro es
    induction es with
    | nil => intro acc; simp
    | cons entry rest ih =>
        intro acc
        have h1 := ih (insert acc entry.1 entry.2).2
        have h2 := length_insert_le acc entry.1 entry.2
        simp only [List.foldl_cons, List.length_cons]
        omega
  simpa [ofEntries] using haux entries []

end Wasm.RustStd.HashMap
