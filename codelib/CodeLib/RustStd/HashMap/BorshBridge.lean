import CodeLib.RustStd.HashMap.Codec

/-!
# From decoder bytes to the entry list

The compiled borsh decoder of `Vec<(u32, u32)>` works on bytes.  Its contract
names a four-byte header and `8 n` payload bytes.  The model works on an
entry list, through `HashMap.deserializeEntries` and `Borsh.hashMap?`.  This
file joins the two.

The driver reads its whole input through the decoder and rejects any input
with unread bytes left over.  So the driver accepts exactly when the byte
list holds a header, holds every pair the header announces, and holds nothing
more.  `deserializeEntries_eq_some_of_accepts` gives the entry list on that
input.  `length_and_count_of_deserializeEntries` is the converse: an input
that the model accepts has exactly that shape.  The two rejection lemmas are
corollaries of the converse, one for a short input and one for an input with
trailing bytes.

The predicates here repeat `Project.RustHashMap.BodyContracts.headerWord` and
`DecodeAccepts` by definition, because `CodeLib` must not depend on the
`programs` package.  Both unfold to the same proposition, so a driver proof
can move between them with `rfl`.

Two lemmas about `WordCodec` come first, because neither is about borsh:

* `length_of_deserialize_eq_some`: an accepted stream holds one whole word
  per value.
* `deserialize_eq_some_map_range`: a stream whose length is a multiple of the
  word width decodes to one word per chunk, in order.
-/

namespace Wasm.WordCodec

variable {W : Type}

/-- A stream that `deserialize` accepts holds one whole word for each value it
returns.  `deserialize` rejects a trailing partial word, so the length is an
exact multiple of the width.

Consumer: `RustStd.HashMap.BorshBridge.length_and_count_of_deserializeEntries`. -/
theorem length_of_deserialize_eq_some (codec : WordCodec W) :
    ∀ (values : List W) (bytes : List UInt8),
      codec.deserialize bytes = some values →
        bytes.length = codec.width * values.length := by
  intro values
  induction values with
  | nil =>
      intro bytes h
      cases bytes with
      | nil => simp
      | cons first rest =>
          rw [deserialize] at h
          split at h
          · simp at h
          · obtain ⟨_, _, htail⟩ := Option.map_eq_some_iff.mp h
            exact absurd htail (List.cons_ne_nil _ _)
  | cons value values ih =>
      intro bytes h
      cases bytes with
      | nil => simp at h
      | cons first rest =>
          rw [deserialize] at h
          split at h
          · simp at h
          · rename_i hlong
            obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp h
            obtain ⟨_, htailEq⟩ := List.cons.inj hcons
            subst htailEq
            have hlen := ih _ htail
            rw [List.length_drop] at hlen
            simp only [List.length_cons] at hlong hlen ⊢
            rw [Nat.mul_succ]
            omega

/-- A stream whose length is `count` whole words decodes to those `count`
words, each read off its own chunk.  The chunk of word `i` starts at
`width * i`.

Consumer: `RustStd.HashMap.BorshBridge.deserializeEntries_eq_some_of_accepts`. -/
theorem deserialize_eq_some_map_range (codec : WordCodec W) :
    ∀ (count : Nat) (bytes : List UInt8),
      bytes.length = codec.width * count →
        codec.deserialize bytes =
          some ((List.range count).map fun i =>
            codec.decode ((bytes.drop (codec.width * i)).take codec.width)) := by
  intro count
  induction count with
  | zero =>
      intro bytes hlen
      rw [Nat.mul_zero] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen]
      simp
  | succ count ih =>
      intro bytes hlen
      have hge : codec.width ≤ bytes.length := by
        rw [hlen, Nat.mul_succ]; omega
      have hchunk : (bytes.take codec.width).length = codec.width := by
        rw [List.length_take]; omega
      have hrest : (bytes.drop codec.width).length = codec.width * count := by
        rw [List.length_drop, hlen, Nat.mul_succ]; omega
      conv_lhs => rw [← List.take_append_drop codec.width bytes]
      rw [codec.deserialize_append _ _ hchunk, ih _ hrest]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Option.map_some, Function.comp_def, List.drop_zero,
        Nat.mul_zero, List.drop_drop, Nat.mul_succ]
      congr 2
      apply List.map_congr_left
      intro i _
      rw [Nat.add_comm]

end Wasm.WordCodec

namespace Wasm.RustStd.HashMap.BorshBridge

open Wasm Wasm.RustStd

/-- The entry count that the first four bytes of the input announce.  This is
`Project.RustHashMap.BodyContracts.headerWord` read as a natural number. -/
def headerCount (bytes : List UInt8) : Nat :=
  (WordCodec.decodeU32 (bytes.take 4)).toNat

/-- The compiled decoder accepts exactly when the input holds a four-byte
header and every pair that the header announces.  It does not reject trailing
bytes.  This repeats `Project.RustHashMap.BodyContracts.DecodeAccepts` by
definition. -/
def DecodeAccepts (bytes : List UInt8) : Prop :=
  4 ≤ bytes.length ∧ 4 + 8 * headerCount bytes ≤ bytes.length

/-- The entries that the payload holds, in wire order.  Entry `i` takes its
key from the four bytes at `4 + 8 i` and its value from the four bytes at
`8 + 8 i`.  This is the order in which the compiled loop stores the pairs
into its output buffer. -/
def wireEntries (bytes : List UInt8) : HashMap.Map UInt32 UInt32 :=
  (List.range (headerCount bytes)).map fun i =>
    (WordCodec.decodeU32 ((bytes.drop (4 + 8 * i)).take 4),
      WordCodec.decodeU32 ((bytes.drop (8 + 8 * i)).take 4))

/-- The entry count of the model list is the header word.  This is the length
relation that the accepting lemma needs. -/
@[simp] theorem length_wireEntries (bytes : List UInt8) :
    (wireEntries bytes).length = headerCount bytes := by
  simp [wireEntries]

/-- The pair codec of two `u32` words is eight bytes wide. -/
theorem pairCodec_u32le_width :
    (HashMap.pairCodec WordCodec.u32le WordCodec.u32le).width = 8 := rfl

/-- The pair codec reads the key from the first four bytes of its chunk and
the value from the rest. -/
theorem pairCodec_u32le_decode (chunk : List UInt8) :
    (HashMap.pairCodec WordCodec.u32le WordCodec.u32le).decode chunk =
      (WordCodec.decodeU32 (chunk.take 4),
        WordCodec.decodeU32 (chunk.drop 4)) := rfl

/-! ## The accepting direction -/

/-- The model accepts every input that the driver accepts, and returns the
payload pairs in wire order.

The driver accepts when the decoder accepts and no byte is left unread, which
is the second hypothesis.  The first hypothesis is the decoder contract
itself. -/
theorem deserializeEntries_eq_some_of_accepts (bytes : List UInt8)
    (_haccept : DecodeAccepts bytes)
    (hexact : bytes.length = 4 + 8 * headerCount bytes) :
    HashMap.deserializeEntries WordCodec.u32le WordCodec.u32le bytes
      = some (wireEntries bytes) := by
  have hrest : (bytes.drop 4).length
      = (HashMap.pairCodec WordCodec.u32le WordCodec.u32le).width
        * headerCount bytes := by
    rw [List.length_drop, hexact, pairCodec_u32le_width]
    omega
  rw [HashMap.deserializeEntries, Vec.deserialize, if_neg (by omega),
    WordCodec.deserialize_eq_some_map_range _ _ _ hrest]
  have hcount : ((List.range (headerCount bytes)).map fun i =>
      (HashMap.pairCodec WordCodec.u32le WordCodec.u32le).decode
        (((bytes.drop 4).drop
          ((HashMap.pairCodec WordCodec.u32le WordCodec.u32le).width * i)).take
          (HashMap.pairCodec WordCodec.u32le WordCodec.u32le).width)).length
      = (WordCodec.decodeU32 (bytes.take 4)).toNat := by
    simp [headerCount]
  dsimp only
  rw [if_pos hcount]
  congr 1
  rw [wireEntries]
  apply List.map_congr_left
  intro i _
  rw [pairCodec_u32le_decode, pairCodec_u32le_width, List.drop_drop,
    List.take_take, List.drop_take, List.drop_drop]
  rw [show min 4 8 = 4 by decide, show (8 - 4 : Nat) = 4 by decide,
    show 4 + 8 * i + 4 = 8 + 8 * i by omega]

/-! ## The rejecting direction -/

/-- An input that the model accepts has the shape the driver accepts: the
pair count is the header word, and the input holds nothing after the last
pair.

This is the converse of `deserializeEntries_eq_some_of_accepts`, and it is
what both rejection lemmas below use. -/
theorem length_and_count_of_deserializeEntries {bytes : List UInt8}
    {entries : HashMap.Map UInt32 UInt32}
    (h : HashMap.deserializeEntries WordCodec.u32le WordCodec.u32le bytes
      = some entries) :
    entries.length = headerCount bytes ∧
      bytes.length = 4 + 8 * headerCount bytes := by
  rw [HashMap.deserializeEntries, Vec.deserialize] at h
  split at h
  · simp at h
  · rename_i hlong
    cases hdes : (HashMap.pairCodec WordCodec.u32le WordCodec.u32le).deserialize
        (bytes.drop 4) with
    | none => rw [hdes] at h; simp at h
    | some values =>
        rw [hdes] at h
        dsimp only at h
        split_ifs at h with hcount
        · have hvalues : values = entries := by simpa using h
          subst hvalues
          have hlen := WordCodec.length_of_deserialize_eq_some _ _ _ hdes
          rw [List.length_drop, pairCodec_u32le_width] at hlen
          exact ⟨hcount, by rw [headerCount, ← hcount]; omega⟩

/-- A short input, or an input whose payload stops before the header says,
decodes to no map.  The driver rejects it, and so does the model. -/
theorem hashMap?_eq_none_of_not_accepts (bytes : List UInt8)
    (hreject : ¬ DecodeAccepts bytes) :
    Borsh.hashMap? WordCodec.u32le WordCodec.u32le bytes = none := by
  rw [Borsh.hashMap?]
  cases hdes : HashMap.deserializeEntries WordCodec.u32le WordCodec.u32le bytes
    with
  | none => rfl
  | some entries =>
      exact absurd
        (by
          obtain ⟨_, hlen⟩ := length_and_count_of_deserializeEntries hdes
          exact ⟨by omega, by omega⟩)
        hreject

/-- An input with trailing bytes decodes to no map.  The decoder itself
accepts it and reports the unread bytes through the slice header.  The driver
rejects it, and so does the model. -/
theorem hashMap?_eq_none_of_trailing (bytes : List UInt8)
    (_haccept : DecodeAccepts bytes)
    (htrailing : bytes.length ≠ 4 + 8 * headerCount bytes) :
    Borsh.hashMap? WordCodec.u32le WordCodec.u32le bytes = none := by
  rw [Borsh.hashMap?]
  cases hdes : HashMap.deserializeEntries WordCodec.u32le WordCodec.u32le bytes
    with
  | none => rfl
  | some entries =>
      exact absurd (length_and_count_of_deserializeEntries hdes).2 htrailing

/-- The map the model builds from an input the driver accepts.  `ofEntries`
collects the wire pairs, so a repeated key keeps its last value. -/
theorem hashMap?_eq_some_of_accepts (bytes : List UInt8)
    (haccept : DecodeAccepts bytes)
    (hexact : bytes.length = 4 + 8 * headerCount bytes) :
    Borsh.hashMap? WordCodec.u32le WordCodec.u32le bytes
      = some (HashMap.ofEntries (wireEntries bytes)) := by
  rw [Borsh.hashMap?,
    deserializeEntries_eq_some_of_accepts bytes haccept hexact]
  rfl

end Wasm.RustStd.HashMap.BorshBridge
