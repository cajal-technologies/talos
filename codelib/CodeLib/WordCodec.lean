/-!
# Fixed-width word codecs for packed byte streams

`WordCodec W` packages the three things a byte-stream example needs in order to
move a `List W` across the `StdIO` host ABI: a fixed `width` in bytes, an
`encode` that lays one word down as exactly `width` bytes, and a `decode` that
reads one word back out of a `width`-byte chunk.

The list-level plumbing — `serialize`, `deserialize`, and the round trip
between them — is defined and proved once here, for every width at once. Only
the word-level round trip is supplied per codec, as the `decode_encode` field:
it is a statement about a concrete bit width, so it is discharged by
kernel-checked bitwise lemmas at the instantiation site and cannot be proved generically.

`decode` is total. `deserialize` returns `Option` for exactly one reason: a
trailing run of fewer than `width` bytes is rejected rather than silently
dropped, so a successful decode has consumed every byte it was given.
`deserialize_serialize_append_eq_none` is that property stated as a theorem.

Consumers: `CodeLib.Examples.MergeSort.StdIO` instantiates it at four-byte
`UInt32` words, `CodeLib.Examples.SelectionSort.StdIO` at eight-byte `UInt64`
words. Before this module the two examples each carried their own copy of the
definitions and both proofs below.
-/

namespace Wasm

/-- A packed byte encoding of `W` in fixed-size words.

`encode` and `decode` are inverse at the word level (`decode_encode`), and
`encode` always produces exactly `width` bytes (`encode_length`). Those two
facts are everything `serialize`/`deserialize` need. -/
structure WordCodec (W : Type) where
  /-- Number of bytes one word occupies in the stream. -/
  width : Nat
  /-- Lay one word down as exactly `width` bytes. -/
  encode : W → List UInt8
  /-- Read one word back out of a `width`-byte chunk. Total: `deserialize`
  only ever applies it to chunks of exactly `width` bytes, so a codec is free
  to return anything on other inputs. -/
  decode : List UInt8 → W
  /-- A zero-width word would leave `deserialize` with nothing to consume. -/
  width_pos : 0 < width
  encode_length : ∀ value, (encode value).length = width
  decode_encode : ∀ value, decode (encode value) = value

namespace WordCodec

variable {W : Type} (codec : WordCodec W)

/-- Packed serialization of a list of words: each word in turn, no framing. -/
def serialize (values : List W) : List UInt8 :=
  values.flatMap codec.encode

@[simp] theorem serialize_nil : codec.serialize [] = [] := rfl

@[simp] theorem serialize_cons (value : W) (values : List W) :
    codec.serialize (value :: values) =
      codec.encode value ++ codec.serialize values := rfl

@[simp] theorem serialize_length (values : List W) :
    (codec.serialize values).length = codec.width * values.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      rw [serialize_cons, List.length_append, codec.encode_length, ih,
        List.length_cons, Nat.mul_succ]
      omega

theorem serializeLength_toNat (values : List W) {limit : Nat}
    (hfit : (codec.serialize values).length ≤ limit)
    (hlimit : limit < UInt32.size) :
    (UInt32.ofNat (codec.serialize values).length).toNat =
      (codec.serialize values).length :=
  UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hfit hlimit)

/-- Decode a packed byte stream. A trailing run of fewer than `width` bytes is
rejected rather than silently ignored, so `some` means every byte was
consumed. -/
def deserialize (codec : WordCodec W) : List UInt8 → Option (List W)
  | [] => some []
  | first :: rest =>
      if (first :: rest).length < codec.width then none
      else
        (deserialize codec ((first :: rest).drop codec.width)).map
          (codec.decode ((first :: rest).take codec.width) :: ·)
termination_by bytes => bytes.length
decreasing_by
  have hpos := codec.width_pos
  simp only [List.length_drop, List.length_cons]; omega

@[simp] theorem deserialize_nil : codec.deserialize [] = some [] := by simp [deserialize]

/-- Fewer than `width` bytes left, and not none left, is a partial word. -/
theorem deserialize_eq_none_of_length_lt (bytes : List UInt8)
    (hne : bytes ≠ []) (hshort : bytes.length < codec.width) :
    codec.deserialize bytes = none := by
  match bytes with
  | [] => exact absurd rfl hne
  | first :: rest =>
      rw [deserialize]; exact if_pos hshort

/-- Peel one whole word off the front of a stream. This is the equation the
concrete codecs re-export at a literal width, so that proofs written against
the hand-rolled `deserialize` keep working unchanged. -/
theorem deserialize_append (chunk rest : List UInt8)
    (hchunk : chunk.length = codec.width) :
    codec.deserialize (chunk ++ rest) =
      (codec.deserialize rest).map (codec.decode chunk :: ·) := by
  match chunk, hchunk with
  | [], hchunk =>
      exact absurd hchunk.symm (Nat.ne_of_gt codec.width_pos)
  | first :: cs, hchunk =>
      have hlength : ((first :: cs) ++ rest).length = codec.width + rest.length := by
        rw [List.length_append, hchunk]
      show codec.deserialize (first :: (cs ++ rest)) = _
      rw [deserialize]
      rw [if_neg (by
        show ¬ ((first :: (cs ++ rest)).length < codec.width)
        rw [show (first :: (cs ++ rest)) = ((first :: cs) ++ rest) from rfl,
          hlength]
        omega)]
      rw [show (first :: (cs ++ rest)) = ((first :: cs) ++ rest) from rfl,
        ← hchunk, List.take_left, List.drop_left]

@[simp] theorem deserialize_serialize (values : List W) :
    codec.deserialize (codec.serialize values) = some values := by
  induction values with
  | nil => simp
  | cons value values ih =>
      rw [serialize_cons,
        codec.deserialize_append _ _ (codec.encode_length value), ih,
        codec.decode_encode]
      rfl

/-- A trailing partial word is rejected, not dropped: appending fewer than
`width` extra bytes to a well-formed stream makes the whole stream fail to
decode. This is the only way `deserialize` produces `none`. -/
theorem deserialize_serialize_append_eq_none (values : List W)
    (trailing : List UInt8) (hne : trailing ≠ [])
    (hshort : trailing.length < codec.width) :
    codec.deserialize (codec.serialize values ++ trailing) = none := by
  induction values with
  | nil =>
      rw [serialize_nil, List.nil_append]
      exact codec.deserialize_eq_none_of_length_lt trailing hne hshort
  | cons value values ih =>
      rw [serialize_cons, List.append_assoc,
        codec.deserialize_append _ _ (codec.encode_length value), ih]
      rfl

end WordCodec

end Wasm
