import CodeLib.RustStd.Vec.Basic
import CodeLib.WordCodec.UInt32

/-!
# A length-prefixed wire format for `Vec`

`WordCodec` packs a `List W` with no framing, so a decoder has to be told how
many words to expect by something outside the stream.  This module adds the
one piece that makes a `Vec` self-describing on the wire: a four-byte
little-endian count in front of the packed words.  The count is the element
count a driver already holds, so the header costs one `len()` call.

The count is a `u32`, so `serialize` is faithful only below `2 ^ 32` elements.
That bound is a hypothesis on the round-trip theorem rather than something
hidden inside a definition, because above it the header genuinely loses
information.

Consumer: `Project.RustVec.Spec`, whose `vec_sum32` contract is stated with
`deserialize` and read back on well-formed input through
`deserialize_serialize`.
-/

namespace Wasm.RustStd.Vec

open Wasm

variable {W : Type}

/-- Serialize a vector as a four-byte little-endian element count followed by
the packed elements. -/
def serialize (codec : WordCodec W) (values : List W) : List UInt8 :=
  WordCodec.u32le.encode (UInt32.ofNat values.length) ++ codec.serialize values

/-- Deserialize the length-prefixed format.  Every failure mode is `none`: a
header shorter than four bytes, a payload with a trailing partial word, or a
payload whose word count disagrees with the header. -/
def deserialize (codec : WordCodec W) (bytes : List UInt8) : Option (List W) :=
  if bytes.length < 4 then none
  else
    match codec.deserialize (bytes.drop 4) with
    | none => none
    | some values =>
        if values.length = (WordCodec.decodeU32 (bytes.take 4)).toNat
        then some values
        else none

@[simp] theorem serialize_length (codec : WordCodec W) (values : List W) :
    (serialize codec values).length = 4 + codec.width * values.length := by
  simp [serialize]

/-- The header is exactly the first four bytes and the payload is the rest. -/
private theorem serialize_split (codec : WordCodec W) (values : List W) :
    (serialize codec values).take 4
        = WordCodec.u32le.encode (UInt32.ofNat values.length)
      ∧ (serialize codec values).drop 4 = codec.serialize values := by
  have hlen :
      (WordCodec.u32le.encode (UInt32.ofNat values.length)).length = 4 := rfl
  constructor
  · rw [serialize, ← hlen, List.take_left]
  · rw [serialize, ← hlen, List.drop_left]

/-- Round trip, for any vector the four-byte header can describe. -/
theorem deserialize_serialize (codec : WordCodec W) (values : List W)
    (hbound : values.length < 2 ^ 32) :
    deserialize codec (serialize codec values) = some values := by
  obtain ⟨htake, hdrop⟩ := serialize_split codec values
  have hcount : values.length
      = (WordCodec.decodeU32 ((serialize codec values).take 4)).toNat := by
    rw [htake]
    show values.length
      = (WordCodec.u32le.decode
          (WordCodec.u32le.encode (UInt32.ofNat values.length))).toNat
    rw [WordCodec.u32le.decode_encode]
    exact (UInt32.toNat_ofNat_of_lt hbound).symm
  rw [deserialize, if_neg (by simp), hdrop, codec.deserialize_serialize]
  exact if_pos hcount

end Wasm.RustStd.Vec
