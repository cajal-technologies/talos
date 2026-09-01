import CodeLib.RustStd.Vec.Basic
import CodeLib.WordCodec
import Mathlib.Data.Nat.Bitwise

/-!
# A length-prefixed wire format for `Vec`

`WordCodec` packs a `List W` with no framing, so a decoder has to be told how
many words to expect by something outside the stream.  This module adds the
one piece that makes a `Vec` self-describing on the wire: a four-byte
little-endian count in front of the packed words.

The header word is byte-identical to the length word of the wasm32 `Vec`
header, which is what makes this format cheap for a driver to produce: the
count it writes is the word it already holds.

The count is a `u32`, so `serialize` is faithful only below `2 ^ 32` elements.
That bound is a hypothesis on the round-trip and injectivity theorems rather
than something hidden inside a definition, because above it the header
genuinely loses information.

`u32le` below duplicates a four-byte little-endian codec that the merge-sort
specification also defines, one package downstream.  codelib cannot import
`programs`, so the definition is mirrored here under distinct names; the
downstream one can be derived from this one once both are in the same build.
-/

namespace Wasm.RustStd.Vec

open Wasm

variable {W : Type}

/-! ## The four-byte little-endian `u32` codec -/

/-- The four little-endian bytes of a 32-bit word. -/
def encodeU32 (value : UInt32) : List UInt8 :=
  [ value.toUInt8
  , (value >>> 8).toUInt8
  , (value >>> 16).toUInt8
  , (value >>> 24).toUInt8 ]

/-- Read one four-byte little-endian word.  Total, as `WordCodec.decode`
requires; `deserialize` only ever applies it to chunks of width four. -/
def decodeU32 : List UInt8 → UInt32
  | b₀ :: b₁ :: b₂ :: b₃ :: _ =>
      b₀.toUInt32 ||| (b₁.toUInt32 <<< 8) |||
        (b₂.toUInt32 <<< 16) ||| (b₃.toUInt32 <<< 24)
  | _ => 0

/-- Kernel-checked reconstruction of a 32-bit natural from its four bytes.
Proved through `Nat.testBit` and `omega` rather than by bit-blasting, so that
no theorem about this wire format depends on a reflection axiom. -/
private theorem reassembleLE32 (n : Nat) (h : n < 2 ^ 32) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 32 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 32 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 32 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hi8 : i < 8
  · simp [hi8, show i < 32 by omega, show ¬i ≥ 8 by omega,
      show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi16 : i < 16
  · have h8le : i ≥ 8 := by omega
    have heq : 8 + (i - 8) = i := by omega
    simp [hi8, h8le, heq, show i < 32 by omega,
      show i - 8 < 8 by omega, show ¬i ≥ 16 by omega,
      show ¬i ≥ 24 by omega]
  by_cases hi24 : i < 24
  · have h16le : i ≥ 16 := by omega
    have heq : 16 + (i - 16) = i := by omega
    simp [hi8, h16le, heq, show i < 32 by omega,
      show ¬i - 8 < 8 by omega, show i - 16 < 8 by omega,
      show ¬i ≥ 24 by omega]
  by_cases hi32 : i < 32
  · have h24le : i ≥ 24 := by omega
    have heq : 24 + (i - 24) = i := by omega
    simp [hi8, hi32, h24le, heq, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show i - 24 < 8 by omega]
  · have hibound : n.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le h
        (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hi8, hibound, show ¬i < 32 by omega,
      show ¬i - 8 < 8 by omega, show ¬i - 16 < 8 by omega,
      show ¬i - 24 < 8 by omega]

/-- Four-byte little-endian `u32` words. -/
def u32le : WordCodec UInt32 where
  width := 4
  encode := encodeU32
  decode := decodeU32
  width_pos := by decide
  encode_length := fun _ => rfl
  decode_encode := by
    intro value
    simp only [encodeU32, decodeU32]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
      UInt32.toNat_shiftRight]
    exact reassembleLE32 value.toNat (UInt32.toNat_lt value)

@[simp] theorem u32le_width : u32le.width = 4 := rfl

@[simp] theorem u32le_encode_length (value : UInt32) :
    (u32le.encode value).length = 4 := rfl

/-! ## The length-prefixed format -/

/-- Serialize a vector as a four-byte little-endian element count followed by
the packed elements. -/
def serialize (codec : WordCodec W) (values : List W) : List UInt8 :=
  u32le.encode (UInt32.ofNat values.length) ++ codec.serialize values

/-- Deserialize the length-prefixed format.  Every failure mode is `none`: a
header shorter than four bytes, a payload with a trailing partial word, or a
payload whose word count disagrees with the header. -/
def deserialize (codec : WordCodec W) (bytes : List UInt8) : Option (List W) :=
  if bytes.length < 4 then none
  else
    match codec.deserialize (bytes.drop 4) with
    | none => none
    | some values =>
        if values.length = (decodeU32 (bytes.take 4)).toNat then some values
        else none

@[simp] theorem serialize_length (codec : WordCodec W) (values : List W) :
    (serialize codec values).length = 4 + codec.width * values.length := by
  simp [serialize]

/-- The header is exactly the first four bytes and the payload is the rest. -/
private theorem serialize_split (codec : WordCodec W) (values : List W) :
    (serialize codec values).take 4 = u32le.encode (UInt32.ofNat values.length)
      ∧ (serialize codec values).drop 4 = codec.serialize values := by
  have hlen : (u32le.encode (UInt32.ofNat values.length)).length = 4 := rfl
  constructor
  · rw [serialize, ← hlen, List.take_left]
  · rw [serialize, ← hlen, List.drop_left]

/-- Round trip, for any vector the four-byte header can describe. -/
theorem deserialize_serialize (codec : WordCodec W) (values : List W)
    (hbound : values.length < 2 ^ 32) :
    deserialize codec (serialize codec values) = some values := by
  obtain ⟨htake, hdrop⟩ := serialize_split codec values
  have hcount : values.length
      = (decodeU32 ((serialize codec values).take 4)).toNat := by
    rw [htake]
    show values.length
      = (u32le.decode (u32le.encode (UInt32.ofNat values.length))).toNat
    rw [u32le.decode_encode]
    exact (UInt32.toNat_ofNat_of_lt hbound).symm
  rw [deserialize, if_neg (by simp), hdrop, codec.deserialize_serialize]
  exact if_pos hcount

/-- Distinct vectors have distinct wire images, below the header's bound. -/
theorem serialize_inj (codec : WordCodec W) {values values' : List W}
    (hbound : values.length < 2 ^ 32) (hbound' : values'.length < 2 ^ 32)
    (heq : serialize codec values = serialize codec values') :
    values = values' := by
  have h := deserialize_serialize codec values hbound
  rw [heq, deserialize_serialize codec values' hbound'] at h
  exact (Option.some_inj.mp h).symm

end Wasm.RustStd.Vec
