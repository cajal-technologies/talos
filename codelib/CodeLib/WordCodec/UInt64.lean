import CodeLib.WordCodec
import CodeLib.ByteReassembly

/-!
# `CodeLib.WordCodec.UInt64`

The eight-byte little-endian `u64` codec, as a `WordCodec UInt64`.

Byte `i` of `encodeU64 v` is `(v >>> 8i).toUInt8`, the same projection
`SepLogic.u64Byte` uses, so an encoded word and its `pointsTo_u64` footprint
agree by `rfl`. The proof of `decode_encode` closes with
`Nat.reassemble64_of_lt` from `CodeLib.ByteReassembly`, which uses
`Nat.testBit` and `omega` rather than bit-blasting, so no theorem stated over
this codec depends on a reflection axiom.

Consumers: `Project.GcdStdio.Spec` (its input and output streams) and
`CodeLib.Examples.SelectionSort.StdIO`.
-/

namespace Wasm.WordCodec

/-- The eight little-endian bytes of a 64-bit word. -/
def encodeU64 (value : UInt64) : List UInt8 :=
  [ value.toUInt8
  , (value >>> 8).toUInt8
  , (value >>> 16).toUInt8
  , (value >>> 24).toUInt8
  , (value >>> 32).toUInt8
  , (value >>> 40).toUInt8
  , (value >>> 48).toUInt8
  , (value >>> 56).toUInt8 ]

/-- Read one eight-byte little-endian word.  Total, as `WordCodec.decode`
requires; `deserialize` only ever applies it to chunks of width eight. -/
def decodeU64 : List UInt8 → UInt64
  | b₀ :: b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: _ =>
      b₀.toUInt64 ||| (b₁.toUInt64 <<< 8) |||
        (b₂.toUInt64 <<< 16) ||| (b₃.toUInt64 <<< 24) |||
        (b₄.toUInt64 <<< 32) ||| (b₅.toUInt64 <<< 40) |||
        (b₆.toUInt64 <<< 48) ||| (b₇.toUInt64 <<< 56)
  | _ => 0

/-- Eight-byte little-endian `u64` words. -/
def u64le : WordCodec UInt64 where
  width := 8
  encode := encodeU64
  decode := decodeU64
  width_pos := by decide
  encode_length := fun _ => rfl
  decode_encode := by
    intro value
    simp only [encodeU64, decodeU64]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft,
      UInt8.toNat_toUInt64, UInt64.toNat_toUInt8,
      UInt64.toNat_shiftRight]
    exact Nat.reassemble64_of_lt value.toNat (UInt64.toNat_lt value)

@[simp] theorem u64le_encode_length (value : UInt64) :
    (u64le.encode value).length = 8 := rfl

end Wasm.WordCodec
