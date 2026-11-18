import CodeLib.WordCodec
import CodeLib.UInt32

/-!
# `CodeLib.WordCodec.UInt32`

The four-byte little-endian `u32` codec, as a `WordCodec UInt32`.

Byte `i` of `encodeU32 v` is `(v >>> 8i).toUInt8`, the same projection
`SepLogic.u32Byte` uses, so an encoded word and its `pointsTo_u32` footprint
agree by `rfl`. The proof of `decode_encode` closes with
`Nat.reassemble32_of_lt` from `CodeLib.UInt32`, which uses `Nat.testBit` and
`omega` rather than bit-blasting, so no theorem stated over this codec depends
on a reflection axiom.

Consumers: `CodeLib.RustStd.Vec.Codec`, which puts `u32le` in front of a packed
`Vec` as its element count; `Project.Mergesort.Spec` (its input and output
streams); and `CodeLib.Examples.MergeSort.StdIO`.
-/

namespace Wasm.WordCodec

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
    exact Nat.reassemble32_of_lt value.toNat (UInt32.toNat_lt value)

@[simp] theorem u32le_encode_length (value : UInt32) :
    (u32le.encode value).length = 4 := rfl

end Wasm.WordCodec
