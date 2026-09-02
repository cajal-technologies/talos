import CodeLib.RustStd.Vec.Codec

/-!
# The borsh wire format

[borsh](https://borsh.io/) is the serialization format the `rust_vec` exports
use on both sides of the byte stream.  Its specification is short, and the
part these programs need is five rules:

* an unsigned integer is its little-endian bytes, with no framing;
* a `bool` is one byte, `0` or `1`;
* `Option` is a tag byte, `0` for `None` and `1` followed by the payload for
  `Some`;
* a dynamic container is a `u32` little-endian length, then the elements;
* a tuple or struct is its fields in order, with nothing between them, so a
  tuple needs no definition here: write `++`.

Every one of those is already expressible with what `CodeLib` has, so this
module adds no new machinery.  It gives the layouts their borsh names, so a
contract can say "this export writes a borsh `Option<u32>`" instead of
restating the tag convention at each use.  The names are the borsh type names
and the namespace is meant to be used qualified: `Borsh.u32`, `Borsh.option`,
`Borsh.vec`.  `vec` is literally `Wasm.RustStd.Vec.serialize`: the
length-prefixed format that module already defines *is* the borsh container
encoding, which is why the round trip below is `Vec.deserialize_serialize`
under another name.

Five definitions and one inherited round-trip theorem.  Consumer:
`Project.RustVec.Spec`, which states one contract per `rust_vec` export in
these terms.
-/

namespace Wasm.RustStd.Borsh

open Wasm

variable {W : Type}

/-- A `u32`, as four little-endian bytes. -/
def u32 (value : UInt32) : List UInt8 :=
  WordCodec.u32le.encode value

/-- A `bool`, as the single byte `1` for `true` and `0` for `false`. -/
def bool (value : Bool) : List UInt8 :=
  [if value then 1 else 0]

/-- An `Option`, as the tag byte `0` alone, or the tag byte `1` followed by the
payload. -/
def option (encode : W → List UInt8) : Option W → List UInt8
  | none => [0]
  | some value => 1 :: encode value

/-- A `Vec`, as a `u32` little-endian element count followed by the packed
elements.  This is `Vec.serialize`, whose header is that same count. -/
def vec (codec : WordCodec W) (values : List W) : List UInt8 :=
  Vec.serialize codec values

/-- Read a `Vec` back.  Every failure mode is `none`, including a payload whose
element count disagrees with the header. -/
def vec? (codec : WordCodec W) (bytes : List UInt8) : Option (List W) :=
  Vec.deserialize codec bytes

/-- The `Vec` round trip, for any vector the `u32` header can describe.
Inherited from `Vec.deserialize_serialize`. -/
theorem vec?_vec (codec : WordCodec W) (values : List W)
    (hbound : values.length < 2 ^ 32) :
    vec? codec (vec codec values) = some values :=
  Vec.deserialize_serialize codec values hbound

end Wasm.RustStd.Borsh
