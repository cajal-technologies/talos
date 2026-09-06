import CodeLib.WordCodec.UInt32

/-!
# SipHash-1-3, as `std::hash::RandomState` computes it

`HashMap<K, V>` with the default `RandomState` hashes each key with
SipHash-1-3.  This file is a pure model of that function, written from
`library/core/src/hash/sip.rs` of Rust 1.95.0, the toolchain that built the
`rust_hash_map` module.  The model is the input to the hash-table model in
`CodeLib.RustStd.HashMap.Table`, which needs the exact hash of each key to
predict the exact control bytes of the table.

Three facts about the Rust side fix the shape of the model:

* The hasher keeps a 64-bit state `v0, v1, v2, v3` seeded from two 64-bit
  keys `k0, k1`.  `RandomState` reads the keys from a thread-local cell and
  bumps `k0` by one after each read.  On `wasm32-unknown-unknown` the cell
  starts from two run-time addresses, not from constants, so the keys are
  parameters here and no theorem in this file fixes them.
* One `write` of the whole message followed by `finish` is the standard
  SipHash over that message: full eight-byte blocks are absorbed in order, and
  the last block carries the remaining bytes with the message length in its
  top byte.  `sipHash13` states that directly and does not model the
  partial-block buffer of the incremental hasher.
* A `u32` key hashes as its four native-endian bytes: `Hash for u32` calls
  `write_u32`, and `DefaultHasher` forwards that to `write(&k.to_ne_bytes())`.
  On wasm32 native order is little-endian, which is
  `Wasm.WordCodec.encodeU32`.  `hashU32` is that path.

`vectors_ok` checks all 64 vectors of `test_siphash_1_3` in
`library/coretests/tests/hash/sip.rs` in the kernel.  Vector `n` is the hash
of the bytes `0, 1, ..., n - 1`, so the vectors cover every block boundary up
to seven full blocks.  Vector 4 is the hash of four bytes, which is the `u32`
path, and `hashU32_vector4` pins it by name.  No proof in this file uses
`native_decide`.
-/

namespace Wasm.RustStd.HashMap.SipHash

/-- Rotate a 64-bit word left by `b` bits, `0 < b < 64`.  `u64::rotate_left`. -/
def rotl (x : UInt64) (b : UInt64) : UInt64 :=
  (x <<< b) ||| (x >>> (64 - b))

/-- The four state words of the hasher. -/
structure State where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  deriving Repr, DecidableEq

/-- The seeded start state.  `Hasher::reset` in `sip.rs`. -/
def init (k0 k1 : UInt64) : State :=
  { v0 := k0 ^^^ 0x736f6d6570736575
    v1 := k1 ^^^ 0x646f72616e646f6d
    v2 := k0 ^^^ 0x6c7967656e657261
    v3 := k1 ^^^ 0x7465646279746573 }

/-- One SipRound.  The `compress!` macro in `sip.rs`. -/
def round (s : State) : State :=
  let v0 := s.v0 + s.v1
  let v2 := s.v2 + s.v3
  let v1 := rotl s.v1 13 ^^^ v0
  let v3 := rotl s.v3 16 ^^^ v2
  let v0 := rotl v0 32
  let v2 := v2 + v1
  let v0 := v0 + v3
  let v1 := rotl v1 17 ^^^ v2
  let v3 := rotl v3 21 ^^^ v0
  let v2 := rotl v2 32
  { v0, v1, v2, v3 }

/-- Absorb one message block: xor it into `v3`, one compression round
(`c_rounds` of `Sip13Rounds`), then xor it into `v0`. -/
def compress (m : UInt64) (s : State) : State :=
  let s := round { s with v3 := s.v3 ^^^ m }
  { s with v0 := s.v0 ^^^ m }

/-- The finalization: xor `0xff` into `v2`, three rounds (`d_rounds`), and
xor the four words together.  The last part of `Hasher::finish`. -/
def finalize (s : State) : UInt64 :=
  let s := { s with v2 := s.v2 ^^^ 0xff }
  let s := round (round (round s))
  s.v0 ^^^ s.v1 ^^^ s.v2 ^^^ s.v3

/-- Up to eight bytes as one little-endian word; the first byte is the least
significant.  Missing bytes are zero.  `u8to64_le` and `load_int_le!`. -/
def u64OfBytesLE (bs : List UInt8) : UInt64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

/-- Absorb every full eight-byte block of the message and return the state
with the bytes that remain, fewer than eight.  The block loop of
`Hasher::write`. -/
def absorb (s : State) : List UInt8 → State × List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      absorb (compress (u64OfBytesLE [b0, b1, b2, b3, b4, b5, b6, b7]) s) rest
  | tail => (s, tail)

/-- SipHash-1-3 of a byte string under the keys `k0, k1`.  The final block is
the tail bytes with the message length, modulo 256, in the top byte. -/
def sipHash13 (k0 k1 : UInt64) (msg : List UInt8) : UInt64 :=
  let (s, tail) := absorb (init k0 k1) msg
  let b : UInt64 := (UInt64.ofNat (msg.length % 256) <<< 56) ||| u64OfBytesLE tail
  finalize (compress b s)

/-- The hash of a `u32` key: SipHash-1-3 of its four little-endian bytes. -/
def hashU32 (k0 k1 : UInt64) (k : UInt32) : UInt64 :=
  sipHash13 k0 k1 (WordCodec.encodeU32 k)

/-! ## Test vectors

`test_siphash_1_3` uses the keys below and hashes the byte string
`0, 1, ..., n - 1` for each `n < 64`.  The Rust test stores each expected
value as eight little-endian bytes; `testVectors` holds the same values as
64-bit literals. -/

/-- `k0` of the test. -/
def testK0 : UInt64 := 0x0706050403020100

/-- `k1` of the test. -/
def testK1 : UInt64 := 0x0f0e0d0c0b0a0908

/-- The message of vector `n`: the bytes `0, 1, ..., n - 1`. -/
def testMessage (n : Nat) : List UInt8 :=
  (List.range n).map UInt8.ofNat

/-- The 64 expected values, in vector order. -/
def testVectors : List UInt64 :=
[
  0xabac0158050fc4dc, 0xc9f49bf37d57ca93, 0x82cb9b024dc7d44d, 0x8bf80ab8e7ddf7fb,
  0xcf75576088d38328, 0xdef9d52f49533b67, 0xc50d2b50c59f22a7, 0xd3927d989bb11140,
  0x369095118d299a8e, 0x25a48eb36c063de4, 0x79de85ee92ff097f, 0x70c118c1f94dc352,
  0x78a384b157b4d9a2, 0x306f760c1229ffa7, 0x605aa111c0f95d34, 0xd320d86d2a519956,
  0xcc4fdd1a7d908b66, 0x9cf2689063dbd80c, 0x8ffc389cb473e63e, 0xf21f9de58d297d1c,
  0xc0dc2f46a6cce040, 0xb992abfe2b45f844, 0x7ffe7b9ba320872e, 0x525a0e7fdae6c123,
  0xf464aeb267349c8c, 0x45cd5928705b0979, 0x3a3e35e3ca9913a5, 0xa91dc74e4ade3b35,
  0xfb0bed02ef6cd00d, 0x88d93cb44ab1e1f4, 0x540f11d643c5e663, 0x2370dd1f8c21d1bc,
  0x81157b6c16a7b60d, 0x4d54b9e57a8ff9bf, 0x759f12781f2a753e, 0xcea1a3bebf186b91,
  0x2cf508d3ada26206, 0xb6101c2da3c33057, 0xb3f47496ae3a36a1, 0x626b57547b108392,
  0xc1d2363299e41531, 0x667cc1923f1ad944, 0x65704ffec8138825, 0x24f280d1c28949a6,
  0xc2ca1cedfaf8876b, 0xc2164bfc9f042196, 0xa16e9c9368b1d623, 0x49fb169c8b5114fd,
  0x9f3143f8df074c46, 0xc6fdaf2412cc86b3, 0x7eaf49d10a52098f, 0x1cf313559d292f9a,
  0xc44a30dda2f41f12, 0x36fae98943a71ed0, 0x318fb34c73f0bce6, 0xa27abf3670a7e980,
  0xb4bcc0db243c6d75, 0x23f8d852fdb71513, 0x8f035f4da67d8a08, 0xd89cd0e5b7e8f148,
  0xf6f4e6bcf7a644ee, 0xaec59ad80f1837f2, 0xc3b2f6154b6694e0, 0x9d199062b7bbb3a8
]

theorem testVectors_length : testVectors.length = 64 := by decide +kernel

/-- Every vector of `test_siphash_1_3` agrees with `sipHash13`. -/
theorem vectors_ok :
    (List.range 64).all
      (fun n => sipHash13 testK0 testK1 (testMessage n) == testVectors[n]!) = true := by
  decide +kernel

/-- Vector 4 is the four-byte message `00 01 02 03`, which is the `u32`
key `0x03020100`. -/
theorem hashU32_vector4 :
    hashU32 testK0 testK1 0x03020100 = 0xcf75576088d38328 := by
  decide +kernel

end Wasm.RustStd.HashMap.SipHash
