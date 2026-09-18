import CodeLib.RustStd.HashMap.TableMem

/-!
# The hoisted first SipRound of the rehash loop

The rehash loop of func 17 hashes one key for each full bucket.  Every part
of the first `SipHash.round` that does not read the key is computed once,
above the loop, in WAT func 17 lines 3750 to 3782 of
`programs/rust/build/rust_hash_map/program.wat`.  The locals there are 16,
18, 19, 20, 21 and 26.

Two things make the hoisted form hard to read against `SipHash.round`.

First, the constant of local 21 is `0x7065646279746573`, not the SipHash
constant `0x7465646279746573` of `SipHash.init`.  The two differ by
`0x0400000000000000`, which is `2 ^ 58`.  The message of `hashU32` is four
bytes, so the last block of `sipHash13` carries the length 4 in its top
byte, and the compiler folded that constant into the start state.

Second, the message is shorter than one block, so `sipHash13` runs exactly
one `compress`.

`hashU32_eq_hoist` states `SipHash.hashU32` as one `finalize` over a state
built from the six hoisted values.  Every step is an equation between two
ways to write the same round, so a body proof can step the compiled code
and keep the model name.
-/

namespace Wasm.RustStd.HashMap.SipHash

/-! ## The four message bytes as one word -/

private theorem testBit_toUInt8 {k : UInt32} {r : Nat} (hr : r < 8) :
    (k.toUInt8).toNat.testBit r = k.toNat.testBit r := by
  rw [UInt32.toNat_toUInt8, Nat.testBit_mod_two_pow]
  simp [hr]

private theorem testBit_shiftRight_toUInt8 (k : UInt32) (c : Nat) {r : Nat}
    (hr : r < 8) (hc : c < 32) (s : UInt32) (hs : s.toNat = c) :
    ((k >>> s).toUInt8).toNat.testBit r = k.toNat.testBit (c + r) := by
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, hs, Nat.mod_eq_of_lt hc,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hr]

/-- The four little-endian bytes of a `u32` pack back to the same `u32`. -/
theorem u64OfBytesLE_encodeU32 (k : UInt32) :
    u64OfBytesLE (WordCodec.encodeU32 k) = k.toUInt64 := by
  rw [← UInt64.toNat_inj]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Table.u64OfBytesLE_testBit _ (by simp [WordCodec.encodeU32]) i,
    UInt32.toNat_toUInt64]
  by_cases hi : i < 32
  · have hr : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hd : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    rcases hd with h | h | h | h <;>
      simp only [WordCodec.encodeU32, h, List.getD_cons_zero, List.getD_cons_succ]
    · rw [testBit_toUInt8 hr]
      congr 1
      omega
    · rw [testBit_shiftRight_toUInt8 k 8 hr (by norm_num) 8 rfl]
      congr 1
      omega
    · rw [testBit_shiftRight_toUInt8 k 16 hr (by norm_num) 16 rfl]
      congr 1
      omega
    · rw [testBit_shiftRight_toUInt8 k 24 hr (by norm_num) 24 rfl]
      congr 1
      omega
  · have hlen : (WordCodec.encodeU32 k).length ≤ i / 8 := by
      simp [WordCodec.encodeU32]
      omega
    rw [List.getD_eq_default _ _ hlen]
    have hk : k.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le k.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hk]

/-! ## The length byte does not meet the key -/

/-- The length byte of the last block and a `u32` key hold disjoint bits, so
the `or` of the model is the `xor` the compiler folded into the constant. -/
theorem or_lengthByte_eq_xor {key : UInt64} (hkey : key.toNat < 2 ^ 32) :
    (0x0400000000000000 : UInt64) ||| key = 0x0400000000000000 ^^^ key := by
  have hconst : (0x0400000000000000 : UInt64).toNat = 2 ^ 58 := by
    have h1 : (0x0400000000000000 : UInt64).toNat = 288230376151711744 := rfl
    rw [h1]
    norm_num
  rw [← UInt64.toNat_inj, UInt64.toNat_or, UInt64.toNat_xor, hconst]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : (58 : Nat) = i
  · subst hi
    have hk : key.toNat.testBit 58 = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hkey (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    simp [hk]
  · simp [hi]

/-- Four bytes are shorter than one block, so `absorb` takes them all to
the tail. -/
private theorem absorb_encodeU32 (k0 k1 : UInt64) (k : UInt32) :
    absorb (init k0 k1) (WordCodec.encodeU32 k)
      = (init k0 k1, WordCodec.encodeU32 k) := by
  simp [WordCodec.encodeU32, absorb]

set_option maxHeartbeats 1000000 in
/-- `hashU32` runs one `compress` only, on the key with the length byte. -/
theorem sipHash13_encodeU32 (k0 k1 : UInt64) (k : UInt32) :
    sipHash13 k0 k1 (WordCodec.encodeU32 k)
      = finalize (compress (0x0400000000000000 ^^^ k.toUInt64) (init k0 k1)) := by
  have hkey : (k.toUInt64).toNat < 2 ^ 32 := by
    rw [UInt32.toNat_toUInt64]
    exact k.toNat_lt
  unfold sipHash13
  rw [absorb_encodeU32]
  dsimp only
  rw [show (WordCodec.encodeU32 k).length = 4 from rfl, u64OfBytesLE_encodeU32,
    show (UInt64.ofNat (4 % 256) <<< 56 : UInt64) = 0x0400000000000000 from rfl,
    or_lengthByte_eq_xor hkey]

/-! ## The hoisted values -/

/-- The six values that func 17 computes once, above the rehash loop.  Each
field carries the number of its WAT local. -/
structure Hoist where
  /-- Local 16: `v0 + v1` of the start state. -/
  sum01 : UInt64
  /-- Local 18: `rotl (v0 + v1) 32`. -/
  rot0 : UInt64
  /-- Local 19: `v1` after its first update. -/
  mid1 : UInt64
  /-- Local 20: `rotl` of local 19 by 17.  This is the part of the second
  `v1` update that does not read `v2`. -/
  pre1 : UInt64
  /-- Local 21: `v3` of the start state with the length byte folded in. -/
  base3 : UInt64
  /-- Local 26: `v2` of the start state. -/
  base2 : UInt64
  deriving Repr, DecidableEq

/-- The hoisted values of the two seeds. -/
def hoist (k0 k1 : UInt64) : Hoist :=
  let s := init k0 k1
  let sum01 := s.v0 + s.v1
  let mid1 := rotl s.v1 13 ^^^ sum01
  { sum01 := sum01
    rot0 := rotl sum01 32
    mid1 := mid1
    pre1 := rotl mid1 17
    base3 := s.v3 ^^^ 0x0400000000000000
    base2 := s.v2 }

/-- The state that the loop body builds for one key, from the hoisted
values.  This is `compress` of the key, written the way the code writes it. -/
def stateFromHoist (h : Hoist) (key : UInt64) : State :=
  let w3 := h.base3 ^^^ key
  let a2 := h.base2 + w3
  let c3 := rotl w3 16 ^^^ a2
  let b2 := a2 + h.mid1
  let c0 := h.rot0 + c3
  { v0 := c0 ^^^ 0x0400000000000000 ^^^ key
    v1 := h.pre1 ^^^ b2
    v2 := rotl b2 32
    v3 := rotl c3 21 ^^^ c0 }

set_option maxHeartbeats 1000000 in
theorem compress_eq_stateFromHoist (k0 k1 key : UInt64) :
    compress (0x0400000000000000 ^^^ key) (init k0 k1)
      = stateFromHoist (hoist k0 k1) key := by
  unfold compress round stateFromHoist hoist
  simp only [UInt64.xor_assoc]

/-- `hashU32` from the hoisted values.  This is what the rehash loop
computes for one key. -/
theorem hashU32_eq_hoist (k0 k1 : UInt64) (k : UInt32) :
    hashU32 k0 k1 k = finalize (stateFromHoist (hoist k0 k1) k.toUInt64) := by
  rw [show hashU32 k0 k1 k = sipHash13 k0 k1 (WordCodec.encodeU32 k) from rfl,
    sipHash13_encodeU32, compress_eq_stateFromHoist]

end Wasm.RustStd.HashMap.SipHash
