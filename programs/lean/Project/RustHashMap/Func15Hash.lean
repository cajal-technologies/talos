import CodeLib.RustStd.HashMap.HashLowWord
import CodeLib.RustStd.HashMap.SipHoist

/-!
# The hash that func 18 computes inline

`HashMap::insert`, absolute func 18, hashes its key with SipHash-1-3 inline.
WAT lines 4139 to 4300 of `programs/rust/build/rust_hash_map/program.wat` hold
one straight run of `i64` arithmetic with no call and no branch.  The run ends
at `local.set 5`, and every later reader of the hash takes bits 0 to 31 only.

`inlineHash` is that run.  Every operand order is the order of the two pushes,
because the interpreter does not state `i64.add` or `i64.xor` as commutative.
The compiled code does not use one order: the first round of the finalize adds
`v0 + v1` while the later rounds add `v1 + v0`, which is why there are two
round shapes here.

`inlineHash_eq_hashU32Low` is the bridge to the model.  It goes to
`SipHash.hashU32Low`, not to `SipHash.hashU32`, because the compiled last
round closes with `i64.shr_u 32` where the model rotates.  Compose it with
`Table.h1_hashU32Low` and `Table.h2_hashU32Low` to speak about
`SipHash.hashU32`.

The two seed words come from the table header: `k0` at `mapBase + 16` and `k1`
at `mapBase + 24`.  The four constants of `SipHash.init` appear folded: the
`v3` constant of the WAT is `0x7065646279746573`, which is the model constant
with bit 58 cleared, because the message of a `u32` key is four bytes and the
compiler folded the length byte into the start state.
-/

namespace Project.RustHashMap.Func15Hash

open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.SipHash

/-! ## Xor as a commutative group -/

theorem xor_left_comm (a b c : UInt64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt64.xor_assoc, UInt64.xor_comm a b, UInt64.xor_assoc]

theorem xor_self_xor (a b : UInt64) : a ^^^ (a ^^^ b) = b := by
  rw [← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

theorem uadd_left_comm (a b c : UInt64) : a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

-- The rewrite set that normalizes a run of `i64.xor` and `i64.add`.
attribute [local simp] UInt64.xor_assoc UInt64.xor_comm xor_left_comm
  xor_self_xor UInt64.add_assoc UInt64.add_comm uadd_left_comm

/-! ## The three round shapes -/

/-- `SipHash.round` in the operand order of the first finalize round, WAT 4191
to 4247. -/
def roundWasm1 (s : State) : State :=
  let v0a := s.v0 + s.v1
  let v1a := v0a ^^^ rotl s.v1 13
  let v2a := s.v2 + s.v3
  let v3a := v2a ^^^ rotl s.v3 16
  let v2b := v1a + v2a
  let v0c := v3a + rotl v0a 32
  { v0 := v0c, v1 := v2b ^^^ rotl v1a 17, v2 := rotl v2b 32,
    v3 := rotl v3a 21 ^^^ v0c }

/-- `SipHash.round` in the operand order of the second finalize round, WAT
4218 to 4284. -/
def roundWasm2 (s : State) : State :=
  let v0a := s.v1 + s.v0
  let v1a := rotl s.v1 13 ^^^ v0a
  let v2a := s.v3 + s.v2
  let v3a := rotl s.v3 16 ^^^ v2a
  let v2b := v1a + v2a
  let v0c := v3a + rotl v0a 32
  { v0 := v0c, v1 := rotl v1a 17 ^^^ v2b, v2 := rotl v2b 32,
    v3 := rotl v3a 21 ^^^ v0c }

/-- The third round and the four-way xor of the finalize, WAT 4254 to 4299.
The compiler cancelled `v0` against the copy of `v0` inside `v3`, so neither
`v0` nor the closing `rotl` of `v2` is computed. -/
def finalWasm (s : State) : UInt64 :=
  let v0a := s.v1 + s.v0
  let v1a := rotl s.v1 13 ^^^ v0a
  let v2a := s.v3 + s.v2
  let v3a := rotl s.v3 16 ^^^ v2a
  let v2b := v1a + v2a
  (rotl v1a 17 ^^^ rotl v3a 21) ^^^ (v2b >>> 32) ^^^ v2b

theorem roundWasm1_eq (s : State) : roundWasm1 s = round s := by
  unfold roundWasm1 SipHash.round
  simp only [UInt64.add_comm, UInt64.xor_comm]

theorem roundWasm2_eq (s : State) : roundWasm2 s = round s := by
  unfold roundWasm2 SipHash.round
  simp only [UInt64.add_comm, UInt64.xor_comm]

theorem finalWasm_eq (s : State) :
    finalWasm s
      = (roundLow s).v0 ^^^ (roundLow s).v1 ^^^ (roundLow s).v2
          ^^^ (roundLow s).v3 := by
  unfold finalWasm roundLow
  simp

/-! ## The single compress -/

/-- WAT 4139 to 4190: the state after the one `compress` of the four key
bytes.  `k0w` is the word at `mapBase + 16` and `k1w` is the word at
`mapBase + 24`. -/
def compressWasm (k0w k1w : UInt64) (key : UInt32) : State :=
  let key64 : UInt64 := key.toUInt64
  let w3 := k1w ^^^ key64 ^^^ 8098989879002948979
  let a2 := w3 + (k0w ^^^ 7816392313619706465)
  let c3 := rotl w3 16 ^^^ a2
  let v1 := k1w ^^^ 7237128888997146477
  let sum01 := v1 + (k0w ^^^ 8317987319222330741)
  let c0 := c3 + rotl sum01 32
  let mid1 := rotl v1 13 ^^^ sum01
  let b2 := mid1 + a2
  { v0 := c0 ^^^ (key64 ||| 288230376151711744)
    v1 := b2 ^^^ rotl mid1 17
    v2 := rotl b2 32
    v3 := rotl c3 21 ^^^ c0 }

set_option maxHeartbeats 1000000 in
theorem compressWasm_eq (k0w k1w : UInt64) (key : UInt32) :
    compressWasm k0w k1w key
      = compress (0x0400000000000000 ^^^ key.toUInt64) (init k0w k1w) := by
  have hkey : (key.toUInt64).toNat < 2 ^ 32 := by
    rw [UInt32.toNat_toUInt64]
    exact key.toNat_lt
  have hor : (key.toUInt64 ||| 288230376151711744 : UInt64)
      = 0x0400000000000000 ^^^ key.toUInt64 := by
    rw [UInt64.or_comm]
    exact or_lengthByte_eq_xor hkey
  have hconst : (8098989879002948979 : UInt64)
      = 0x7465646279746573 ^^^ 0x0400000000000000 := by decide
  unfold compressWasm compress SipHash.round init
  simp only [hor, hconst]
  simp

/-! ## The whole run -/

/-- The `i64` run of WAT 4139 to 4300. -/
def inlineHash (k0w k1w : UInt64) (key : UInt32) : UInt64 :=
  let s := compressWasm k0w k1w key
  finalWasm (roundWasm2 (roundWasm1 { s with v2 := s.v2 ^^^ 255 }))

/-- `hashU32Low` runs one `compress` only, because four bytes are shorter than
one block.  This is `SipHash.sipHash13_encodeU32` for the compiled finalize. -/
theorem hashU32Low_eq_compress (k0 k1 : UInt64) (k : UInt32) :
    hashU32Low k0 k1 k
      = finalizeLow (compress (0x0400000000000000 ^^^ k.toUInt64) (init k0 k1)) := by
  have hkey : (k.toUInt64).toNat < 2 ^ 32 := by
    rw [UInt32.toNat_toUInt64]
    exact k.toNat_lt
  unfold hashU32Low sipHash13Low
  rw [show absorb (init k0 k1) (Wasm.WordCodec.encodeU32 k)
        = (init k0 k1, Wasm.WordCodec.encodeU32 k) by
      simp [Wasm.WordCodec.encodeU32, absorb]]
  dsimp only
  rw [show (Wasm.WordCodec.encodeU32 k).length = 4 from rfl, u64OfBytesLE_encodeU32,
    show (UInt64.ofNat (4 % 256) <<< 56 : UInt64) = 0x0400000000000000 from rfl,
    or_lengthByte_eq_xor hkey]

/-- The compiled run is the compiled hash. -/
theorem inlineHash_eq_hashU32Low (k0w k1w : UInt64) (key : UInt32) :
    inlineHash k0w k1w key = hashU32Low k0w k1w key := by
  rw [hashU32Low_eq_compress]
  unfold inlineHash finalizeLow
  simp only [compressWasm_eq, roundWasm1_eq, roundWasm2_eq, finalWasm_eq]

end Project.RustHashMap.Func15Hash
