import CodeLib.RustStd.HashMap.Table
import CodeLib.RustStd.HashMap.SipHash

/-!
# The compiled hash agrees with the model on the low word

`SipHash.finalize` closes its last round with `rotl v2 32`.  The compiled
code of `RawTable::insert` puts `i64.shr_u 32` there instead: see WAT func
18, lines 4294 to 4299 of `programs/rust/build/rust_hash_map/program.wat`,
where the closing `i64.rotl` of the model becomes `i64.shr_u`.  The two
words are different in general: `rotl v2 32` moves the low half of `v2` to
the high half of the result, and `v2 >>> 32` makes the high half zero.

The compiler is correct because only the low 32 bits of the hash are read.
`Table.h1` reads bits 0 to 31 and `Table.h2` reads bits 25 to 31.  This
module names that relation `AgreeLow32`, proves it for the compiled
finalize, and lifts it to both readers.  A body proof of func 17 or func 18
can therefore step the shift form and still speak about `SipHash.hashU32`.

`roundLow`, `finalizeLow`, `sipHash13Low` and `hashU32Low` are the compiled
forms.  They are a bridge, not a specification.  Use `SipHash.hashU32` in
every contract.

The `AgreeLow32` lemmas belong beside `SipHash.rotl`.
-/

namespace Wasm.RustStd.HashMap

/-- Two 64-bit words hold the same low 32 bits. -/
def AgreeLow32 (a b : UInt64) : Prop := a.toNat % 2 ^ 32 = b.toNat % 2 ^ 32

theorem agreeLow32_of_testBit {a b : UInt64}
    (h : ∀ i : Nat, i < 32 → a.toNat.testBit i = b.toNat.testBit i) :
    AgreeLow32 a b := by
  unfold AgreeLow32
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · rw [h i hi]
  · simp [hi]

/-- Read one low bit out of an `AgreeLow32`. -/
theorem AgreeLow32.testBit {a b : UInt64} (h : AgreeLow32 a b) {i : Nat}
    (hi : i < 32) : a.toNat.testBit i = b.toNat.testBit i := by
  have hbit : (a.toNat % 2 ^ 32).testBit i = (b.toNat % 2 ^ 32).testBit i :=
    congrArg (fun n : Nat => n.testBit i) h
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at hbit
  simpa [hi] using hbit

/-- `xor` on the right keeps the relation. -/
theorem AgreeLow32.xor_left {a b : UInt64} (h : AgreeLow32 a b) (c : UInt64) :
    AgreeLow32 (a ^^^ c) (b ^^^ c) := by
  apply agreeLow32_of_testBit
  intro i hi
  rw [UInt64.toNat_xor, UInt64.toNat_xor, Nat.testBit_xor, Nat.testBit_xor,
    h.testBit hi]

/-- `xor` on the left keeps the relation. -/
theorem AgreeLow32.xor_right {a b : UInt64} (h : AgreeLow32 a b) (c : UInt64) :
    AgreeLow32 (c ^^^ a) (c ^^^ b) := by
  apply agreeLow32_of_testBit
  intro i hi
  rw [UInt64.toNat_xor, UInt64.toNat_xor, Nat.testBit_xor, Nat.testBit_xor,
    h.testBit hi]

namespace SipHash

/-- A left rotation by 32 and a right shift by 32 agree on the low word.
This is the one step where the compiled hash leaves the model. -/
theorem agreeLow32_rotl32 (x : UInt64) : AgreeLow32 (rotl x 32) (x >>> 32) := by
  have hx : rotl x 32 = (x <<< 32) ||| (x >>> 32) := rfl
  apply agreeLow32_of_testBit
  intro i hi
  have hzero : (x.toNat <<< ((32 : UInt64).toNat % 64) % 2 ^ 64).testBit i
      = false := by
    simp only [show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    simp [Nat.not_le.mpr hi]
  rw [hx, UInt64.toNat_or, Nat.testBit_or, UInt64.toNat_shiftLeft, hzero,
    Bool.false_or]

/-- The last round of the compiled hash.  It is `round` with the closing
`rotl v2 32` replaced by `v2 >>> 32`. -/
def roundLow (s : State) : State :=
  let v0 := s.v0 + s.v1
  let v2 := s.v2 + s.v3
  let v1 := rotl s.v1 13 ^^^ v0
  let v3 := rotl s.v3 16 ^^^ v2
  let v0 := rotl v0 32
  let v2 := v2 + v1
  let v0 := v0 + v3
  let v1 := rotl v1 17 ^^^ v2
  let v3 := rotl v3 21 ^^^ v0
  let v2 := v2 >>> 32
  { v0, v1, v2, v3 }

theorem roundLow_v0 (s : State) : (roundLow s).v0 = (round s).v0 := rfl

theorem roundLow_v1 (s : State) : (roundLow s).v1 = (round s).v1 := rfl

theorem roundLow_v3 (s : State) : (roundLow s).v3 = (round s).v3 := rfl

theorem agreeLow32_roundLow_v2 (s : State) :
    AgreeLow32 (round s).v2 (roundLow s).v2 :=
  agreeLow32_rotl32 _

/-- The compiled finalize: three rounds, the last one `roundLow`. -/
def finalizeLow (s : State) : UInt64 :=
  let s := { s with v2 := s.v2 ^^^ 0xff }
  let s := roundLow (round (round s))
  s.v0 ^^^ s.v1 ^^^ s.v2 ^^^ s.v3

theorem agreeLow32_finalizeLow (s : State) :
    AgreeLow32 (finalize s) (finalizeLow s) :=
  ((agreeLow32_roundLow_v2 _).xor_right _).xor_left _

/-- SipHash-1-3 as the compiled code computes it. -/
def sipHash13Low (k0 k1 : UInt64) (msg : List UInt8) : UInt64 :=
  let (s, tail) := absorb (init k0 k1) msg
  let b : UInt64 := (UInt64.ofNat (msg.length % 256) <<< 56) ||| u64OfBytesLE tail
  finalizeLow (compress b s)

/-- The hash of a `u32` key as the compiled code computes it. -/
def hashU32Low (k0 k1 : UInt64) (k : UInt32) : UInt64 :=
  sipHash13Low k0 k1 (WordCodec.encodeU32 k)

theorem agreeLow32_sipHash13Low (k0 k1 : UInt64) (msg : List UInt8) :
    AgreeLow32 (sipHash13 k0 k1 msg) (sipHash13Low k0 k1 msg) := by
  unfold sipHash13 sipHash13Low
  rcases habsorb : absorb (init k0 k1) msg with ⟨s, tail⟩
  exact agreeLow32_finalizeLow _

theorem agreeLow32_hashU32Low (k0 k1 : UInt64) (k : UInt32) :
    AgreeLow32 (hashU32 k0 k1 k) (hashU32Low k0 k1 k) :=
  agreeLow32_sipHash13Low k0 k1 _

end SipHash

namespace Table

private theorem testBit_127 (i : Nat) : (127 : Nat).testBit i = decide (i < 7) := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | n + 7 =>
    have hlt : (127 : Nat) < 2 ^ (n + 7) := by
      calc (127 : Nat) < 2 ^ 7 := by decide
        _ ≤ 2 ^ (n + 7) := Nat.pow_le_pow_right (by decide) (by omega)
    have hge : ¬ (n + 7 < 7) := by omega
    simp [Nat.testBit_lt_two_pow hlt, hge]

/-- `h1` reads bits 0 to 31 only. -/
theorem h1_congr {a b : UInt64} (h : AgreeLow32 a b) : h1 a = h1 b := h

/-- `h2` reads bits 25 to 31 only. -/
theorem h2_congr {a b : UInt64} (h : AgreeLow32 a b) : h2 a = h2 b := by
  unfold h2
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_shiftRight, show (25 : UInt64).toNat % 64 = 25 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, show (0x7f : UInt64).toNat = 127 from rfl,
    testBit_127]
  by_cases hi : i < 7
  · rw [h.testBit (by omega)]
  · simp [hi]

/-- The compiled hash gives the same bucket as the model hash. -/
theorem h1_hashU32Low (k0 k1 : UInt64) (k : UInt32) :
    h1 (SipHash.hashU32 k0 k1 k) = h1 (SipHash.hashU32Low k0 k1 k) :=
  h1_congr (SipHash.agreeLow32_hashU32Low k0 k1 k)

/-- The compiled hash gives the same control byte as the model hash. -/
theorem h2_hashU32Low (k0 k1 : UInt64) (k : UInt32) :
    h2 (SipHash.hashU32 k0 k1 k) = h2 (SipHash.hashU32Low k0 k1 k) :=
  h2_congr (SipHash.agreeLow32_hashU32Low k0 k1 k)

end Table

end Wasm.RustStd.HashMap
