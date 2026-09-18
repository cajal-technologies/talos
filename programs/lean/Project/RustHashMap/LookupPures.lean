import CodeLib.SepLogic.SmallStepTotalLiftingBits
import CodeLib.RustStd.HashMap.TableU32
import CodeLib.RustStd.HashMap.TableRefinement
import CodeLib.RustStd.HashMap.ProbeWasm
import CodeLib.RustStd.HashMap.Swar
import CodeLib.RustStd.HashMap.HashLowWord
import CodeLib.RustStd.HashMap.SipHoist
import CodeLib.RustStd.HashMap.BorshBridge
import Project.RustHashMap.Spec
import Project.RustHashMap.KeyDecoderContract

/-!
# The pure lemmas of the two lookup kernels

`HashMap::contains_key` is absolute `func 12`, WAT lines 2286 to 2554 of
`programs/rust/build/rust_hash_map/program.wat`.  `HashMap::get` is
absolute `func 20`, WAT lines 4771 to 5056.  Both bodies are frameless.
Both inline the same SipHash run and the same probe loop, and both take an
early exit when the item count of the header is zero.

This file holds the pure facts that the two body proofs and the two
drivers need.  It has no separation logic about the compiled state: every
statement here is about the model, about a word, or about one owned range.

## The four groups

* The bit bridges, the hash flattening and the address bridges are copies
  of lemmas in `BitPures.lean`, `Func15Hash.lean`, `Func15Insert.lean`,
  `ProbeStop.lean` and `CollectTail.lean`.  Each copy names its original.
  They are duplicated rather than imported to keep this file's import
  surface at the `CodeLib` layer, and `CollectTail.lean` cannot be
  imported here at all, because it depends on this file.
* The probe lemmas repeat the insert proof as well, with one change.  The
  insert loop runs on a table with room, so it gets its stopping window
  from `1 <= t.growthLeft`.  A lookup runs on a table that `ofEntries`
  filled, and such a table can be exactly full.  `exists_empty_of_clean`
  drops the hypothesis: a `Clean` table always has an `EMPTY` byte,
  because `Shape.cap_lt` keeps the capacity below the bucket count.
* The walk lemmas turn the trace of a compiled probe loop into
  `Table.find ... = none`.  The loop stops at the first window with an
  `EMPTY` byte and the walk lemma needs no key match up to that window.
* The output lemmas turn the model answer into the borsh bytes that
  `Project.RustHashMap.Spec.containsKeyOutput` and
  `Project.RustHashMap.Spec.getOutput` name.

## The zero-item exit

Both bodies read the item count at `mapBase + 12` and return the empty
answer when it is zero.  `find_eq_none_of_items_zero` closes that arm: a
`WF` table with no item has no slot, so the model lookup is `none` too.
-/

namespace Wasm.SmallStep

/-! ## The missing `wasm_twp_pures` cases

Copy of the section with the same name in `BitPures.lean`. -/

macro_rules
  | `(tactic| wasm_twp_pures [twp_addI64 $rest:ident*]) =>
      `(tactic| iapply twp_addI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_andI64_bits $rest:ident*]) =>
      `(tactic| iapply twp_andI64_bits; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_xorI64 $rest:ident*]) =>
      `(tactic| iapply twp_xorI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_rotlI64 $rest:ident*]) =>
      `(tactic| iapply twp_rotlI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_xor $rest:ident*]) =>
      `(tactic| iapply twp_xor; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_clz $rest:ident*]) =>
      `(tactic| iapply twp_clz; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_eqzI64 $rest:ident*]) =>
      `(tactic| iapply twp_eqzI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_neI64 $rest:ident*]) =>
      `(tactic| iapply twp_neI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_eqI64 $rest:ident*]) =>
      `(tactic| iapply twp_eqI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ltS $rest:ident*]) =>
      `(tactic| iapply twp_ltS rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ne $rest:ident*]) =>
      `(tactic| iapply twp_ne rfl; wasm_twp_pures [$rest:ident*])

end Wasm.SmallStep

namespace Project.RustHashMap.LookupPures

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.Table
open Wasm.RustStd.HashMap.SipHash

/-! ## The five rotate bridges

Copy of the section with the same name in `BitPures.lean`. -/

/-- The rotate that `twp_rotlI64` gives, at amount 13. -/
theorem rotlWasm13 (x : UInt64) :
    (let count := (13 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 13 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 16. -/
theorem rotlWasm16 (x : UInt64) :
    (let count := (16 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 16 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 17. -/
theorem rotlWasm17 (x : UInt64) :
    (let count := (17 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 17 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 21. -/
theorem rotlWasm21 (x : UInt64) :
    (let count := (21 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 21 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 32. -/
theorem rotlWasm32 (x : UInt64) :
    (let count := (32 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 32 := rfl

/-! ## The shift-amount bridges

Copy of the section with the same name in `BitPures.lean`. -/

/-- `i64.shr_u` at 1. -/
theorem shrU64Wasm1 (x : UInt64) : x >>> ((1 : UInt64) % 64) = x >>> 1 :=
  rfl

/-- `i64.shr_u` at 25. -/
theorem shrU64Wasm25 (x : UInt64) : x >>> ((25 : UInt64) % 64) = x >>> 25 :=
  rfl

/-- `i64.shr_u` at 32. -/
theorem shrU64Wasm32 (x : UInt64) : x >>> ((32 : UInt64) % 64) = x >>> 32 :=
  rfl

/-- `i64.shl` at 1. -/
theorem shl64Wasm1 (x : UInt64) : x <<< ((1 : UInt64) % 64) = x <<< 1 := rfl

/-- `i32.shr_u` at 3. -/
theorem shrU32Wasm3 (x : UInt32) : x >>> ((3 : UInt32) % 32) = x >>> 3 := rfl

/-- `i32.shl` at 3. -/
theorem shl32Wasm3 (x : UInt32) : x <<< ((3 : UInt32) % 32) = x <<< 3 := rfl

/-- `i32.wrap_i64` as `twp_wrapI64` states it, as the model writes it. -/
theorem wrapWasm (x : UInt64) :
    UInt32.ofNat (x.toNat % 2 ^ 32) = x.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32,
    UInt32.toNat_ofNat_of_lt' (by
      have h : x.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos 32)
      change x.toNat % 2 ^ 32 < 4294967296
      omega)]

/-! ## The hash that the two lookup bodies compute inline

Copy of `Func15Hash.lean`, from `xor_left_comm` on.  Absolute
`func 12` holds the same run at WAT 2292 to 2452 and absolute `func 20` at
WAT 4782 to 4942.  The seeds come from the table header, `k0` at
`mapBase + 16` and `k1` at `mapBase + 24`. -/

section InlineHash

theorem xor_left_comm (a b c : UInt64) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt64.xor_assoc, UInt64.xor_comm a b, UInt64.xor_assoc]

theorem xor_self_xor (a b : UInt64) : a ^^^ (a ^^^ b) = b := by
  rw [← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

theorem uadd_left_comm (a b c : UInt64) : a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

-- The rewrite set that normalizes a run of `i64.xor` and `i64.add`.
attribute [local simp] UInt64.xor_assoc UInt64.xor_comm xor_left_comm
  xor_self_xor UInt64.add_assoc UInt64.add_comm uadd_left_comm

/-- `SipHash.round` in the operand order of the first finalize round. -/
def roundWasm1 (s : State) : State :=
  let v0a := s.v0 + s.v1
  let v1a := v0a ^^^ rotl s.v1 13
  let v2a := s.v2 + s.v3
  let v3a := v2a ^^^ rotl s.v3 16
  let v2b := v1a + v2a
  let v0c := v3a + rotl v0a 32
  { v0 := v0c, v1 := v2b ^^^ rotl v1a 17, v2 := rotl v2b 32,
    v3 := rotl v3a 21 ^^^ v0c }

/-- `SipHash.round` in the operand order of the second finalize round. -/
def roundWasm2 (s : State) : State :=
  let v0a := s.v1 + s.v0
  let v1a := rotl s.v1 13 ^^^ v0a
  let v2a := s.v3 + s.v2
  let v3a := rotl s.v3 16 ^^^ v2a
  let v2b := v1a + v2a
  let v0c := v3a + rotl v0a 32
  { v0 := v0c, v1 := rotl v1a 17 ^^^ v2b, v2 := rotl v2b 32,
    v3 := rotl v3a 21 ^^^ v0c }

/-- The third round and the four-way xor of the finalize.  The compiler
cancelled `v0` against the copy of `v0` inside `v3`, so neither `v0` nor
the closing `rotl` of `v2` is computed. -/
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

/-- The state after the one `compress` of the four key bytes.  `k0w` is the
word at `mapBase + 16` and `k1w` is the word at `mapBase + 24`. -/
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

/-- The `i64` run of the two lookup bodies. -/
def inlineHash (k0w k1w : UInt64) (key : UInt32) : UInt64 :=
  let s := compressWasm k0w k1w key
  finalWasm (roundWasm2 (roundWasm1 { s with v2 := s.v2 ^^^ 255 }))

/-- `hashU32Low` runs one `compress` only, because four bytes are shorter
than one block. -/
theorem hashU32Low_eq_compress (k0 k1 : UInt64) (k : UInt32) :
    hashU32Low k0 k1 k
      = finalizeLow
          (compress (0x0400000000000000 ^^^ k.toUInt64) (init k0 k1)) := by
  have hkey : (k.toUInt64).toNat < 2 ^ 32 := by
    rw [UInt32.toNat_toUInt64]
    exact k.toNat_lt
  unfold hashU32Low sipHash13Low
  rw [show absorb (init k0 k1) (Wasm.WordCodec.encodeU32 k)
        = (init k0 k1, Wasm.WordCodec.encodeU32 k) by
      simp [Wasm.WordCodec.encodeU32, absorb]]
  dsimp only
  rw [show (Wasm.WordCodec.encodeU32 k).length = 4 from rfl,
    u64OfBytesLE_encodeU32,
    show (UInt64.ofNat (4 % 256) <<< 56 : UInt64) = 0x0400000000000000
      from rfl,
    or_lengthByte_eq_xor hkey]

/-- The compiled run is the compiled hash. -/
theorem inlineHash_eq_hashU32Low (k0w k1w : UInt64) (key : UInt32) :
    inlineHash k0w k1w key = hashU32Low k0w k1w key := by
  rw [hashU32Low_eq_compress]
  unfold inlineHash finalizeLow
  simp only [compressWasm_eq, roundWasm1_eq, roundWasm2_eq, finalWasm_eq]

end InlineHash

/-! ## Small word bridges

Copy of `Func15Insert.lean`, from `addNegEight` on. -/

theorem addNegEight (x : UInt32) : x + 4294967288 = x - 8 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967288 : UInt32).toNat = 4294967288 from rfl,
    show (8 : UInt32).toNat = 8 from rfl] at *
  omega

theorem negEightAdd (x : UInt32) : 4294967288 + x = x - 8 := by
  rw [UInt32.add_comm]; exact addNegEight x

theorem addNegFour (x : UInt32) : x + 4294967292 = x - 4 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967292 : UInt32).toNat = 4294967292 from rfl,
    show (4 : UInt32).toNat = 4 from rfl] at *
  omega

theorem negFourAdd (x : UInt32) : 4294967292 + x = x - 4 := by
  rw [UInt32.add_comm]; exact addNegFour x

theorem shl3_ofNat (i : Nat) :
    UInt32.ofNat i <<< (3 : UInt32) = UInt32.ofNat (8 * i) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (3 : UInt32).toNat % 32 = 3 from rfl]
  simp only [Nat.shiftLeft_eq, Nat.pow_succ]
  omega

/-- The key address of bucket `i`, in the operand order the compiled code
leaves on the stack.  Copy of `Func15Insert.lean:144`. -/
theorem slotAddr_of_wasm (ctrl : UInt32) (i : Nat) :
    ctrl - (UInt32.ofNat i <<< (3 : UInt32)) - 8 = bucketAddr ctrl i := by
  rw [shl3_ofNat, sub_sub_addr, bucketAddr, Nat.mul_succ, UInt32.ofNat_add]
  rfl

/-- Copy of `Func15Insert.lean:232`. -/
theorem sub_eight_add_four (x : UInt32) : x - 8 + 4 = x - 4 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (8 : UInt32).toNat = 8 from rfl,
    show (4 : UInt32).toNat = 4 from rfl] at *
  omega

/-- The value address of bucket `i`.  Copy of `Func15Insert.lean:239`. -/
theorem slotValueAddr_of_wasm (ctrl : UInt32) (i : Nat) :
    ctrl - (UInt32.ofNat i <<< (3 : UInt32)) - 4 = bucketAddr ctrl i + 4 := by
  rw [← slotAddr_of_wasm ctrl i, sub_eight_add_four]

/-- The three address facts that the offset-free `twp_load32_addr` asks
for.  Copy of `Func15Insert.lean:244`. -/
theorem addr3 (addr : UInt32) (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧ (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- `Group::match_empty` in the operand order of the compiled test.
Moved out of `Project.RustHashMap.LookupProbe`. -/
theorem swarMatchEmpty_wasm (x : UInt64) :
    (x &&& (x <<< 1)) &&& 9259542123273814144 = Table.swarMatchEmpty x :=
  rfl

/-- The next stride register, as a number.  Moved out of
`Project.RustHashMap.LookupProbe`. -/
theorem stride_step (n : Nat) (hn : 8 * n < UInt32.size) :
    (8 : UInt32) + UInt32.ofNat (8 * n) = UInt32.ofNat (8 * (n + 1)) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
    show (8 : UInt32).toNat = 8 from rfl]
  have hlt : 8 * n % UInt32.size = 8 * n := Nat.mod_eq_of_lt hn
  change (8 + 8 * n % 4294967296) % 4294967296 = 8 * (n + 1) % 4294967296
  omega

/-! ## One owned range as words

Copies of `outWords` in `Func15Insert.lean` and of `wordPair` in
`CollectTail.lean`. -/

section Memory

variable {α : Type} [WasmHeapGS α]

/-- An eight-byte range is two owned words. -/
theorem outWords (memId : Nat) (ptr : UInt32)
    (bytes : List UInt8) (hlength : bytes.length = 8)
    (hnowrap : ptr.toNat + 8 < UInt32.size) :
    Slices.ByteSlice (α := α) memId ptr bytes ⊢
      iprop(∃ w0 : UInt32, ∃ w1 : UInt32,
        pointsTo_u32 memId ptr w0 ∗ pointsTo_u32 memId (ptr + 4) w1) := by
  have hhead : (bytes.take 4).length = 4 := by rw [List.length_take]; omega
  have htail : (bytes.drop 4).length = 4 := by rw [List.length_drop]; omega
  have hstep : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using Slices.byteOffset_toNat ptr 4 (by omega)
  have happ :=
    (Slices.ByteSlice_append (α := α) memId ptr (bytes.take 4)
      (bytes.drop 4)).mp
  rw [List.take_append_drop, hhead,
    show (UInt32.ofNat 4 : UInt32) = 4 from rfl] at happ
  iintro Hbytes
  icases happ $$ Hbytes with ⟨Hhead, Htail⟩
  iexists WordCodec.decodeU32 (bytes.take 4)
  iexists WordCodec.decodeU32 (bytes.drop 4)
  isplitl [Hhead]
  · iapply (Slices.ByteSlice_four_as_word memId ptr (bytes.take 4) hhead
      (by omega)).mp
    iexact Hhead
  · iapply (Slices.ByteSlice_four_as_word memId (ptr + 4) (bytes.drop 4)
      htail (by omega)).mp
    iexact Htail

/-- The `u64` that two adjacent words pack into. -/
def wordPair (w0 w1 : UInt32) : UInt64 :=
  HashMap.Table.groupWord
    [u32Byte w0 0, u32Byte w0 1, u32Byte w0 2, u32Byte w0 3,
      u32Byte w1 0, u32Byte w1 1, u32Byte w1 2, u32Byte w1 3]

/-- Two adjacent owned words are one owned `u64`. -/
theorem pointsTo_u32_pair_as_groupWord (memId : Nat) (addr : UInt32)
    (w0 w1 : UInt32) :
    iprop(pointsTo_u32 (α := α) memId addr w0 ∗
        pointsTo_u32 memId (addr + 4) w1) ⊣⊢
      pointsTo_u64 memId addr (wordPair w0 w1) := by
  unfold wordPair
  refine (BI.sep_congr (pointsTo_u32_as_bytes memId addr w0)
    (pointsTo_u32_as_bytes memId (addr + 4) w1)).trans ?_
  refine (pointsToBytes_append (α := α) memId addr
    [u32Byte w0 0, u32Byte w0 1, u32Byte w0 2, u32Byte w0 3]
    [u32Byte w1 0, u32Byte w1 1, u32Byte w1 2, u32Byte w1 3]).symm.trans ?_
  exact HashMap.Table.pointsToBytes_eight_as_u64 memId addr
    [u32Byte w0 0, u32Byte w0 1, u32Byte w0 2, u32Byte w0 3,
      u32Byte w1 0, u32Byte w1 1, u32Byte w1 2, u32Byte w1 3] rfl

/-- The four header words are two `u64` cells. -/
theorem tableHeader_as_u64 (memId : Nat)
    (base ctrl mask growthLeft items : UInt32) :
    HashMap.Table.tableHeader (α := α) memId base ctrl mask growthLeft
        items ⊣⊢
      iprop(pointsTo_u64 memId base (wordPair ctrl mask) ∗
        pointsTo_u64 memId (base + 8) (wordPair growthLeft items)) := by
  have e12 : base + 12 = base + 8 + 4 := by rw [UInt32.add_assoc]; rfl
  unfold HashMap.Table.tableHeader
  rw [e12]
  refine BI.sep_assoc.symm.trans ?_
  exact BI.sep_congr (pointsTo_u32_pair_as_groupWord memId base ctrl mask)
    (pointsTo_u32_pair_as_groupWord memId (base + 8) growthLeft items)

/-- A table names its base address only in the header, so a caller that
rebuilds the header at another address holds the table there. -/
theorem TableAt_relocate (memId : Nat) (src dst : UInt32)
    (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.TableAt (α := α) memId src t ⊢
      iprop(∃ ctrl : UInt32, ∃ mask : UInt32, ∃ growthLeft : UInt32,
        ∃ items : UInt32,
        HashMap.Table.tableHeader memId src ctrl mask growthLeft items ∗
        (HashMap.Table.tableHeader memId dst ctrl mask growthLeft items -∗
          HashMap.Table.TableAt memId dst t)) := by
  iintro Htable
  isimp only [HashMap.Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Hbody⟩
  icases Hbody with (Hsingleton | ⟨%hbuckets, Hallocated⟩)
  · isimp only [HashMap.Table.SingletonBody] at Hsingleton
    icases Hsingleton with ⟨%hfacts, Hheader, Hctrl⟩
    iexists ctrl, (0 : UInt32), (0 : UInt32), (0 : UInt32)
    isplitl [Hheader]
    · iexact Hheader
    · iintro Hheader
      isimp only [HashMap.Table.TableAt]
      iexists ctrl
      ileft
      isimp only [HashMap.Table.SingletonBody]
      isplitl_pureexact hfacts
      · iframe Hheader Hctrl
  · isimp only [HashMap.Table.TableBody] at Hallocated
    icases Hallocated with ⟨%hctrlBound, Hheader, Hbytes, Hslots⟩
    iexists ctrl, (UInt32.ofNat (t.buckets - 1)),
      (UInt32.ofNat t.growthLeft), (UInt32.ofNat t.items)
    isplitl [Hheader]
    · iexact Hheader
    · iintro Hheader
      isimp only [HashMap.Table.TableAt]
      iexists ctrl
      iright
      isplitl_pureexact hbuckets
      · isimp only [HashMap.Table.TableBody]
        isplitl_pureexact hctrlBound
        · iframe Hheader Hbytes Hslots

/-- The whole 32-byte map value as four `u64` cells, and the wand that puts
it back at another address. -/
theorem HashMapAt_move (memId : Nat) (src dst : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.HashMapAt (α := α) memId src k0 k1 t ⊢
      iprop(∃ v0 : UInt64, ∃ v1 : UInt64,
        pointsTo_u64 memId src v0 ∗ pointsTo_u64 memId (src + 8) v1 ∗
        pointsTo_u64 memId (src + 16) k0 ∗
        pointsTo_u64 memId (src + 24) k1 ∗
        (pointsTo_u64 memId dst v0 -∗ pointsTo_u64 memId (dst + 8) v1 -∗
          pointsTo_u64 memId (dst + 16) k0 -∗
          pointsTo_u64 memId (dst + 24) k1 -∗
          HashMap.Table.HashMapAt memId dst k0 k1 t)) := by
  iintro Hmap
  isimp only [HashMap.Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  ihave ⟨%ctrl, %mask, %growthLeft, %items, Hheader, Hback⟩ :=
    TableAt_relocate memId src dst t $$ Htable
  ihave Hcells :=
    (tableHeader_as_u64 memId src ctrl mask growthLeft items).mp $$ Hheader
  icases Hcells with ⟨Hc0, Hc1⟩
  iexists (wordPair ctrl mask), (wordPair growthLeft items)
  iframe Hc0 Hc1 Hk0 Hk1
  iintro Hd0 Hd1 Hdk0 Hdk1
  ihave Hheader :
      HashMap.Table.tableHeader memId dst ctrl mask growthLeft items
      $$ [Hd0 Hd1]
  · iapply (tableHeader_as_u64 memId dst ctrl mask growthLeft items).mpr
    iframe Hd0 Hd1
  ihave Htable := Hback $$ Hheader
  isimp only [HashMap.Table.HashMapAt]
  iframe Htable Hdk0 Hdk1

/-- A 32-byte slice is four `u64` cells. -/
theorem ByteSlice_thirtyTwo_as_cells (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (hlength : bytes.length = 32) :
    Slices.ByteSlice (α := α) memId addr bytes ⊢
      iprop(∃ d0 : UInt64, ∃ d1 : UInt64, ∃ d2 : UInt64, ∃ d3 : UInt64,
        pointsTo_u64 memId addr d0 ∗ pointsTo_u64 memId (addr + 8) d1 ∗
        pointsTo_u64 memId (addr + 16) d2 ∗
        pointsTo_u64 memId (addr + 24) d3) := by
  obtain ⟨x0, x1, x2, x3, hcat, hl0, hl1, hl2, hl3⟩ :
      ∃ x0 x1 x2 x3 : List UInt8, bytes = x0 ++ (x1 ++ (x2 ++ x3)) ∧
        x0.length = 8 ∧ x1.length = 8 ∧ x2.length = 8 ∧ x3.length = 8 := by
    refine ⟨bytes.take 8, (bytes.drop 8).take 8, (bytes.drop 16).take 8,
      bytes.drop 24, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show bytes.drop 24 = (bytes.drop 16).drop 8 by
        rw [List.drop_drop], List.take_append_drop,
        show bytes.drop 16 = (bytes.drop 8).drop 8 by rw [List.drop_drop],
        List.take_append_drop, List.take_append_drop]
    · rw [List.length_take]; omega
    · rw [List.length_take, List.length_drop]; omega
    · rw [List.length_take, List.length_drop]; omega
    · rw [List.length_drop]; omega
  subst hcat
  have e8 : UInt32.ofNat 8 = (8 : UInt32) := rfl
  have e16 : addr + 8 + 8 = addr + 16 := by rw [UInt32.add_assoc]; rfl
  have e24 : addr + 16 + 8 = addr + 24 := by rw [UInt32.add_assoc]; rfl
  iintro Hslice
  ihave ⟨H0, Hrest⟩ :=
    (Slices.ByteSlice_append memId addr x0 (x1 ++ (x2 ++ x3))).mp $$ Hslice
  isimp only [hl0, e8] at Hrest
  ihave ⟨H1, Hrest⟩ :=
    (Slices.ByteSlice_append memId (addr + 8) x1 (x2 ++ x3)).mp $$ Hrest
  isimp only [hl1, e8, e16] at Hrest
  ihave ⟨H2, H3⟩ :=
    (Slices.ByteSlice_append memId (addr + 16) x2 x3).mp $$ Hrest
  isimp only [hl2, e8, e24] at H3
  ihave ⟨%_hb0, Hc0⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId addr x0 hl0).mp $$ H0
  ihave ⟨%_hb1, Hc1⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId (addr + 8) x1 hl1).mp $$ H1
  ihave ⟨%_hb2, Hc2⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId (addr + 16) x2 hl2).mp $$ H2
  ihave ⟨%_hb3, Hc3⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId (addr + 24) x3 hl3).mp $$ H3
  iexists (HashMap.Table.groupWord x0), (HashMap.Table.groupWord x1),
    (HashMap.Table.groupWord x2), (HashMap.Table.groupWord x3)
  iframe Hc0 Hc1 Hc2 Hc3

end Memory

/-! ## The probe walk -/

section Probe

variable {K V : Type} {hash : K → UInt64} {t : Table K V}

/-- The stride of window `n` is eight groups times `n`.  Copy of
`probeSeq_stride` in `ProbeStop.lean`. -/
theorem probeSeq_stride (t : Table K V) (h : UInt64) (n : Nat) :
    (probeSeq t h n).stride = 8 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [probeSeq, ProbeSeq.next, ih]; omega

/-- `Group::match_tag`, with the `not` on the left and the tag lanes as
`repeatByte`.  Copy of `ProbeStop.lean:89`. -/
theorem swarMatchTag_wasm (tag : UInt8) (x : UInt64) :
    ((x ^^^ repeatByte tag) ^^^ 18446744073709551615) &&&
        ((x ^^^ repeatByte tag) + 18374403900871474943) &&&
          9259542123273814144 =
      swarMatchTag tag x := by
  rw [show (9259542123273814144 : UInt64) = REP80 from rfl,
    UInt64.and_comm ((x ^^^ repeatByte tag) ^^^ 18446744073709551615),
    ← repeatByte_eq_mul_REP01]
  exact swarMatchTag_of_wasm tag x

/-- The tag of a hash is a `FULL` control byte.  Copy of
`ProbeStop.lean:99`. -/
theorem isFull_h2 (h : UInt64) : isFull (h2 h) = true := by
  have hb : ((h >>> 25) &&& 127).toNat < 128 := by
    rw [UInt64.toNat_and, show (127 : UInt64).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hlt : (h2 h).toNat < 128 := by
    rw [← UInt8.toNat_toUInt64, h2_toUInt64]
    exact hb
  unfold isFull
  rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt]
  exact hlt

/-- A byte that the compiled `match_tag` flags names a full bucket, so the
slot of that bucket holds a pair.  Copy of `ProbeStop.lean:121`. -/
theorem slotAt_isSome_of_mem_matchBytes (hw : Layout hash t) (h : UInt64)
    (n : Nat) {j : Nat}
    (hj : j ∈ setBytes (swarMatchTag (h2 h) (groupWord (window t h n)))) :
    (t.slotAt (probeIdx t h n j)).isSome = true := by
  have hg : (window t h n).length = 8 := groupAt_length _ _
  simp only [setBytes, List.mem_filter, List.mem_range] at hj
  obtain ⟨hj8, hb⟩ := hj
  have hfullb : isFull ((window t h n).getD j EMPTY) = true :=
    isFull_of_hasBit_swarMatchTag hg hj8 (isFull_h2 h) hb
  rw [hw.window_getD h n j hj8] at hfullb
  by_cases hpad : IsPad t.buckets ((probeSeq t h n).pos + j)
  · rw [if_pos hpad] at hfullb
    exact absurd hfullb (by decide)
  · rw [if_neg hpad] at hfullb
    exact (hw.full_iff _ (hw.probeIdx_lt h n j)).mp hfullb

/-- `slotAt_isSome_of_mem_matchBytes` with `window` and `probeIdx`
unfolded, which is the shape a body proof reads off the compiled probe.
Copy of `ProbeStop.lean:132`. -/
theorem slotAt_isSome_of_mem_matchTag (hw : Layout hash t) (h : UInt64)
    (n : Nat) {j : Nat}
    (hj : j ∈ setBytes
      (swarMatchTag (h2 h) (groupWord (groupAt t (probeSeq t h n).pos)))) :
    (t.slotAt (((probeSeq t h n).pos + j) % t.buckets)).isSome = true :=
  slotAt_isSome_of_mem_matchBytes hw h n hj

/-! ### Where a lookup walk stops

`ProbeStop.exists_empty_window` takes `1 ≤ t.growthLeft`, which a table
that `ofEntries` filled to the last slot does not have.  The hypothesis is
not needed.  `Clean` ties `growthLeft + items` to the capacity, `WF` ties
`items` to the entry list, and `Shape.cap_lt` keeps the capacity below the
bucket count.  A table with no `EMPTY` byte therefore has one item per
bucket, which is more items than the capacity allows. -/

/-- A `Clean` table always has an `EMPTY` byte. -/
theorem exists_empty_of_clean (hw : WF hash t) (hcl : Clean t) :
    ∃ e, e < t.buckets ∧ t.ctrlAt e = EMPTY := by
  by_contra hno
  have hfull : ∀ i, i < t.buckets → (t.slotAt i).isSome = true := by
    intro i hi
    rw [← hw.full_iff i hi]
    rcases hf : isFull (t.ctrlAt i) with _ | _
    · exfalso
      have hsp : isSpecial (t.ctrlAt i) = true :=
        isSpecial_iff.2 (by rw [hf]; decide)
      exact hno ⟨i, hi, hcl.1 i hi hsp⟩
    · rfl
  have hlen : (Table.toList t).length = t.buckets := by
    unfold Table.toList
    rw [List.range_eq_range']
    exact length_filterMap_range' t.slotAt t.buckets 0
      (fun i _ hi => hfull i (by omega))
  have h1 := hw.shape.cap_lt
  have h2 := hw.items_eq
  have h3 := hcl.2
  omega

/-- A `Clean` table has a window with an `EMPTY` byte, inside the probe
fuel.  This is `ProbeStop.exists_empty_window` without the growth
hypothesis. -/
theorem exists_empty_window_of_clean (hw : WF hash t) (hcl : Clean t)
    (h : UInt64) :
    ∃ n, n < probeFuel t ∧ matchEmpty (window t h n) = true := by
  obtain ⟨e, he, hemp⟩ := exists_empty_of_clean hw hcl
  have hne := hw.toLayout.firstSpecial_probe h he hemp
  rcases hf : firstSpecial t h (probeFuel t) 0 with _ | ⟨n, j⟩
  · exact absurd hf hne
  obtain ⟨-, hlt, hls, -⟩ := firstSpecial_some t h _ _ _ _ hf
  unfold window at hls
  obtain ⟨hj, hsp, -⟩ := lowestSpecial_groupAt_some hls
  refine ⟨n, by omega, ?_⟩
  rw [matchEmpty_window]
  refine ⟨j, hj, ?_⟩
  have hp := hw.toLayout.probe_lt h n
  have hmir := hw.toLayout.mirror ((probeSeq t h n).pos + j) (by omega)
  by_cases hpad : IsPad t.buckets ((probeSeq t h n).pos + j)
  · rw [hmir, if_pos hpad]
  · rw [hmir, if_neg hpad]
    rw [hmir, if_neg hpad] at hsp
    exact hcl.1 _ (Nat.mod_lt _ hw.toLayout.pos) hsp

/-- The first window with an `EMPTY` byte.  The compiled loop stops at or
before it, so `N - n` is the measure of the walk.  This is
`ProbeStop.exists_first_empty_window` without the growth hypothesis. -/
theorem exists_first_empty_window_of_clean (hw : WF hash t) (hcl : Clean t)
    (h : UInt64) :
    ∃ N, N < probeFuel t ∧ matchEmpty (window t h N) = true ∧
      ∀ m, m < N → matchEmpty (window t h m) = false := by
  have hex : ∃ n, matchEmpty (window t h n) = true := by
    obtain ⟨n, -, hn⟩ := exists_empty_window_of_clean hw hcl h
    exact ⟨n, hn⟩
  obtain ⟨n, hn, hmatch⟩ := exists_empty_window_of_clean hw hcl h
  refine ⟨Nat.find hex, Nat.lt_of_le_of_lt (Nat.find_le hmatch) hn,
    Nat.find_spec hex, ?_⟩
  intro m hm
  exact Bool.eq_false_iff.mpr (Nat.find_min hex hm)

end Probe

/-! ## From a compiled walk to `find ... = none` -/

section Walk

variable {K V : Type} [BEq K]

/-- The compiled probe loop leaves the walk it made.  No window up to `N`
holds the key, and window `N` has an `EMPTY` byte, so `findLoop` returns
`none` from any earlier window with enough fuel. -/
theorem findLoop_none_of_walk (t : Table K V) (h : UInt64) (tag : UInt8)
    (k : K) (N : Nat) (hstop : matchEmpty (window t h N) = true)
    (hno : ∀ m, m ≤ N →
      (matchTag tag (window t h m)).find?
        (fun j => t.keyIs (probeIdx t h m j) k) = none) :
    ∀ (f s d : Nat), s + d = N → d < f →
      findLoop t tag k f (probeSeq t h s) = none := by
  intro f
  induction f with
  | zero => intro s d _ hd; omega
  | succ f ih =>
    intro s d hsd hd
    have hcur :
        (matchTag tag (groupAt t (probeSeq t h s).pos)).find?
          (fun j => t.keyIs (((probeSeq t h s).pos + j) % t.buckets) k)
          = none :=
      hno s (by omega)
    simp only [findLoop, hcur]
    match d, hsd, hd with
    | 0, hsd, _ =>
      have hsN : s = N := by omega
      subst hsN
      have : matchEmpty (groupAt t (probeSeq t h s).pos) = true := hstop
      simp only [this, if_true]
    | d + 1, hsd, hd =>
      by_cases hemp : matchEmpty (groupAt t (probeSeq t h s).pos) = true
      · simp only [hemp, if_true]
      · rw [Bool.not_eq_true] at hemp
        simp only [hemp]
        exact ih (s + 1) d (by omega) (by omega)

/-- The whole compiled walk: `find` is `none`. -/
theorem find_none_of_walk (t : Table K V) (h : UInt64) (k : K) (N : Nat)
    (hN : N < probeFuel t) (hstop : matchEmpty (window t h N) = true)
    (hno : ∀ m, m ≤ N →
      (matchTag (h2 h) (window t h m)).find?
        (fun j => t.keyIs (probeIdx t h m j) k) = none) :
    find t h k = none :=
  findLoop_none_of_walk t h (h2 h) k N hstop hno (probeFuel t) 0 N
    (by omega) hN

end Walk

/-! ## The zero-item exit of both bodies -/

section Empty

variable {K V : Type} [BEq K] [LawfulBEq K] {hash : K → UInt64}
variable {t : Table K V}

/-- A `WF` table with no item has no slot, so the model lookup fails.  Both
bodies read the item count at `mapBase + 12` and take this arm when it is
zero. -/
theorem find_eq_none_of_items_zero (hw : WF hash t) (h0 : t.items = 0)
    (k : K) : find t (hash k) k = none := by
  refine (hw.toLayout.find_eq_none_iff k).2 ?_
  intro i hi v hs
  have hmem : (k, v) ∈ Table.toList t := by
    unfold Table.toList
    simp only [List.mem_filterMap, List.mem_range]
    exact ⟨i, hi, hs⟩
  have hlen : (Table.toList t).length = 0 := by rw [← hw.items_eq, h0]
  have hpos := List.length_pos_of_mem hmem
  omega

/-- `contains_key` on a table with no item. -/
theorem containsKey_eq_false_of_items_zero (hw : WF hash t)
    (h0 : t.items = 0) (k : K) : Table.containsKey hash t k = false := by
  unfold Table.containsKey
  rw [find_eq_none_of_items_zero hw h0 k]
  rfl

/-- `get` on a table with no item. -/
theorem get_eq_none_of_items_zero (hw : WF hash t) (h0 : t.items = 0)
    (k : K) : Table.get hash t k = none := by
  unfold Table.get
  rw [find_eq_none_of_items_zero hw h0 k]
  rfl

end Empty

/-! ## The output bytes -/

section Output

open Project.RustHashMap.BodyContracts
open Project.RustHashMap.KeyDecoderContract

/-- A borsh `bool` is the one byte that the compiled body stores.  Both
lookup bodies leave the answer as a `u32` that is `0` or `1`. -/
theorem borsh_bool_eq_byte (b : Bool) :
    Borsh.bool b = [(if b then (1 : UInt32) else 0).toUInt8] := by
  cases b <;> rfl

/-- A borsh `Option<u32>` on the `none` arm. -/
theorem borsh_option_none :
    Borsh.option Borsh.u32 none = [0] := rfl

/-- A borsh `Option<u32>` on the `some` arm, with the payload in the word
form that the driver writes. -/
theorem borsh_option_u32_some (v : UInt32) :
    Borsh.option Borsh.u32 (some v) = 1 :: WordCodec.u32le.serialize [v] := by
  simp [Borsh.option, Borsh.u32, WordCodec.serialize]

/-! ### The model input of an accepted run -/

/-- The map that the model reads from an input the key decoder accepts. -/
def acceptedEntries (bytes : List UInt8) : HashMap.Map UInt32 UInt32 :=
  BorshBridge.wireEntries (mapBytes bytes)

/-- The model of an input that absolute `func 10` accepts.  The key is the
first four bytes and the map is the wire pairs of the rest. -/
theorem keyAndMap_of_accepts (bytes : List UInt8)
    (haccept : KeyDecodeAccepts bytes) :
    Spec.keyAndMap bytes =
      some (leadingKey bytes, HashMap.ofEntries (acceptedEntries bytes)) := by
  obtain ⟨hfour, hdec, hexact⟩ := haccept
  unfold Spec.keyAndMap
  rw [if_neg (by omega), Spec.mapOf,
    BorshBridge.hashMap?_eq_some_of_accepts (bytes.drop 4) hdec hexact.symm]
  rfl

/-- The model of an input that absolute `func 10` rejects.  Three shapes
reject: a short input, a payload that stops before the header says, and a
payload with bytes left over. -/
theorem keyAndMap_eq_none_of_not_accepts (bytes : List UInt8)
    (hreject : ¬ KeyDecodeAccepts bytes) : Spec.keyAndMap bytes = none := by
  unfold Spec.keyAndMap
  by_cases hfour : bytes.length < 4
  · rw [if_pos hfour]
  · rw [if_neg hfour]
    have hrest : Spec.mapOf (bytes.drop 4) = none := by
      unfold Spec.mapOf
      by_cases hdec : DecodeAccepts (mapBytes bytes)
      · refine BorshBridge.hashMap?_eq_none_of_trailing (bytes.drop 4) hdec ?_
        intro hlen
        exact hreject ⟨by omega, hdec, hlen.symm⟩
      · exact BorshBridge.hashMap?_eq_none_of_not_accepts (bytes.drop 4) hdec
    rw [hrest]
    rfl

/-! ### The two outputs -/

/-- The output of `map_contains_key` on an accepted input, as the table
model writes it.  The bound on the entry count is the one that
`Table.containsKey_ofEntries_u32` asks for; the decoder header bounds the
count by the input length, so every caller has it. -/
theorem containsKeyOutput_of_accepts (bytes : List UInt8) (k0 k1 : UInt64)
    (haccept : KeyDecodeAccepts bytes)
    (hn : (acceptedEntries bytes).length ≤ 2 ^ 30) :
    Spec.containsKeyOutput bytes =
      Borsh.bool (Table.containsKey (SipHash.hashU32 k0 k1)
        (Table.ofEntries (SipHash.hashU32 k0 k1) (acceptedEntries bytes))
        (leadingKey bytes)) := by
  unfold Spec.containsKeyOutput
  rw [keyAndMap_of_accepts bytes haccept,
    Table.containsKey_ofEntries_u32 k0 k1 _ hn (leadingKey bytes)]

/-- The output of `map_get` on an accepted input, as the table model writes
it. -/
theorem getOutput_of_accepts (bytes : List UInt8) (k0 k1 : UInt64)
    (haccept : KeyDecodeAccepts bytes)
    (hn : (acceptedEntries bytes).length ≤ 2 ^ 30) :
    Spec.getOutput bytes =
      Borsh.option Borsh.u32 (Table.get (SipHash.hashU32 k0 k1)
        (Table.ofEntries (SipHash.hashU32 k0 k1) (acceptedEntries bytes))
        (leadingKey bytes)) := by
  unfold Spec.getOutput
  rw [keyAndMap_of_accepts bytes haccept,
    Table.get_ofEntries_u32 k0 k1 _ hn (leadingKey bytes)]

/-- The output of `map_contains_key` on a rejected input. -/
theorem containsKeyOutput_of_rejects (bytes : List UInt8)
    (hreject : ¬ KeyDecodeAccepts bytes) :
    Spec.containsKeyOutput bytes = [] := by
  unfold Spec.containsKeyOutput
  rw [keyAndMap_eq_none_of_not_accepts bytes hreject]

/-- The output of `map_get` on a rejected input. -/
theorem getOutput_of_rejects (bytes : List UInt8)
    (hreject : ¬ KeyDecodeAccepts bytes) : Spec.getOutput bytes = [] := by
  unfold Spec.getOutput
  rw [keyAndMap_eq_none_of_not_accepts bytes hreject]

end Output

end Project.RustHashMap.LookupPures
