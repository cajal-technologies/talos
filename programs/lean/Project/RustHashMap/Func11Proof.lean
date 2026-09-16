import Project.RustHashMap.SortPures

/-!
# Proof of `ipnsort`, absolute `func 14`

Absolute `func 14` is `ipnsort`, local `func11`, WAT lines 2635 to 2848
of `programs/rust/build/rust_hash_map/program.wat`.  This module proves
`SortContracts.Func11Spec` from `SortContracts.Func21Spec`, the contract
of `quicksort`, which `Project.RustHashMap.Func21Proof` proves.

## The register map

The body has three parameters and six more registers.

| Register | Meaning |
| --- | --- |
| 0 | the buffer address, never written |
| 1 | the length, and an entry address inside the reverse loop |
| 2 | the comparison closure, and the odd bit of the half length |
| 3 | the key below the scan, and an entry address |
| 4 | the flag that says the first two entries descend |
| 5 | the scan counter, and the reverse counter |
| 6 | the scan pointer, and the address one past the buffer |
| 7 | the key at the scan, and the trip count of the reverse loop |
| 8 | the entry that one exchange holds |

## The regions

| Name | WAT | What it does |
| --- | --- | --- |
| `sortTail` | 2835 to 2847 | the limit and the one call |
| `body1` | 2637 to 2833 | the block that the return leaves |
| `body2` | 2638 to 2832 | the short exit, the scan and the reverse |
| `scanBlock` | 2643 to 2727 | the two scans and the partial-run test |
| `blockFour` | 2644 to 2722 | the descending scan |
| `blockFive` | 2645 to 2687 | the first test and the ascending scan |
| `scanALoop` | 2666 to 2687 | one step of the ascending scan |
| `scanBLoop` | 2701 to 2722 | one step of the descending scan |
| `reverseTail` | 2729 to 2831 | the reverse of a descending run |
| `revBlock` | 2740 to 2808 | the trip count and the unrolled loop |
| `revLoop` | 2758 to 2805 | two exchanges of the reverse |
| `middleSwap` | 2810 to 2831 | the odd exchange in the middle |

## The three loops

The two scans walk forward one entry at a time.  Their invariant is the
neighbour fact of every index below the counter, and the buffer stays as
it was.  The measure is `len - counter`.

The reverse loop counts two exchanges per trip.  The buffer holds
`SortPures.reverseFold pairs k` after `k` exchanges, the trip adds two
with `reverseFold_succ`, and the odd exchange in the middle adds the
last one.  `reverseFold_half` turns the whole run into `List.reverse`.
The measure is `trips - k`.
-/

namespace Project.RustHashMap.Func11Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.SortContracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.SortPures
open scoped Wasm.SmallStep.Outcome

/-! ## Word arithmetic -/

private theorem ofNat_toNat {k : Nat} (h : k < UInt32.size) :
    (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' h

private theorem ofNat_zero : UInt32.ofNat 0 = 0 := rfl

/-- Drop an empty antecedent.  The caller of this body hands back one
resource that the body does not keep, and the contract names it `emp`. -/
private theorem emp_wand_elim {PROP : Type} [BI PROP] {Q : PROP} :
    iprop(emp -∗ Q) ⊢ Q :=
  BI.emp_sep.mpr.trans BI.wand_elim_right

/-- `i32.shl` masks the shift count. -/
private theorem shl_three (x : UInt32) :
    x <<< ((3 : UInt32) % 32) = x <<< 3 := rfl

private theorem shl_one (x : UInt32) :
    x <<< ((1 : UInt32) % 32) = x <<< 1 := rfl

private theorem shr_one (x : UInt32) :
    x >>> ((1 : UInt32) % 32) = x >>> 1 := rfl

/-- `i32.shr_u` by one is a division by two. -/
private theorem shift_right_one (x : UInt32) :
    x >>> (1 : UInt32) = UInt32.ofNat (x.toNat / 2) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hx := UInt32.toNat_lt x
  have hlt : x.toNat / 2 < UInt32.size := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat % 32 = 1 by decide,
    UInt32.toNat_ofNat_of_lt' hlt, Nat.shiftRight_eq_div_pow, pow_one]

/-- The complement of a number that fits in `w` bits. -/
private theorem nat_xor_allOnes (w j : Nat) (h : j < 2 ^ w) :
    j ^^^ (2 ^ w - 1) = 2 ^ w - 1 - j := by
  have h1 : (BitVec.ofNat w j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have h2 : (BitVec.allOnes w).toNat = 2 ^ w - 1 := BitVec.toNat_allOnes
  have h3 := congrArg BitVec.toNat
    (BitVec.xor_allOnes (x := BitVec.ofNat w j))
  rw [BitVec.toNat_xor, BitVec.toNat_not, h1, h2] at h3
  exact h3

/-- An exclusive-or of two even numbers. -/
private theorem two_mul_xor (a b : Nat) :
    2 * a ^^^ 2 * b = 2 * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have ha : 2 * a / 2 = a := by omega
    have hb : 2 * b / 2 = b := by omega
    have hc : 2 * (a ^^^ b) / 2 = a ^^^ b := by omega
    simp [Nat.testBit_succ, ha, hb, hc, Nat.testBit_xor]

/-- A conjunction with an even mask. -/
private theorem two_mul_and (a b c : Nat) (hc : c < 2) :
    (2 * a + c) &&& 2 * b = 2 * (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have ha : (2 * a + c) / 2 = a := by omega
    have hb : 2 * b / 2 = b := by omega
    have hd : 2 * (a &&& b) / 2 = a &&& b := by omega
    simp [Nat.testBit_succ, ha, hb, hd, Nat.testBit_and]

/-- The compiled complement, WAT 2761 to 2762 and 2821 to 2822. -/
private theorem xor_ones_toNat (x : UInt32) :
    (x ^^^ 4294967295).toNat = 4294967295 - x.toNat := by
  have hx : x.toNat < 2 ^ 32 := UInt32.toNat_lt x
  rw [UInt32.toNat_xor,
    show ((4294967295 : UInt32)).toNat = 2 ^ 32 - 1 from rfl,
    nat_xor_allOnes 32 x.toNat hx]
  norm_num

/-- The compiled complement of the second exchange, WAT 2787 to 2788.
The counter is even and below `2 ^ 26`, so every bit it sets is a bit of
the mask and the exclusive-or is a difference. -/
private theorem xor_mask_toNat (i : Nat) (hev : 2 ∣ i)
    (hlt : i < 2 ^ 26) :
    ((UInt32.ofNat i) ^^^ 536870910).toNat = 536870910 - i := by
  have hsz : i < UInt32.size := by
    have : (2 : Nat) ^ 26 < UInt32.size := by decide
    omega
  obtain ⟨j, rfl⟩ := hev
  have hj : j < 2 ^ 28 := by omega
  have hpow : (2 : Nat) ^ 28 = 268435456 := by norm_num
  rw [UInt32.toNat_xor, ofNat_toNat hsz,
    show ((536870910 : UInt32)).toNat = 2 * (2 ^ 28 - 1) from rfl,
    two_mul_xor, nat_xor_allOnes 28 j hj]
  omega

/-! ## Addresses of the entry buffer -/

/-- `i32.shl` by three is a multiplication by eight. -/
private theorem shift_three (x : UInt32)
    (hbound : 8 * x.toNat < UInt32.size) :
    x <<< (3 : UInt32) = UInt32.ofNat (8 * x.toNat) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h2 : (2 : Nat) ^ 3 = 8 := by norm_num
  have hlt : x.toNat * 8 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, show (3 : UInt32).toNat % 32 = 3 by decide,
    Nat.shiftLeft_eq, h2, Nat.mod_eq_of_lt hlt,
    UInt32.toNat_ofNat_of_lt' hbound]
  omega

/-- The address of entry `k`.  `i32.add` puts the second operand first,
so every compiled address of this body has the index on the left. -/
private theorem index_addr (v : UInt32) (k n : Nat) (hk : k ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    UInt32.ofNat k <<< ((3 : UInt32) % 32) + v
      = v + UInt32.ofNat (8 * k) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hkn : k < UInt32.size := by omega
  have hto : (UInt32.ofNat k).toNat = k := ofNat_toNat hkn
  rw [shl_three, shift_three _ (by rw [hto]; omega), hto]
  exact UInt32.add_comm _ _

/-- Adding a small literal to an index. -/
private theorem index_add (c m : Nat) (hc : c < UInt32.size)
    (h : m + c < UInt32.size) :
    UInt32.ofNat c + UInt32.ofNat m = UInt32.ofNat (m + c) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, ofNat_toNat hc,
    ofNat_toNat (show m < UInt32.size by omega), ofNat_toNat h, hpow]
  omega

/-- Adding the literal one to an index. -/
private theorem index_add_one (m : Nat) (h : m + 1 < UInt32.size) :
    (1 : UInt32) + UInt32.ofNat m = UInt32.ofNat (m + 1) := by
  have hlit : (1 : UInt32) = UInt32.ofNat 1 := rfl
  rw [hlit]
  exact index_add 1 m (by omega) h

/-- Adding the literal two to an index. -/
private theorem index_add_two (m : Nat) (h : m + 2 < UInt32.size) :
    (2 : UInt32) + UInt32.ofNat m = UInt32.ofNat (m + 2) := by
  have hlit : (2 : UInt32) = UInt32.ofNat 2 := rfl
  rw [hlit]
  exact index_add 2 m (by omega) h

private theorem ofNat_lt_iff {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) :
    UInt32.ofNat a < UInt32.ofNat b ↔ a < b := by
  rw [UInt32.lt_iff_toNat_lt, ofNat_toNat ha, ofNat_toNat hb]

private theorem ofNat_le_iff {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) :
    UInt32.ofNat a ≤ UInt32.ofNat b ↔ a ≤ b := by
  rw [UInt32.le_iff_toNat_le, ofNat_toNat ha, ofNat_toNat hb]

private theorem ofNat_eq_iff {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) :
    UInt32.ofNat a = UInt32.ofNat b ↔ a = b := by
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    rw [ofNat_toNat ha, ofNat_toNat hb] at this
    exact this
  · intro h; rw [h]

private theorem ofNat_ne_zero {a : Nat} (h1 : 0 < a)
    (h : a < UInt32.size) : UInt32.ofNat a ≠ 0 := by
  intro hc
  have := congrArg UInt32.toNat hc
  rw [ofNat_toNat h, show (0 : UInt32).toNat = 0 from rfl] at this
  omega

/-- The scan pointer starts at entry two, WAT 2660 to 2663. -/
private theorem addr_two (v : UInt32) :
    (16 : UInt32) + v = v + UInt32.ofNat (8 * 2) :=
  UInt32.add_comm _ _

/-- The scan pointer step, WAT 2673 to 2675. -/
private theorem addr_step (v : UInt32) (n k : Nat) (hk : k + 1 ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (8 : UInt32) + (v + UInt32.ofNat (8 * k))
      = v + UInt32.ofNat (8 * (k + 1)) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have h1 : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have h2 : (v + UInt32.ofNat (8 * (k + 1))).toNat
      = v.toNat + 8 * (k + 1) :=
    Slices.byteOffset_toNat v (8 * (k + 1)) (by omega)
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, h1, h2,
    show ((8 : UInt32)).toNat = 8 from rfl, hpow]
  omega

/-- The entry above entry `k`, reached by the offset eight. -/
private theorem addr_next (v : UInt32) (n k : Nat) (hk : k + 1 ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    v + UInt32.ofNat (8 * k) + 8 = v + UInt32.ofNat (8 * (k + 1)) := by
  rw [← addr_step v n k hk hroom]
  exact UInt32.add_comm _ _

/-- The high address of the first exchange, WAT 2759 to 2765. -/
private theorem rev_addr_hi (v : UInt32) (n i : Nat) (hi : i < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (UInt32.ofNat i ^^^ 4294967295) <<< ((3 : UInt32) % 32) +
        (v + UInt32.ofNat (8 * n))
      = v + UInt32.ofNat (8 * (n - 1 - i)) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow3 : (2 : Nat) ^ 3 = 8 := by norm_num
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hisz : i < UInt32.size := by omega
  have hend : (v + UInt32.ofNat (8 * n)).toNat = v.toNat + 8 * n :=
    Slices.byteOffset_toNat v (8 * n) (by omega)
  have hres : (v + UInt32.ofNat (8 * (n - 1 - i))).toNat
      = v.toNat + 8 * (n - 1 - i) :=
    Slices.byteOffset_toNat v (8 * (n - 1 - i)) (by omega)
  have hxor : (UInt32.ofNat i ^^^ 4294967295).toNat = 4294967295 - i := by
    rw [xor_ones_toNat, ofNat_toNat hisz]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_shiftLeft,
    show ((3 : UInt32) % 32).toNat % 32 = 3 from rfl, Nat.shiftLeft_eq,
    hxor, hend, hres, hpow3, hpow]
  omega

/-- The high address of the second exchange, WAT 2785 to 2791. -/
private theorem rev_addr_hi2 (v : UInt32) (n i : Nat) (hev : 2 ∣ i)
    (hlt : i < 2 ^ 26) (hi : i + 2 ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (UInt32.ofNat i ^^^ 536870910) <<< ((3 : UInt32) % 32) +
        (v + UInt32.ofNat (8 * n))
      = v + UInt32.ofNat (8 * (n - 2 - i)) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow3 : (2 : Nat) ^ 3 = 8 := by norm_num
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hpow26 : (2 : Nat) ^ 26 = 67108864 := by norm_num
  have hend : (v + UInt32.ofNat (8 * n)).toNat = v.toNat + 8 * n :=
    Slices.byteOffset_toNat v (8 * n) (by omega)
  have hres : (v + UInt32.ofNat (8 * (n - 2 - i))).toNat
      = v.toNat + 8 * (n - 2 - i) :=
    Slices.byteOffset_toNat v (8 * (n - 2 - i)) (by omega)
  have hxor := xor_mask_toNat i hev hlt
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_shiftLeft,
    show ((3 : UInt32) % 32).toNat % 32 = 3 from rfl, Nat.shiftLeft_eq,
    hxor, hend, hres, hpow3, hpow]
  omega

/-! ## The regions of the body -/

/-- The registers of the body.  Registers 0 to 2 are the parameters. -/
@[reducible] private def regs (l0 l1 l2 l3 l4 l5 l6 l7 : UInt32)
    (l8 : UInt64) (vs : List Value) : Locals :=
  { params := [.i32 l0, .i32 l1, .i32 l2],
    locals := [.i32 l3, .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i64 l8],
    values := vs }

/-- One step of the ascending scan, WAT 2666 to 2687. -/
@[reducible] private def scanALoop : Program :=
  [.localGet 6, .load32 0, .localTee 7, .localGet 3, .ltU, .br_if 2,
    .localGet 6, .const 8, .add, .localSet 6, .localGet 7, .localSet 3,
    .localGet 1, .localGet 5, .const 1, .add, .localTee 5, .ne,
    .br_if 0, .br 3]

/-- The ascending scan below the first test, WAT 2654 to 2687. -/
@[reducible] private def blockFiveTail : Program :=
  [.const 2, .localSet 5, .localGet 1, .const 2, .eq, .br_if 1,
    .localGet 0, .const 16, .add, .localSet 6, .const 2, .localSet 5,
    .loop 0 0 scanALoop]

/-- The first comparison and the ascending scan, WAT 2645 to 2687. -/
@[reducible] private def blockFive : Program :=
  .localGet 0 :: .load32 8 :: .localTee 3 :: .localGet 0 ::
    .load32 0 :: .ltU :: .localTee 4 :: .br_if 0 :: blockFiveTail

/-- One step of the descending scan, WAT 2701 to 2722. -/
@[reducible] private def scanBLoop : Program :=
  [.localGet 6, .load32 0, .localTee 7, .localGet 3, .geU, .br_if 1,
    .localGet 6, .const 8, .add, .localSet 6, .localGet 7, .localSet 3,
    .localGet 1, .localGet 5, .const 1, .add, .localTee 5, .ne,
    .br_if 0, .br 2]

/-- The descending scan below the first test, WAT 2689 to 2722. -/
@[reducible] private def blockFourTail : Program :=
  [.const 2, .localSet 5, .localGet 1, .const 2, .eq, .br_if 0,
    .localGet 0, .const 16, .add, .localSet 6, .const 2, .localSet 5,
    .loop 0 0 scanBLoop]

/-- The descending scan, WAT 2644 to 2722. -/
@[reducible] private def blockFour : Program :=
  .block 0 0 blockFive :: blockFourTail

/-- The partial-run test, WAT 2724 to 2727. -/
@[reducible] private def scanTest : Program :=
  [.localGet 5, .localGet 1, .ne, .br_if 2]

/-- The two scans and the partial-run test, WAT 2643 to 2727. -/
@[reducible] private def scanBlock : Program :=
  .block 0 0 blockFour :: scanTest

/-- Two exchanges of the reverse, WAT 2758 to 2805. -/
@[reducible] private def revLoop : Program :=
  [.localGet 6, .localGet 5, .const 4294967295, .xor, .const 3, .shl,
    .add, .localTee 1, .load64 0, .localSet 8, .localGet 1, .localGet 0,
    .localGet 5, .const 3, .shl, .add, .localTee 3, .load64 0,
    .store64 0, .localGet 3, .localGet 8, .store64 0, .localGet 3,
    .load64 8, .localSet 8, .localGet 3, .localGet 6, .localGet 5,
    .const 536870910, .xor, .const 3, .shl, .add, .localTee 1,
    .load64 0, .store64 8, .localGet 1, .localGet 8, .store64 0,
    .localGet 5, .const 2, .add, .localTee 5, .localGet 7, .ne,
    .br_if 0]

/-- The odd exchange in the middle, WAT 2810 to 2831. -/
@[reducible] private def middleSwap : Program :=
  [.localGet 0, .localGet 5, .const 3, .shl, .add, .localTee 3,
    .load64 0, .localSet 8, .localGet 3, .localGet 6, .localGet 5,
    .const 4294967295, .xor, .const 3, .shl, .add, .localTee 5,
    .load64 0, .store64 0, .localGet 5, .localGet 8, .store64 0]

/-- The odd-bit test after the unrolled loop, WAT 2806 to 2808. -/
@[reducible] private def revBlockTail : Program :=
  [.localGet 2, .eqz, .br_if 1]

/-- The trip count and the unrolled loop, WAT 2740 to 2808. -/
@[reducible] private def revBlock : Program :=
  .localGet 1 :: .const 1 :: .shrU :: .localTee 3 :: .const 1 ::
    .eq :: .br_if 0 :: .localGet 3 :: .const 1 :: .and ::
    .localSet 2 :: .localGet 3 :: .const 134217726 :: .and ::
    .localSet 7 :: .const 0 :: .localSet 5 :: .loop 0 0 revLoop ::
    revBlockTail

/-- The end pointer, the trip count and the exchanges, WAT 2732 to
2831. -/
@[reducible] private def revSetup : Program :=
  .localGet 0 :: .localGet 1 :: .const 3 :: .shl :: .add ::
    .localSet 6 :: .const 0 :: .localSet 5 :: .block 0 0 revBlock ::
    middleSwap

/-- The reverse of a descending run, WAT 2729 to 2831. -/
@[reducible] private def reverseTail : Program :=
  .localGet 4 :: .eqz :: .br_if 0 :: revSetup

/-- The short exit, the scan and the reverse, WAT 2638 to 2832. -/
@[reducible] private def body2 : Program :=
  .localGet 1 :: .const 2 :: .ltU :: .br_if 0 ::
    .block 0 0 scanBlock :: reverseTail

/-- The block that the explicit return leaves, WAT 2637 to 2833. -/
@[reducible] private def body1 : Program :=
  [.block 0 0 body2, .ret]

/-- The recursion limit and the one call, WAT 2835 to 2847. -/
@[reducible] private def sortTail : Program :=
  [.localGet 0, .localGet 1, .const 0, .localGet 1, .const 1, .or, .clz,
    .const 1, .shl, .const 62, .xor, .localGet 2, .call 24]

set_option maxRecDepth 1048576 in
/-- The generated body is one block and the call. -/
private theorem func11_shape :
    Project.RustHashMap.func11 = .block 0 0 body1 :: sortTail := rfl

private theorem func11_index :
    Project.RustHashMap.«module».funcs[11]? =
      some Project.RustHashMap.func11Def := by rfl

/-! ## The control frames of the two outer blocks -/

/-- The frame of the block that the explicit return leaves. -/
@[reducible] private def frame1 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := body1,
    continuation := sortTail, belowStack := [] }

/-- The frame that the short exit and the ascending run leave. -/
@[reducible] private def frame2 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := body2,
    continuation := [.ret], belowStack := [] }

/-- The frame that a whole monotone run leaves. -/
@[reducible] private def frame3 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := scanBlock, continuation := reverseTail, belowStack := [] }

/-- The frame that a partial run leaves. -/
@[reducible] private def frame4 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := blockFour, continuation := scanTest, belowStack := [] }

/-- The frame that the descending first test leaves. -/
@[reducible] private def frame5 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := blockFive, continuation := blockFourTail,
    belowStack := [] }

/-! ## One entry of the buffer -/

/-- Entry `i` of a list, with no proof that `i` is in range.  Out of
range the model reads the entry `(0, 0)`, exactly as `keyAt` does. -/
private def entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    UInt32 × UInt32 :=
  ps.getD i (0, 0)

private theorem keyAt_entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    keyAt ps i = (entryAt ps i).1 := rfl

private theorem entryAt_eq_getElem (ps : List (UInt32 × UInt32))
    {i : Nat} (hi : i < ps.length) : entryAt ps i = ps[i] :=
  List.getD_eq_getElem _ _ hi

private theorem getElem_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps[i] = entryAt ps i :=
  (entryAt_eq_getElem ps hi).symm

private theorem set_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps.set i (entryAt ps i) = ps := by
  rw [entryAt_eq_getElem ps hi, List.set_getElem_self hi]

private theorem set_pair_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) :
    ps.set i ((entryAt ps i).1, (entryAt ps i).2) = ps :=
  set_entryAt ps hi

/-! ## Address facts of one entry cell -/

/-- Move an owned word between two names of one address. -/
private theorem wordMove32 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 (α := α) 0 address value ⊢
      pointsTo_u32 0 address' value := by
  rw [haddress]

/-- Move an owned double word between two names of one address. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

/-- The four byte addresses of one `i32` cell.  Copy of
`FrameCells.lean:221`, which this module does not import. -/
private theorem offset_facts (base offset : UInt32) (o : Nat)
    (hoffset : UInt32.ofNat o = offset)
    (hbound : base.toNat + o + 4 ≤ UInt32.size) :
    (base + offset).toNat = base.toNat + offset.toNat ∧
      (base + offset + 1).toNat = (base + offset).toNat + 1 ∧
      (base + offset + 2).toNat = (base + offset).toNat + 2 ∧
      (base + offset + 3).toNat = (base + offset).toNat + 3 := by
  subst hoffset
  have ho : o < UInt32.size := by omega
  have hto : (UInt32.ofNat o).toNat = o := UInt32.toNat_ofNat_of_lt' ho
  have h0 : (base + UInt32.ofNat o).toNat = base.toNat + o :=
    Slices.byteOffset_toNat base o (by omega)
  refine ⟨by rw [h0, hto], ?_, ?_, ?_⟩
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)

/-- The eight byte addresses of one `i64` cell.  Copy of
`FrameCells.lean:256`, which this module does not import. -/
private theorem offset_facts64 (base offset : UInt32) (o : Nat)
    (hoffset : UInt32.ofNat o = offset)
    (hbound : base.toNat + o + 8 ≤ UInt32.size) :
    (base + offset).toNat = base.toNat + offset.toNat ∧
      (base + offset + 1).toNat = (base + offset).toNat + 1 ∧
      (base + offset + 2).toNat = (base + offset).toNat + 2 ∧
      (base + offset + 3).toNat = (base + offset).toNat + 3 ∧
      (base + offset + 4).toNat = (base + offset).toNat + 4 ∧
      (base + offset + 5).toNat = (base + offset).toNat + 5 ∧
      (base + offset + 6).toNat = (base + offset).toNat + 6 ∧
      (base + offset + 7).toNat = (base + offset).toNat + 7 := by
  subst hoffset
  have ho : o < UInt32.size := by omega
  have hto : (UInt32.ofNat o).toNat = o := UInt32.toNat_ofNat_of_lt' ho
  have h0 : (base + UInt32.ofNat o).toNat = base.toNat + o :=
    Slices.byteOffset_toNat base o (by omega)
  refine ⟨by rw [h0, hto], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 4 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 5 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 6 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 7 (by omega)

/-- The key cell of entry `k` of a buffer that does not wrap. -/
private theorem cell_facts32 (v : UInt32) (k n : Nat) (hk : k < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * k) + 1).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + 1 ∧
      (v + UInt32.ofNat (8 * k) + 2).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + 2 ∧
      (v + UInt32.ofNat (8 * k) + 3).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + 3 := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have h := offset_facts (v + UInt32.ofNat (8 * k)) 0 0 rfl (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa using h.2.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2

/-- The whole cell of entry `k` of a buffer that does not wrap. -/
private theorem cell_facts64 (v : UInt32) (k n : Nat) (hk : k < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * k) + 0).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + (0 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * k) + 0 + 1).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 1 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 2).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 2 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 3).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 3 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 4).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 4 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 5).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 5 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 6).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 6 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 7).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 7 := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  exact offset_facts64 (v + UInt32.ofNat (8 * k)) 0 0 rfl (by omega)

/-- The whole cell of entry `k + 1`, reached by the offset eight. -/
private theorem next_facts64 (v : UInt32) (k n : Nat) (hk : k + 1 < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * k) + 8).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + (8 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * k) + 8 + 1).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 1 ∧
      (v + UInt32.ofNat (8 * k) + 8 + 2).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 2 ∧
      (v + UInt32.ofNat (8 * k) + 8 + 3).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 3 ∧
      (v + UInt32.ofNat (8 * k) + 8 + 4).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 4 ∧
      (v + UInt32.ofNat (8 * k) + 8 + 5).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 5 ∧
      (v + UInt32.ofNat (8 * k) + 8 + 6).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 6 ∧
      (v + UInt32.ofNat (8 * k) + 8 + 7).toNat
        = (v + UInt32.ofNat (8 * k) + 8).toNat + 7 := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  exact offset_facts64 (v + UInt32.ofNat (8 * k)) 8 8 rfl (by omega)

/-! ## One memory step on one entry -/

set_option maxHeartbeats 2000000 in
/-- `i32.load` of the key of entry `k`. -/
private theorem twp_key_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i32 (entryAt ps k).1 :: values⟩, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load32 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts32 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr (entryAt ps k).1
    hfacts.1 hfacts.2.1 hfacts.2.2 with Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps k).1 Hcell
  isimp only [getElem_entryAt ps hkl, set_pair_self ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i32.load offset=8` of the key of entry one, WAT 2647. -/
private theorem twp_key_read_one [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v : UInt32} {ps : List (UInt32 × UInt32)} {n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : 1 < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i32 (entryAt ps 1).1 :: values⟩, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 v :: values⟩,
          .load32 8 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  have hkl : 1 < ps.length := by omega
  have hfacts := offset_facts v 8 8 rfl (by omega)
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove32 (rfl : v + UInt32.ofNat (8 * 1) = v + 8)
    $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load32
    (address := v) (offset := 8)
    (entryAt ps 1).1 hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2
    with Hcell
  ihave Hcell := wordMove32 (rfl : v + 8 = v + UInt32.ofNat (8 * 1))
    $$ Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps 1).1 Hcell
  isimp only [getElem_entryAt ps hkl, set_pair_self ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.load` of the whole entry `k`. -/
private theorem twp_entry_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (entryAt ps k)) :: values⟩, code,
            arity, remainder, controls, calls⟩ : Expr Universal.State) @
          s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord (entryAt ps k)) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps k) Hcell
  isimp only [set_entryAt ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.store` of a whole entry into slot `k`. -/
private theorem twp_entry_write [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)}
    {q : UInt32 × UInt32} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v (ps.set k q) -∗
        WP (.running ⟨⟨params, localValues, values⟩, code, arity,
            remainder, controls, calls⟩ : Expr Universal.State) @ s; E
          [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i64 (Table.pairWord q) :: .i32 addr :: values⟩,
          .store64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord (entryAt ps k)) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %q Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.load offset=8` of the whole entry `k + 1`, WAT 2782. -/
private theorem twp_entry_read_next [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k + 1 < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (entryAt ps (k + 1))) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load64 8 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k + 1 < ps.length := by omega
  have hnext : v + UInt32.ofNat (8 * k) + 8
      = v + UInt32.ofNat (8 * (k + 1)) := addr_next v n k (by omega) hroom
  have hfacts := next_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 hnext.symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := v + UInt32.ofNat (8 * k)) (offset := 8)
    (Table.pairWord (entryAt ps (k + 1))) hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 hnext $$ Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps (k + 1)) Hcell
  isimp only [set_entryAt ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.store offset=8` into slot `k + 1`, WAT 2794. -/
private theorem twp_entry_write_next
    [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)}
    {q : UInt32 × UInt32} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k + 1 < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v (ps.set (k + 1) q) -∗
        WP (.running ⟨⟨params, localValues, values⟩, code, arity,
            remainder, controls, calls⟩ : Expr Universal.State) @ s; E
          [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i64 (Table.pairWord q) :: .i32 addr :: values⟩,
          .store64 8 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k + 1 < ps.length := by omega
  have hnext : v + UInt32.ofNat (8 * k) + 8
      = v + UInt32.ofNat (8 * (k + 1)) := addr_next v n k (by omega) hroom
  have hfacts := next_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 hnext.symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := v + UInt32.ofNat (8 * k)) (offset := 8)
    (Table.pairWord (entryAt ps (k + 1))) hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 hnext $$ Hcell
  ihave Hbuf := Hclose $$ %q Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

/-! ## Where each stage leaves the machine -/

/-- Where an early return leaves the machine: at the explicit return,
with the output buffer in place. -/
private def retExit [WasmSmallStepGS hlc Universal.State]
    (v : UInt32) (out : List (UInt32 × UInt32))
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ r1 : UInt32, ∀ r2 : UInt32, ∀ r3 : UInt32,
    ∀ r4 : UInt32, ∀ r5 : UInt32, ∀ r6 : UInt32,
    ∀ r7 : UInt32, ∀ r8 : UInt64,
    Table.PairSlice 0 v out -∗
    WP (.running ⟨regs v r1 r2 r3 r4 r5 r6 r7 r8 [], [.ret], arity,
        remainder, controls, calls⟩ : Expr Universal.State) @ s; E
      [{ Φ }])

/-- The machine after the one call, with the sorted buffer back. -/
private def sortExit [WasmSmallStepGS hlc Universal.State]
    (v sp : UInt32) (pairs : List (UInt32 × UInt32)) (depth : Nat)
    (after : Locals) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ out : List (UInt32 × UInt32), ∀ below' : List UInt8,
    RuntimeContext -∗
    StackPointer sp -∗
    StackBelow sp depth below' -∗
    Table.PairSlice 0 v out -∗
    ⌜out.Perm pairs ∧ Table.SortedByKey out⌝ -∗
    WP (.running ⟨after, [], arity, remainder, controls, calls⟩ :
      Expr Universal.State) @ s; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The recursion limit and the one call, WAT 2835 to 2847.  The body
passes the null ancestor and the limit `((len ||| 1).clz <<< 1) ^^^ 62`,
which `SortPures.sortLimit_of_wasm` reads as `SortContracts.sortLimit`.
The whole stack below the caller goes to the call, because the depth of
the call is the depth of this body. -/
private theorem twp_sort_tail [WasmSmallStepGS hlc Universal.State]
    (hfunc21 : Func21Spec (hlc := hlc))
    {sp v len env l3 l4 l5 l6 l7 : UInt32} {l8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {below : List UInt8}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = len.toNat)
    (hnodup : NodupKeys pairs)
    (hlen27 : len.toNat ≤ 2 ^ 27)
    (hroom : v.toNat + 8 * len.toNat < UInt32.size)
    (hdepth : sortDepth len.toNat ≤ sp.toNat) :
    iprop(RuntimeContext ∗ StackPointer sp ∗
      StackBelow sp (sortDepth len.toNat) below ∗
      Table.PairSlice 0 v pairs ∗
      sortExit v sp pairs (sortDepth len.toNat)
        (regs v len env l3 l4 l5 l6 l7 l8 []) arity remainder controls
        calls s E Φ) ⊢
      WP (.running ⟨regs v len env l3 l4 l5 l6 l7 l8 [], sortTail,
          arity, remainder, controls, calls⟩ : Expr Universal.State) @
        s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hlim : (UInt32.ofNat (sortLimit len.toNat)).toNat
      = sortLimit len.toNat := by
    have hne : len.toNat ||| 1 ≠ 0 := by
      intro hzero
      have hbit := Nat.testBit_lor len.toNat 1 0
      simp [hzero] at hbit
    have hlt : len.toNat ||| 1 < 2 ^ 28 := by
      refine Nat.or_lt_two_pow ?_ ?_ <;> omega
    have hlog : Nat.log2 (len.toNat ||| 1) < 28 := (Nat.log2_lt hne).2 hlt
    exact ofNat_toNat (by unfold sortLimit; omega)
  iintro ⟨Hruntime, Hsp, Hbelow, Hbuf, Hexit⟩
  simp only [sortTail, regs]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_localGet
    twp_const twp_or]
  iapply Wasm.SmallStep.twp_clz
  wasm_twp_pures [twp_const twp_shl]
  isimp only [shl_one]
  wasm_twp_pures [twp_const]
  iapply Wasm.SmallStep.twp_xor
  isimp only [sortLimit_of_wasm len hlen27]
  wasm_twp_pures [twp_localGet]
  have Hcall := hfunc21 sp v len (UInt32.ofNat (sortLimit len.toNat))
    env none pairs below
    (callerLocals := regs v len env l3 l4 l5 l6 l7 l8 [])
    (stack := []) (code := []) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hcall
  simp only [ancestorArg, AncestorCell, hlim,
    ← sortDepth_eq_quicksortDepth, List.append_nil] at Hcall
  iapply Hcall
  isplitl_exacts [Hruntime Hsp Hbelow Hbuf]
  · iapply BI.emp_sep.mpr
    isplitl_pureexact (⟨hlen, hlen27, hnodup, by simp [AncestorBelow],
      hroom, hdepth, by simp, by simp [AncestorFits]⟩ :
      pairs.length = len.toNat ∧ len.toNat ≤ 2 ^ 27 ∧
        NodupKeys pairs ∧ AncestorBelow none pairs ∧
        v.toNat + 8 * len.toNat < UInt32.size ∧
        sortDepth len.toNat ≤ sp.toNat ∧
        (∀ p k, (none : Option (UInt32 × UInt32)) = some (p, k) →
          p ≠ 0) ∧
        AncestorFits (none : Option (UInt32 × UInt32)))
    · isimp only [SortPost]
      iintro %out %below' Hr Hs Hb Hp Hemp %hf
      iclear Hemp
      isimp only [ResumeWP, resumeExpr, List.nil_append,
        List.append_nil]
      isimp only [sortExit] at Hexit
      ihave Hgo := Hexit $$ %out %below' Hr Hs Hb Hp %hf
      iexact Hgo

/-! ## The ascending scan -/

set_option maxHeartbeats 2000000 in
/-- The ascending scan, WAT 2666 to 2687.  The loop walks forward while
each key is at least the key below it.  Its invariant is the neighbour
fact of every index below the counter, and the buffer never changes. -/
private theorem twp_asc_loop [WasmSmallStepGS hlc Universal.State]
    {v len env l7 : UInt32} {l8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {n i : Nat} {Rest : HeapIProp}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hi2 : 2 ≤ i) (hin : i < n)
    (hpre : ∀ m, m + 1 < i → keyAt pairs m ≤ keyAt pairs (m + 1))
    (hpartial : ∀ r3 r4 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 r4 r5 r6 r7 r8 [], sortTail,
            arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])
    (hfull : (∀ m, m + 1 < n → keyAt pairs m ≤ keyAt pairs (m + 1)) →
      ∀ r3 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 0 r5 r6 r7 r8 [], reverseTail,
            arity, remainder, frame2 :: frame1 :: controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
      WP (.running ⟨regs v len env (keyAt pairs (i - 1)) 0
            (UInt32.ofNat i) (v + UInt32.ofNat (8 * i)) l7 l8 [],
          [.loop 0 0 scanALoop], arity, remainder,
          frame5 :: frame4 :: frame3 :: frame2 :: frame1 :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hnsz : n < UInt32.size := by omega
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  iintro ⟨Hbuf, HRest⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat × UInt32 × UInt64)
    (measure := fun p => n - p.1)
    (locals := fun p => regs v len env (keyAt pairs (p.1 - 1)) 0
      (UInt32.ofNat p.1) (v + UInt32.ofNat (8 * p.1)) p.2.1 p.2.2 [])
    (I := fun p => iprop(
      ⌜2 ≤ p.1 ∧ p.1 < n ∧
        ∀ m, m + 1 < p.1 → keyAt pairs m ≤ keyAt pairs (m + 1)⌝ ∗
      Table.PairSlice 0 v pairs ∗ Rest))
    (initial := (i, l7, l8))
    (initialLocals := regs v len env (keyAt pairs (i - 1)) 0
      (UInt32.ofNat i) (v + UInt32.ofNat (8 * i)) l7 l8 [])
    rfl rfl
  · intro p
    obtain ⟨j, s7, s8⟩ := p
    iintro Hrec ⟨%hinv, Hbuf, HRest⟩
    obtain ⟨hj2, hjn, hjpre⟩ := hinv
    replace hj2 : 2 ≤ j := hj2
    replace hjn : j < n := hjn
    simp only [Wasm.SmallStep.loopBodyExpr, scanALoop, regs]
    wasm_twp_pures [twp_localGet]
    iapply twp_key_read (k := j) (n := n) (by omega) hlen hroom rfl
    isplitl_exact Hbuf
    · iintro Hbuf
      isimp only [← keyAt_entryAt]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      by_cases hdrop : keyAt pairs j < keyAt pairs (j - 1)
      · -- WAT 2672: the run stops here, so the sort tail runs
        iapply Wasm.SmallStep.twp_ltU (result := 1) (by rw [if_pos hdrop])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [frame4, List.take, List.append_nil, scanTest]
        wasm_twp_pures [twp_localGet twp_localGet]
        iapply Wasm.SmallStep.twp_ne (result := 1)
          (by
            rw [if_pos (by
              rw [hlenv]
              exact fun hc =>
                absurd ((ofNat_eq_iff (by omega) hnsz).mp hc) (by omega))])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [frame1, List.take, List.append_nil]
        iapply (hpartial (keyAt pairs (j - 1)) 0 (UInt32.ofNat j)
          (v + UInt32.ofNat (8 * j)) (keyAt pairs j) s8)
        isplitl_exact Hbuf
        iexact HRest
      · -- WAT 2673 to 2686: the run goes on
        have hstep : keyAt pairs (j - 1) ≤ keyAt pairs j :=
          UInt32.le_of_not_lt hdrop
        have hnew : ∀ m, m + 1 < j + 1 →
            keyAt pairs m ≤ keyAt pairs (m + 1) := by
          intro m hm
          by_cases hlast : m + 1 = j
          · have hm1 : m = j - 1 := by omega
            rw [hm1, show j - 1 + 1 = j from by omega]
            exact hstep
          · exact hjpre m (by omega)
        iapply Wasm.SmallStep.twp_ltU (result := 0)
          (by rw [if_neg hdrop])
        iapply Wasm.SmallStep.twp_brIfZero
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [addr_step v n j (by omega) hroom]
        wasm_twp_pures [twp_localSet]
        simp only [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_localSet]
        simp only [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
        isimp only [index_add_one j (by omega)]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        by_cases hend : j + 1 = n
        · -- WAT 2686: the whole run ascends
          iapply Wasm.SmallStep.twp_ne (result := 0)
            (by rw [if_neg (by rw [hlenv, hend]; exact fun hc => hc rfl)])
          iapply Wasm.SmallStep.twp_brIfZero
          iapply Wasm.SmallStep.twp_br rfl
          simp only [frame3, List.take, List.append_nil]
          iapply (hfull (by rw [← hend]; exact hnew) (keyAt pairs j)
            (UInt32.ofNat (j + 1)) (v + UInt32.ofNat (8 * (j + 1)))
            (keyAt pairs j) s8)
          isplitl_exact Hbuf
          iexact HRest
        · -- WAT 2685: one more entry
          iapply Wasm.SmallStep.twp_ne (result := 1)
            (by
              rw [if_pos (by
                rw [hlenv]
                exact fun hc =>
                  absurd ((ofNat_eq_iff hnsz (by omega)).mp hc)
                    (by omega))])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
            rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          ihave Hgo := Hrec
            $$ %((j + 1, keyAt pairs j, s8) : Nat × UInt32 × UInt64)
            %(show n - (j + 1) < n - j by omega)
          simp only [Nat.add_sub_cancel]
          iapply Hgo
          isplitl_pureexact (⟨by omega, by omega, hnew⟩ :
            2 ≤ j + 1 ∧ j + 1 < n ∧
              ∀ m, m + 1 < j + 1 →
                keyAt pairs m ≤ keyAt pairs (m + 1))
          · iframe Hbuf HRest
  · isplitl_pureexact (⟨hi2, hin, hpre⟩ :
      2 ≤ i ∧ i < n ∧
        ∀ m, m + 1 < i → keyAt pairs m ≤ keyAt pairs (m + 1))
    · iframe Hbuf HRest

/-! ## The descending scan -/

set_option maxHeartbeats 2000000 in
/-- The descending scan, WAT 2701 to 2722.  The exit test is `i32.ge_u`,
so the loop goes on only while the next key is below the key above it. -/
private theorem twp_desc_loop [WasmSmallStepGS hlc Universal.State]
    {v len env l7 : UInt32} {l8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {n i : Nat} {Rest : HeapIProp}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hi2 : 2 ≤ i) (hin : i < n)
    (hpre : ∀ m, m + 1 < i → keyAt pairs (m + 1) < keyAt pairs m)
    (hpartial : ∀ r3 r4 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 r4 r5 r6 r7 r8 [], sortTail,
            arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])
    (hfull : (∀ m, m + 1 < n → keyAt pairs (m + 1) < keyAt pairs m) →
      ∀ r3 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 1 r5 r6 r7 r8 [], reverseTail,
            arity, remainder, frame2 :: frame1 :: controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
      WP (.running ⟨regs v len env (keyAt pairs (i - 1)) 1
            (UInt32.ofNat i) (v + UInt32.ofNat (8 * i)) l7 l8 [],
          [.loop 0 0 scanBLoop], arity, remainder,
          frame4 :: frame3 :: frame2 :: frame1 :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hnsz : n < UInt32.size := by omega
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  iintro ⟨Hbuf, HRest⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat × UInt32 × UInt64)
    (measure := fun p => n - p.1)
    (locals := fun p => regs v len env (keyAt pairs (p.1 - 1)) 1
      (UInt32.ofNat p.1) (v + UInt32.ofNat (8 * p.1)) p.2.1 p.2.2 [])
    (I := fun p => iprop(
      ⌜2 ≤ p.1 ∧ p.1 < n ∧
        ∀ m, m + 1 < p.1 → keyAt pairs (m + 1) < keyAt pairs m⌝ ∗
      Table.PairSlice 0 v pairs ∗ Rest))
    (initial := (i, l7, l8))
    (initialLocals := regs v len env (keyAt pairs (i - 1)) 1
      (UInt32.ofNat i) (v + UInt32.ofNat (8 * i)) l7 l8 [])
    rfl rfl
  · intro p
    obtain ⟨j, s7, s8⟩ := p
    iintro Hrec ⟨%hinv, Hbuf, HRest⟩
    obtain ⟨hj2, hjn, hjpre⟩ := hinv
    replace hj2 : 2 ≤ j := hj2
    replace hjn : j < n := hjn
    simp only [Wasm.SmallStep.loopBodyExpr, scanBLoop, regs]
    wasm_twp_pures [twp_localGet]
    iapply twp_key_read (k := j) (n := n) (by omega) hlen hroom rfl
    isplitl_exact Hbuf
    · iintro Hbuf
      isimp only [← keyAt_entryAt]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      by_cases hrise : keyAt pairs (j - 1) ≤ keyAt pairs j
      · -- WAT 2707: the run stops here, so the sort tail runs
        iapply Wasm.SmallStep.twp_geU (result := 1) (by rw [if_pos hrise])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [frame4, List.take, List.append_nil, scanTest]
        wasm_twp_pures [twp_localGet twp_localGet]
        iapply Wasm.SmallStep.twp_ne (result := 1)
          (by
            rw [if_pos (by
              rw [hlenv]
              exact fun hc =>
                absurd ((ofNat_eq_iff (by omega) hnsz).mp hc) (by omega))])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [frame1, List.take, List.append_nil]
        iapply (hpartial (keyAt pairs (j - 1)) 1 (UInt32.ofNat j)
          (v + UInt32.ofNat (8 * j)) (keyAt pairs j) s8)
        isplitl_exact Hbuf
        iexact HRest
      · -- WAT 2708 to 2721: the run goes on
        have hstep : keyAt pairs j < keyAt pairs (j - 1) :=
          UInt32.not_le.mp hrise
        have hnew : ∀ m, m + 1 < j + 1 →
            keyAt pairs (m + 1) < keyAt pairs m := by
          intro m hm
          by_cases hlast : m + 1 = j
          · have hm1 : m = j - 1 := by omega
            rw [hm1, show j - 1 + 1 = j from by omega]
            exact hstep
          · exact hjpre m (by omega)
        iapply Wasm.SmallStep.twp_geU (result := 0)
          (by rw [if_neg hrise])
        iapply Wasm.SmallStep.twp_brIfZero
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [addr_step v n j (by omega) hroom]
        wasm_twp_pures [twp_localSet]
        simp only [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_localSet]
        simp only [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
        isimp only [index_add_one j (by omega)]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        by_cases hend : j + 1 = n
        · -- WAT 2721: the whole run descends
          iapply Wasm.SmallStep.twp_ne (result := 0)
            (by rw [if_neg (by rw [hlenv, hend]; exact fun hc => hc rfl)])
          iapply Wasm.SmallStep.twp_brIfZero
          iapply Wasm.SmallStep.twp_br rfl
          simp only [frame3, List.take, List.append_nil]
          iapply (hfull (by rw [← hend]; exact hnew) (keyAt pairs j)
            (UInt32.ofNat (j + 1)) (v + UInt32.ofNat (8 * (j + 1)))
            (keyAt pairs j) s8)
          isplitl_exact Hbuf
          iexact HRest
        · -- WAT 2720: one more entry
          iapply Wasm.SmallStep.twp_ne (result := 1)
            (by
              rw [if_pos (by
                rw [hlenv]
                exact fun hc =>
                  absurd ((ofNat_eq_iff hnsz (by omega)).mp hc)
                    (by omega))])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
            rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          ihave Hgo := Hrec
            $$ %((j + 1, keyAt pairs j, s8) : Nat × UInt32 × UInt64)
            %(show n - (j + 1) < n - j by omega)
          simp only [Nat.add_sub_cancel]
          iapply Hgo
          isplitl_pureexact (⟨by omega, by omega, hnew⟩ :
            2 ≤ j + 1 ∧ j + 1 < n ∧
              ∀ m, m + 1 < j + 1 →
                keyAt pairs (m + 1) < keyAt pairs m)
          · iframe Hbuf HRest
  · isplitl_pureexact (⟨hi2, hin, hpre⟩ :
      2 ≤ i ∧ i < n ∧
        ∀ m, m + 1 < i → keyAt pairs (m + 1) < keyAt pairs m)
    · iframe Hbuf HRest

/-! ## The odd exchange in the middle -/

/-- An exchange does not depend on the order of its two indices. -/
private theorem swapAt_comm (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    Table.swapAt ps i j = Table.swapAt ps j i := by
  apply List.ext_getElem?
  intro k
  by_cases hki : k = i
  · subst hki
    rw [Table.swapAt_getElem?_left ps hi hj]
    by_cases hkj : k = j
    · subst hkj
      rw [Table.swapAt_getElem?_left ps hj hi]
    · rw [Table.swapAt_getElem?_right ps hj hi]
  · by_cases hkj : k = j
    · subst hkj
      rw [Table.swapAt_getElem?_right ps hi hj,
        Table.swapAt_getElem?_left ps hj hi]
    · rw [Table.swapAt_getElem?_other ps hki hkj,
        Table.swapAt_getElem?_other ps hkj hki]

set_option maxHeartbeats 2000000 in
/-- The odd exchange in the middle, WAT 2810 to 2831.  The body reaches
it with the counter in register five and the address one past the buffer
in register six. -/
private theorem twp_middle [WasmSmallStepGS hlc Universal.State]
    {v w1 w2 w3 w4 w7 : UInt32} {w8 : UInt64}
    {cur : List (UInt32 × UInt32)} {n k : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : cur.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hk : k < n) :
    iprop(Table.PairSlice 0 v cur ∗
      (∀ q1 : UInt32, ∀ q2 : UInt32, ∀ q3 : UInt32, ∀ q4 : UInt32,
        ∀ q5 : UInt32, ∀ q6 : UInt32, ∀ q7 : UInt32, ∀ q8 : UInt64,
        Table.PairSlice 0 v (Table.swapAt cur k (n - 1 - k)) -∗
        WP (.running ⟨regs v q1 q2 q3 q4 q5 q6 q7 q8 [], [], arity,
            remainder, controls, calls⟩ : Expr Universal.State) @ s; E
          [{ Φ }])) ⊢
      WP (.running ⟨regs v w1 w2 w3 w4 (UInt32.ofNat k)
            (v + UInt32.ofNat (8 * n)) w7 w8 [], middleSwap, arity,
          remainder, controls, calls⟩ : Expr Universal.State) @ s; E
        [{ Φ }] := by
  have hhi : n - 1 - k < n := by omega
  have hklen : k < cur.length := by omega
  have hhilen : n - 1 - k < cur.length := by omega
  have hlen1 : (cur.set k (entryAt cur (n - 1 - k))).length = n := by
    rw [List.length_set]
    exact hlen
  iintro ⟨Hbuf, Hcont⟩
  simp only [middleSwap, regs]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
  isimp only [index_addr v k n (by omega) hroom]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_entry_read (k := k) (n := n) hk hlen hroom rfl
  isplitl_exact Hbuf
  · iintro Hbuf
    wasm_twp_pures [twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const]
    iapply Wasm.SmallStep.twp_xor
    wasm_twp_pures [twp_const twp_shl twp_add]
    isimp only [rev_addr_hi v n k hk hroom]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_entry_read (k := n - 1 - k) (n := n) hhi hlen hroom rfl
    isplitl_exact Hbuf
    · iintro Hbuf
      iapply twp_entry_write (k := k) (n := n) (q := entryAt cur (n - 1 - k))
        hk hlen hroom rfl
      isplitl_exact Hbuf
      · iintro Hbuf
        wasm_twp_pures [twp_localGet twp_localGet]
        iapply twp_entry_write (k := n - 1 - k) (n := n)
          (ps := cur.set k (entryAt cur (n - 1 - k)))
          (q := entryAt cur k) hhi hlen1 hroom rfl
        isplitl_exact Hbuf
        · iintro Hbuf
          have hmodel : (cur.set k (entryAt cur (n - 1 - k))).set
                (n - 1 - k) (entryAt cur k)
              = Table.swapAt cur k (n - 1 - k) := by
            rw [Table.swapAt_eq_set_set cur hklen hhilen,
              getElem_entryAt cur hklen, getElem_entryAt cur hhilen]
          isimp only [hmodel] at Hbuf
          ihave Hgo := Hcont $$ %w1 %w2
            %(v + UInt32.ofNat (8 * k)) %w4
            %(v + UInt32.ofNat (8 * (n - 1 - k)))
            %(v + UInt32.ofNat (8 * n)) %w7
            %(Table.pairWord (entryAt cur k)) Hbuf
          iexact Hgo

/-! ## The unrolled reverse loop -/

set_option maxHeartbeats 2000000 in
/-- Two exchanges of the reverse, WAT 2758 to 2805.  The counter counts
the exchanges, the buffer holds `SortPures.reverseFold pairs` of that
counter, and one trip adds two exchanges. -/
private theorem twp_rev_loop [WasmSmallStepGS hlc Universal.State]
    {v w1 odd w3 flag : UInt32} {w8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {n trips i : Nat}
    {after : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hn27 : n ≤ 2 ^ 27)
    (htrips : 2 * trips ≤ n) (hteven : 2 ∣ trips)
    (hi : i < trips) (hieven : 2 ∣ i) :
    iprop(Table.PairSlice 0 v (reverseFold pairs i) ∗
      (∀ q1 : UInt32, ∀ q3 : UInt32, ∀ q8 : UInt64,
        Table.PairSlice 0 v (reverseFold pairs trips) -∗
        WP (.running ⟨regs v q1 odd q3 flag (UInt32.ofNat trips)
              (v + UInt32.ofNat (8 * n)) (UInt32.ofNat trips) q8 [],
            after, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨regs v w1 odd w3 flag (UInt32.ofNat i)
            (v + UInt32.ofNat (8 * n)) (UInt32.ofNat trips) w8 [],
          .loop 0 0 revLoop :: after, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hp26 : (2 : Nat) ^ 26 = 67108864 := by norm_num
  have hp27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  iintro ⟨Hbuf, Hexit⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat × UInt32 × UInt32 × UInt64)
    (measure := fun p => trips - p.1)
    (locals := fun p => regs v p.2.1 odd p.2.2.1 flag
      (UInt32.ofNat p.1) (v + UInt32.ofNat (8 * n))
      (UInt32.ofNat trips) p.2.2.2 [])
    (I := fun p => iprop(
      ⌜p.1 < trips ∧ 2 ∣ p.1⌝ ∗
      Table.PairSlice 0 v (reverseFold pairs p.1) ∗
      (∀ q1 : UInt32, ∀ q3 : UInt32, ∀ q8 : UInt64,
        Table.PairSlice 0 v (reverseFold pairs trips) -∗
        WP (.running ⟨regs v q1 odd q3 flag (UInt32.ofNat trips)
              (v + UInt32.ofNat (8 * n)) (UInt32.ofNat trips) q8 [],
            after, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])))
    (initial := (i, w1, w3, w8))
    (initialLocals := regs v w1 odd w3 flag (UInt32.ofNat i)
      (v + UInt32.ofNat (8 * n)) (UInt32.ofNat trips) w8 [])
    rfl rfl
  · intro p
    obtain ⟨j, t1, t3, t8⟩ := p
    iintro Hrec ⟨%hinv, Hbuf, Hexit⟩
    obtain ⟨hjt, hjeven⟩ := hinv
    replace hjt : j < trips := hjt
    replace hjeven : 2 ∣ j := hjeven
    have hj2 : j + 2 ≤ trips := by omega
    have hroomj : 2 * j + 4 ≤ n := by omega
    have hj26 : j < 2 ^ 26 := by omega
    have hjn : j < n := by omega
    have hj1n : j + 1 < n := by omega
    have hhi : n - 1 - j < n := by omega
    have hhi2 : n - 2 - j < n := by omega
    have hcur : (reverseFold pairs j).length = n := by
      rw [reverseFold_length]; exact hlen
    have hcur1 : (reverseFold pairs (j + 1)).length = n := by
      rw [reverseFold_length]; exact hlen
    have hjl : j < (reverseFold pairs j).length := by omega
    have hhil : n - 1 - j < (reverseFold pairs j).length := by omega
    have hj1l : j + 1 < (reverseFold pairs (j + 1)).length := by omega
    have hhi2l : n - 2 - j < (reverseFold pairs (j + 1)).length := by
      omega
    have hsetA : ((reverseFold pairs j).set (n - 1 - j)
          (entryAt (reverseFold pairs j) j)).length = n := by
      rw [List.length_set]; exact hcur
    have hsetB : ((reverseFold pairs (j + 1)).set (j + 1)
          (entryAt (reverseFold pairs (j + 1)) (n - 2 - j))).length
        = n := by
      rw [List.length_set]; exact hcur1
    have hsucc1 : reverseFold pairs (j + 1)
        = Table.swapAt (reverseFold pairs j) j (n - 1 - j) := by
      have h := reverseFold_succ pairs j
      rw [hlen] at h
      exact h
    have hsucc2 : reverseFold pairs (j + 2)
        = Table.swapAt (reverseFold pairs (j + 1)) (j + 1)
          (n - 2 - j) := by
      have h := reverseFold_succ pairs (j + 1)
      rw [hlen, show n - 1 - (j + 1) = n - 2 - j from by omega,
        show j + 1 + 1 = j + 2 from by omega] at h
      exact h
    have hstepA : ((reverseFold pairs j).set (n - 1 - j)
          (entryAt (reverseFold pairs j) j)).set j
          (entryAt (reverseFold pairs j) (n - 1 - j))
        = reverseFold pairs (j + 1) := by
      rw [hsucc1, swapAt_comm (reverseFold pairs j) hjl hhil,
        Table.swapAt_eq_set_set (reverseFold pairs j) hhil hjl,
        getElem_entryAt _ hjl, getElem_entryAt _ hhil]
    have hstepB : ((reverseFold pairs (j + 1)).set (j + 1)
          (entryAt (reverseFold pairs (j + 1)) (n - 2 - j))).set
          (n - 2 - j) (entryAt (reverseFold pairs (j + 1)) (j + 1))
        = reverseFold pairs (j + 2) := by
      rw [hsucc2,
        Table.swapAt_eq_set_set (reverseFold pairs (j + 1)) hj1l hhi2l,
        getElem_entryAt _ hj1l, getElem_entryAt _ hhi2l]
    simp only [Wasm.SmallStep.loopBodyExpr, revLoop, regs]
    wasm_twp_pures [twp_localGet twp_localGet twp_const]
    iapply Wasm.SmallStep.twp_xor
    wasm_twp_pures [twp_const twp_shl twp_add]
    isimp only [rev_addr_hi v n j hjn hroom]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_entry_read (k := n - 1 - j) (n := n) hhi hcur hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_pures [twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
      twp_shl twp_add]
    isimp only [index_addr v j n (by omega) hroom]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_entry_read (k := j) (n := n) hjn hcur hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    iapply twp_entry_write (k := n - 1 - j) (n := n)
      (q := entryAt (reverseFold pairs j) j) hhi hcur hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_entry_write (k := j) (n := n)
      (q := entryAt (reverseFold pairs j) (n - 1 - j)) hjn hsetA hroom
      rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hstepA] at Hbuf
    wasm_twp_pures [twp_localGet]
    iapply twp_entry_read_next (k := j) (n := n) hj1n hcur1 hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_pures [twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const]
    iapply Wasm.SmallStep.twp_xor
    wasm_twp_pures [twp_const twp_shl twp_add]
    isimp only [rev_addr_hi2 v n j hjeven hj26 (by omega) hroom]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_entry_read (k := n - 2 - j) (n := n) hhi2 hcur1 hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    iapply twp_entry_write_next (k := j) (n := n)
      (q := entryAt (reverseFold pairs (j + 1)) (n - 2 - j)) hj1n hcur1
      hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_entry_write (k := n - 2 - j) (n := n)
      (q := entryAt (reverseFold pairs (j + 1)) (j + 1)) hhi2 hsetB
      hroom rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hstepB] at Hbuf
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [index_add_two j (by omega)]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    by_cases hdone : j + 2 = trips
    · -- WAT 2803: the trip count is reached
      iapply Wasm.SmallStep.twp_ne (result := 0)
        (by rw [if_neg (by simp [hdone])])
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      isimp only [hdone] at Hbuf
      isimp only [hdone]
      ihave Hgo := Hexit $$ %(v + UInt32.ofNat (8 * (n - 2 - j)))
        %(v + UInt32.ofNat (8 * j))
        %(Table.pairWord (entryAt (reverseFold pairs (j + 1)) (j + 1)))
        Hbuf
      iexact Hgo
    · -- WAT 2804: one more trip
      iapply Wasm.SmallStep.twp_ne (result := 1)
        (by
          rw [if_pos (fun hc => absurd
            ((ofNat_eq_iff (by omega) (by omega)).mp hc) (by omega))])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hgo := Hrec
        $$ %((j + 2, v + UInt32.ofNat (8 * (n - 2 - j)),
            v + UInt32.ofNat (8 * j),
            Table.pairWord (entryAt (reverseFold pairs (j + 1))
              (j + 1))) : Nat × UInt32 × UInt32 × UInt64)
        %(show trips - (j + 2) < trips - j by omega)
      iapply Hgo
      isplitl_pureexact (⟨by omega, by omega⟩ :
        j + 2 < trips ∧ 2 ∣ (j + 2))
      · iframe Hbuf Hexit
  · isplitl_pureexact (⟨hi, hieven⟩ : i < trips ∧ 2 ∣ i)
    · iframe Hbuf Hexit

/-! ## The whole reverse -/

/-- The odd bit of the half length, WAT 2748 to 2751. -/
private theorem half_and_one (m : Nat) (h : m < UInt32.size) :
    UInt32.ofNat m &&& 1 = UInt32.ofNat (m % 2) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, ofNat_toNat h,
    show ((1 : UInt32)).toNat = 1 from rfl, Nat.and_one_is_mod,
    ofNat_toNat (by omega)]

/-- The even part of the half length, WAT 2752 to 2755. -/
private theorem half_and_mask (m : Nat) (h : m < 2 ^ 27) :
    UInt32.ofNat m &&& 134217726 = UInt32.ofNat (2 * (m / 2)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hp26 : (2 : Nat) ^ 26 = 67108864 := by norm_num
  have hp27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have hhalf : m / 2 < 2 ^ 26 := by omega
  have hnat : m &&& 134217726 = 2 * (m / 2) := by
    conv_lhs => rw [show m = 2 * (m / 2) + m % 2 from by omega]
    rw [show (134217726 : Nat) = 2 * (2 ^ 26 - 1) from by omega,
      two_mul_and (m / 2) (2 ^ 26 - 1) (m % 2) (by omega),
      Nat.and_two_pow_sub_one_of_lt_two_pow hhalf]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, ofNat_toNat (by omega),
    show ((134217726 : UInt32)).toNat = 134217726 from rfl, hnat,
    ofNat_toNat (by omega)]

set_option maxHeartbeats 2000000 in
/-- The reverse of a descending run, WAT 2732 to 2831.  The loop is
unrolled by two, so the compiled body makes one more exchange in the
middle when the half length is odd.  Both forms end with
`SortPures.reverseFold pairs (pairs.length / 2)`, which
`SortPures.reverseFold_half` reads as `List.reverse`. -/
private theorem twp_reverse [WasmSmallStepGS hlc Universal.State]
    {v len r2 r3 flag r5 r6 r7 : UInt32} {r8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {n : Nat}
    {arity : Nat} {remainder : List Value}
    {ctl : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (h2n : 2 ≤ n) (hn27 : n ≤ 2 ^ 27) :
    iprop(Table.PairSlice 0 v pairs ∗
      retExit v pairs.reverse arity remainder ctl calls s E Φ) ⊢
      WP (.running ⟨regs v len r2 r3 flag r5 r6 r7 r8 [], revSetup,
          arity, remainder, frame2 :: ctl, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hp27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have hnsz : n < UInt32.size := by omega
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  have hhalf : reverseFold pairs (n / 2) = pairs.reverse := by
    rw [← hlen]; exact reverseFold_half pairs
  have hend : len <<< ((3 : UInt32) % 32) + v
      = v + UInt32.ofNat (8 * n) := by
    rw [hlenv]
    exact index_addr v n n (Nat.le_refl n) hroom
  iintro ⟨Hbuf, Hexit⟩
  simp only [revSetup, regs]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
  isimp only [hend]
  wasm_twp_pures [twp_localSet]
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_block]
  simp only [revBlock,
    List.drop_zero]
  wasm_twp_pures [twp_localGet twp_const twp_shrU]
  isimp only [shr_one, shift_right_one len, hn]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  by_cases hone : n / 2 = 1
  · -- WAT 2747: the buffer holds two or three entries
    iapply Wasm.SmallStep.twp_eq (result := 1)
      (by
        rw [if_pos (by
          rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl]
          exact (ofNat_eq_iff (by omega) (by omega)).mpr hone)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take, List.append_nil]
    iapply twp_middle (k := 0) (n := n) hlen hroom (by omega)
    isplitl_exact Hbuf
    iintro %q1 %q2 %q3 %q4 %q5 %q6 %q7 %q8 Hbuf
    have hmid : Table.swapAt pairs 0 (n - 1 - 0) = pairs.reverse := by
      have h := reverseFold_succ pairs 0
      rw [hlen, reverseFold_zero] at h
      rw [← h, show (0 : Nat) + 1 = n / 2 from by omega, hhalf]
    isimp only [hmid] at Hbuf
    wasm_twp_pures [twp_exitControl]
    simp only [List.take, List.append_nil]
    isimp only [retExit] at Hexit
    ihave Hgo := Hexit $$ %q1 %q2 %q3 %q4 %q5 %q6 %q7 %q8 Hbuf
    iexact Hgo
  · -- WAT 2748 to 2808: the unrolled loop runs at least once
    have hhalf2 : 2 ≤ n / 2 := by omega
    have htrips : 2 * (2 * (n / 2 / 2)) ≤ n := by omega
    iapply Wasm.SmallStep.twp_eq (result := 0)
      (by
        rw [if_neg (by
          rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl]
          exact fun hc =>
            hone ((ofNat_eq_iff (by omega) (by omega)).mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_const twp_and]
    isimp only [half_and_one (n / 2) (by omega)]
    wasm_twp_pures [twp_localSet]
    simp only [List.set]
    wasm_twp_pures [twp_localGet twp_const twp_and]
    isimp only [half_and_mask (n / 2) (by omega)]
    wasm_twp_pures [twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_rev_loop (n := n) (trips := 2 * (n / 2 / 2)) (i := 0)
      hlen hroom hn27 htrips ⟨n / 2 / 2, rfl⟩ (by omega) ⟨0, rfl⟩
    isimp only [reverseFold_zero]
    isplitl_exact Hbuf
    iintro %q1 %q3 %q8 Hbuf
    simp only [revBlockTail]
    wasm_twp_pures [twp_localGet]
    by_cases hodd : n / 2 % 2 = 0
    · -- WAT 2808: the half length is even, so the loop did every swap
      iapply Wasm.SmallStep.twp_eqz (result := 1)
        (by
          rw [if_pos (by
            rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl]
            exact (ofNat_eq_iff (by omega) (by omega)).mpr hodd)])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take, List.append_nil]
      isimp only [show 2 * (n / 2 / 2) = n / 2 from by omega, hhalf]
        at Hbuf
      isimp only [retExit] at Hexit
      ihave Hgo := Hexit $$ %q1 %(UInt32.ofNat (n / 2 % 2)) %q3 %flag
        %(UInt32.ofNat (2 * (n / 2 / 2)))
        %(v + UInt32.ofNat (8 * n))
        %(UInt32.ofNat (2 * (n / 2 / 2))) %q8 Hbuf
      iexact Hgo
    · -- WAT 2810 to 2831: one exchange is left in the middle
      have htail : 2 * (n / 2 / 2) + 1 = n / 2 := by omega
      have hcurT : (reverseFold pairs (2 * (n / 2 / 2))).length = n := by
        rw [reverseFold_length pairs (2 * (n / 2 / 2))]
        exact hlen
      iapply Wasm.SmallStep.twp_eqz (result := 0)
        (by
          rw [if_neg (by
            rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl]
            exact fun hc =>
              hodd ((ofNat_eq_iff (by omega) (by omega)).mp hc))])
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_exitControl]
      simp only [List.take, List.append_nil]
      iapply twp_middle (k := 2 * (n / 2 / 2)) (n := n) hcurT hroom
        (by omega)
      isplitl_exact Hbuf
      iintro %p1 %p2 %p3 %p4 %p5 %p6 %p7 %p8 Hbuf
      have hmid : Table.swapAt (reverseFold pairs (2 * (n / 2 / 2)))
            (2 * (n / 2 / 2)) (n - 1 - 2 * (n / 2 / 2))
          = pairs.reverse := by
        have h := reverseFold_succ pairs (2 * (n / 2 / 2))
        rw [hlen] at h
        rw [← h, htail, hhalf]
      isimp only [hmid] at Hbuf
      wasm_twp_pures [twp_exitControl]
      simp only [List.take, List.append_nil]
      isimp only [retExit] at Hexit
      ihave Hgo := Hexit $$ %p1 %p2 %p3 %p4 %p5 %p6 %p7 %p8 Hbuf
      iexact Hgo

/-! ## The length test above each scan -/

set_option maxHeartbeats 2000000 in
/-- The length test and the ascending scan, WAT 2654 to 2687.  Two
entries need no scan, because the first test already ordered them. -/
private theorem twp_scan_asc [WasmSmallStepGS hlc Universal.State]
    {v len env w5 w6 w7 : UInt32} {w8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {n : Nat} {Rest : HeapIProp}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size) (h2n : 2 ≤ n)
    (hfirst : keyAt pairs 0 ≤ keyAt pairs 1)
    (hpartial : ∀ r3 r4 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 r4 r5 r6 r7 r8 [], sortTail,
            arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])
    (hfull : (∀ m, m + 1 < n → keyAt pairs m ≤ keyAt pairs (m + 1)) →
      ∀ r3 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 0 r5 r6 r7 r8 [], reverseTail,
            arity, remainder, frame2 :: frame1 :: controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
      WP (.running ⟨regs v len env (keyAt pairs 1) 0 w5 w6 w7 w8 [],
          blockFiveTail, arity, remainder,
          frame5 :: frame4 :: frame3 :: frame2 :: frame1 :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hnsz : n < UInt32.size := by
    have hlt := UInt32.toNat_lt len
    omega
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  iintro ⟨Hbuf, HRest⟩
  simp only [blockFiveTail, regs]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases htwo : n = 2
  · -- WAT 2659: the buffer holds two entries
    iapply Wasm.SmallStep.twp_eq (result := 1)
      (by rw [if_pos (by rw [hlenv, htwo]; rfl)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take, List.append_nil, scanTest]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply Wasm.SmallStep.twp_ne (result := 0)
      (by rw [if_neg (by rw [hlenv, htwo]; exact fun hc => hc rfl)])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_exitControl]
    simp only [List.take, List.append_nil]
    iapply (hfull
      (by
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        exact hfirst) (keyAt pairs 1) 2 w6 w7 w8)
    isplitl_exact Hbuf
    iexact HRest
  · -- WAT 2660 to 2687: the scan runs
    iapply Wasm.SmallStep.twp_eq (result := 0)
      (by
        rw [if_neg (by
          rw [hlenv, show (2 : UInt32) = UInt32.ofNat 2 from rfl]
          exact fun hc => htwo ((ofNat_eq_iff hnsz (by omega)).mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [addr_two v]
    wasm_twp_pures [twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_asc_loop (i := 2) (n := n) hlen hn hroom (Nat.le_refl 2)
      (by omega)
      (by
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        exact hfirst) hpartial hfull
    isplitl_exact Hbuf
    iexact HRest

set_option maxHeartbeats 2000000 in
/-- The length test and the descending scan, WAT 2689 to 2722. -/
private theorem twp_scan_desc [WasmSmallStepGS hlc Universal.State]
    {v len env w5 w6 w7 : UInt32} {w8 : UInt64}
    {pairs : List (UInt32 × UInt32)} {n : Nat} {Rest : HeapIProp}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size) (h2n : 2 ≤ n)
    (hfirst : keyAt pairs 1 < keyAt pairs 0)
    (hpartial : ∀ r3 r4 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 r4 r5 r6 r7 r8 [], sortTail,
            arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])
    (hfull : (∀ m, m + 1 < n → keyAt pairs (m + 1) < keyAt pairs m) →
      ∀ r3 r5 r6 r7 : UInt32, ∀ r8 : UInt64,
      iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
        WP (.running ⟨regs v len env r3 1 r5 r6 r7 r8 [], reverseTail,
            arity, remainder, frame2 :: frame1 :: controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v pairs ∗ Rest) ⊢
      WP (.running ⟨regs v len env (keyAt pairs 1) 1 w5 w6 w7 w8 [],
          blockFourTail, arity, remainder,
          frame4 :: frame3 :: frame2 :: frame1 :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hnsz : n < UInt32.size := by
    have hlt := UInt32.toNat_lt len
    omega
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  iintro ⟨Hbuf, HRest⟩
  simp only [blockFourTail, regs]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases htwo : n = 2
  · -- WAT 2694: the buffer holds two entries
    iapply Wasm.SmallStep.twp_eq (result := 1)
      (by rw [if_pos (by rw [hlenv, htwo]; rfl)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take, List.append_nil, scanTest]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply Wasm.SmallStep.twp_ne (result := 0)
      (by rw [if_neg (by rw [hlenv, htwo]; exact fun hc => hc rfl)])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_exitControl]
    simp only [List.take, List.append_nil]
    iapply (hfull
      (by
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        exact hfirst) (keyAt pairs 1) 2 w6 w7 w8)
    isplitl_exact Hbuf
    iexact HRest
  · -- WAT 2695 to 2722: the scan runs
    iapply Wasm.SmallStep.twp_eq (result := 0)
      (by
        rw [if_neg (by
          rw [hlenv, show (2 : UInt32) = UInt32.ofNat 2 from rfl]
          exact fun hc => htwo ((ofNat_eq_iff hnsz (by omega)).mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [addr_two v]
    wasm_twp_pures [twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_localSet]
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_desc_loop (i := 2) (n := n) hlen hn hroom (Nat.le_refl 2)
      (by omega)
      (by
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        exact hfirst) hpartial hfull
    isplitl_exact Hbuf
    iexact HRest

/-! ## The body -/

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- Absolute `func 14` puts the entries in key order.  It moves the
entries only.  The one call that the body makes is `quicksort`, so the
proof rests on `SortContracts.Func21Spec`. -/
theorem func11_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc21 : Func21Spec (hlc := hlc)) : Func11Spec (hlc := hlc) := by
  unfold Func11Spec CallContract callExpr
  intro sp v len env pairs below callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hbuf, %hpure, Hcont⟩
  obtain ⟨hplen, hnodup, hlen27, hroom, hdepth⟩ := hpure
  have hs : UInt32.size = 4294967296 := rfl
  have hnsz : len.toNat < UInt32.size := UInt32.toNat_lt len
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module»
      14 Project.RustHashMap.func11Def (by decide) func11_index
    with Hmodule
  simp only [Project.RustHashMap.func11Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, ValueType.zero, func11_shape,
    Nat.reduceAdd]
  iclose_map_runtime Hruntime with Hmodule Henv
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases hsmall : len.toNat < 2
  · -- WAT 2642: one entry or none is already in key order
    iapply Wasm.SmallStep.twp_ltU (result := 1)
      (by rw [if_pos (UInt32.lt_iff_toNat_lt.mpr hsmall)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take, List.append_nil]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallExplicit
      with Hmodule
    simp only [List.take, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    isimp only [SortPost] at Hcont
    ihave Hwand := Hcont $$ %pairs %below Hruntime Hsp Hbelow Hbuf
    ihave Hwand := emp_wand_elim $$ Hwand
    ihave Hgo := Hwand
      $$ %(⟨List.Perm.refl pairs,
          sortedByKey_of_ascending pairs
            (fun i hi => absurd hi (by omega))⟩ :
        pairs.Perm pairs ∧ Table.SortedByKey pairs)
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
    iexact Hgo
  · -- WAT 2643 to 2847: the scan, the reverse and the sort tail
    iapply Wasm.SmallStep.twp_ltU (result := 0)
      (by rw [if_neg (fun hc => hsmall (UInt32.lt_iff_toNat_lt.mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_localGet]
    iapply twp_key_read_one (n := len.toNat) (by omega) hplen hroom
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [← keyAt_entryAt]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    iapply twp_key_read (k := 0) (n := len.toNat) (by omega) hplen hroom
      (UInt32.add_zero v).symm
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [← keyAt_entryAt]
    by_cases hdesc : keyAt pairs 1 < keyAt pairs 0
    · -- WAT 2653: the first two entries descend
      iapply Wasm.SmallStep.twp_ltU (result := 1)
        (by rw [if_pos hdesc])
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take, List.append_nil]
      iapply twp_scan_desc (n := len.toNat)
        (Rest := iprop(RuntimeContext ∗ StackPointer sp ∗
          StackBelow sp (sortDepth len.toNat) below ∗
          SortPost v pairs sp (sortDepth len.toNat) iprop(emp)
            callerLocals stack code arity remainder controls calls s E
            Φ))
        hplen rfl hroom (by omega) hdesc
        (by
          intro r3 r4 r5 r6 r7 r8
          iintro ⟨Hp, Hr, Hs, Hb, Hc⟩
          iapply twp_sort_tail hfunc21 hplen hnodup hlen27 hroom hdepth
          isplitl_exacts [Hr Hs Hb Hp]
          isimp only [sortExit]
          iintro %out %below' Hr Hs Hb Hp %hf
          iopen_map_runtime Hr with ⟨Hmod, Hev⟩
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
            with Hmod
          simp only [List.take, List.nil_append]
          iclose_map_runtime Hr with Hmod Hev
          isimp only [SortPost] at Hc
          ihave Hwand := Hc $$ %out %below' Hr Hs Hb Hp
          ihave Hwand := emp_wand_elim $$ Hwand
          ihave Hgo := Hwand $$ %hf
          isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
          iexact Hgo)
        (by
          intro hfact r3 r5 r6 r7 r8
          iintro ⟨Hp, Hr, Hs, Hb, Hc⟩
          simp only [reverseTail, regs]
          wasm_twp_pures [twp_localGet]
          iapply Wasm.SmallStep.twp_eqz (result := 0)
            (by rw [if_neg (by decide)])
          iapply Wasm.SmallStep.twp_brIfZero
          iapply twp_reverse (n := len.toNat) hplen rfl hroom (by omega)
            hlen27
          isplitl_exact Hp
          isimp only [retExit]
          iintro %q1 %q2 %q3 %q4 %q5 %q6 %q7 %q8 Hp
          iopen_map_runtime Hr with ⟨Hmod, Hev⟩
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallExplicit
            with Hmod
          simp only [List.take, List.nil_append]
          iclose_map_runtime Hr with Hmod Hev
          isimp only [SortPost] at Hc
          ihave Hwand := Hc $$ %pairs.reverse %below Hr Hs Hb Hp
          ihave Hwand := emp_wand_elim $$ Hwand
          ihave Hgo := Hwand
            $$ %(⟨List.reverse_perm pairs,
                sortedByKey_reverse_of_scan pairs
                  (fun i hi => hfact i (by omega))⟩ :
              pairs.reverse.Perm pairs ∧
                Table.SortedByKey pairs.reverse)
          isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
          iexact Hgo)
      isplitl_exact Hbuf
      iframe Hruntime Hsp Hbelow Hcont
    · -- WAT 2654: the first two entries do not descend
      iapply Wasm.SmallStep.twp_ltU (result := 0)
        (by rw [if_neg hdesc])
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply Wasm.SmallStep.twp_brIfZero
      iapply twp_scan_asc (n := len.toNat)
        (Rest := iprop(RuntimeContext ∗ StackPointer sp ∗
          StackBelow sp (sortDepth len.toNat) below ∗
          SortPost v pairs sp (sortDepth len.toNat) iprop(emp)
            callerLocals stack code arity remainder controls calls s E
            Φ))
        hplen rfl hroom (by omega) (UInt32.le_of_not_lt hdesc)
        (by
          intro r3 r4 r5 r6 r7 r8
          iintro ⟨Hp, Hr, Hs, Hb, Hc⟩
          iapply twp_sort_tail hfunc21 hplen hnodup hlen27 hroom hdepth
          isplitl_exacts [Hr Hs Hb Hp]
          isimp only [sortExit]
          iintro %out %below' Hr Hs Hb Hp %hf
          iopen_map_runtime Hr with ⟨Hmod, Hev⟩
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
            with Hmod
          simp only [List.take, List.nil_append]
          iclose_map_runtime Hr with Hmod Hev
          isimp only [SortPost] at Hc
          ihave Hwand := Hc $$ %out %below' Hr Hs Hb Hp
          ihave Hwand := emp_wand_elim $$ Hwand
          ihave Hgo := Hwand $$ %hf
          isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
          iexact Hgo)
        (by
          intro hfact r3 r5 r6 r7 r8
          iintro ⟨Hp, Hr, Hs, Hb, Hc⟩
          simp only [reverseTail, regs]
          wasm_twp_pures [twp_localGet]
          iapply Wasm.SmallStep.twp_eqz (result := 1)
            (by rw [if_pos rfl])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
            rfl
          simp only [List.take, List.append_nil]
          iopen_map_runtime Hr with ⟨Hmod, Hev⟩
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallExplicit
            with Hmod
          simp only [List.take, List.nil_append]
          iclose_map_runtime Hr with Hmod Hev
          isimp only [SortPost] at Hc
          ihave Hwand := Hc $$ %pairs %below Hr Hs Hb Hp
          ihave Hwand := emp_wand_elim $$ Hwand
          ihave Hgo := Hwand
            $$ %(⟨List.Perm.refl pairs,
                sortedByKey_of_ascending pairs
                  (fun i hi => hfact i (by omega))⟩ :
              pairs.Perm pairs ∧ Table.SortedByKey pairs)
          isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
          iexact Hgo)
      isplitl_exact Hbuf
      iframe Hruntime Hsp Hbelow Hcont

end Project.RustHashMap.Func11Proof
