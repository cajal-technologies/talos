import CodeLib.RustStd.HashMap.ProbeWasm

/-!
# The full-byte mask and the order of the resize walk

`Table.resize` moves every full bucket of the old table into a fresh one.  It
folds over `Table.fullIndices`, which is the ascending list of the buckets
whose control byte is full.

The compiled `reserve_rehash_inner`, absolute `func 17` at WAT lines 3783 to
4082, does not have that list.  It walks the old control bytes one group of
eight at a time, and inside a group it takes the lowest set byte first,
through `i32.ctz` and the `m & (m - 1)` step.  This file shows that the two
orders agree.

## The mask the code computes

The group mask at WAT line 3783 is `~load64(ctrl) & REP80`.  `Swar.lean`
names `x &&& REP80` as the special bytes, and it has no name for the
complement.  `swarMatchFull` below is that name, and
`hasBit_swarMatchFull` is the byte-level reading of it.  `isFull` is the
negation of `isSpecial`, so the two masks are complementary.

## Where these belong

`swarMatchFull` and its three lemmas belong beside
`swarMatchEmptyOrDeleted` in `Swar.lean`.  They sit here to keep that
file's import surface small.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.RustStd.HashMap

section Full

/-- `match_full`, the complement of `match_empty_or_deleted`.  The compiled
code writes it as `~group & REP80` at WAT line 3783. -/
def swarMatchFull (x : UInt64) : UInt64 := ~~~x &&& REP80

theorem hasBit_not (a : UInt64) {j : Nat} (hj : j < 8) :
    hasBit (~~~a) j = !hasBit a j := by
  rw [not_eq_xor_neg_one]
  unfold hasBit
  rw [UInt64.toNat_xor, Nat.testBit_xor]
  have h : (18446744073709551615 : UInt64).toNat.testBit (8 * j + 7) = true := by
    interval_cases j <;> decide
  rw [h]
  cases a.toNat.testBit (8 * j + 7) <;> rfl

theorem isFull_eq_not_isSpecial (c : UInt8) : isFull c = !isSpecial c := by
  unfold isFull isSpecial
  simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le]
  have h : (0x80 : UInt8).toNat = 128 := by decide
  rw [h]
  cases Nat.lt_or_ge c.toNat 128 with
  | inl hlt => simp [hlt, Nat.not_le.mpr hlt]
  | inr hge => simp [Nat.not_lt.mpr hge, hge]

theorem hasBit_swarMatchFull {g : List UInt8} (hg : g.length = 8) {j : Nat}
    (hj : j < 8) :
    hasBit (swarMatchFull (groupWord g)) j = isFull (g.getD j EMPTY) := by
  unfold swarMatchFull
  rw [hasBit_and, hasBit_REP80 hj, Bool.and_true, hasBit_not _ hj,
    hasBit_groupWord hg hj, testBit_seven_eq (UInt8.toNat_lt _),
    isFull_eq_not_isSpecial]
  unfold isSpecial
  simp only [UInt8.le_iff_toNat_le]
  rfl

/-- The mask invariant that `lowestSetByte_eq_ctz` and `setBytes_iterNext`
both ask for. -/
theorem swarMatchFull_and_REP80 (x : UInt64) :
    swarMatchFull x &&& REP80 = swarMatchFull x := by
  unfold swarMatchFull
  exact and_REP80_and_REP80 _

end Full

section Walk

variable {K V : Type}

theorem length_groupAt (t : Table K V) (pos : Nat) : (groupAt t pos).length = 8 := by
  simp [groupAt]

theorem getD_groupAt (t : Table K V) (pos : Nat) {j : Nat} (hj : j < 8) :
    (groupAt t pos).getD j EMPTY = t.ctrlAt (pos + j) := by
  simp [groupAt, List.getD_eq_getElem?_getD, hj]

/-- The bytes that the group mask reports are exactly the full buckets of
that group, in ascending order. -/
theorem setBytes_swarMatchFull (t : Table K V) (pos : Nat) :
    setBytes (swarMatchFull (groupWord (groupAt t pos))) =
      (List.range 8).filter (fun j => isFull (t.ctrlAt (pos + j))) := by
  unfold setBytes
  apply List.filter_congr
  intro j hj
  have hj8 : j < 8 := by simpa using hj
  rw [hasBit_swarMatchFull (length_groupAt t pos) hj8, getD_groupAt t pos hj8]

/-- One group of the walk, as a slice of the ascending bucket range. -/
theorem map_setBytes_swarMatchFull (t : Table K V) (b : Nat) :
    (setBytes (swarMatchFull (groupWord (groupAt t (8 * b))))).map
        (fun j => 8 * b + j) =
      ((List.range 8).map (fun j => 8 * b + j)).filter
        (fun i => isFull (t.ctrlAt i)) := by
  rw [setBytes_swarMatchFull]
  generalize List.range 8 = l
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : isFull (t.ctrlAt (8 * b + x)) <;> simp [h, ih]

/-- The ascending bucket range of a table whose bucket count is a multiple of
eight, cut into the groups that the walk loads. -/
theorem range_tile (n : Nat) :
    List.range (8 * n) =
      (List.range n).flatMap (fun b => (List.range 8).map (fun j => 8 * b + j)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    rw [Nat.mul_succ, List.range_add, ih, hr, List.flatMap_append]
    simp

/-- The walk of `reserve_rehash_inner` visits exactly `Table.fullIndices`, in
the same ascending order that `Table.resize` folds over.

The loop loads group `b` at control offset `8 * b`, and inside the group it
takes the lowest set byte of the mask first.  `setBytes` is ascending, so the
concatenation over ascending groups is the ascending list of full buckets.
The model and the compiled loop therefore move the same buckets in the same
order, and `Table.resize` needs no reordering lemma. -/
theorem walk_eq_fullIndices (t : Table K V) {n : Nat} (hbuckets : t.buckets = 8 * n) :
    (List.range n).flatMap (fun b =>
        (setBytes (swarMatchFull (groupWord (groupAt t (8 * b))))).map
          (fun j => 8 * b + j)) = fullIndices t := by
  unfold fullIndices
  rw [hbuckets, range_tile n, List.filter_flatMap]
  apply List.flatMap_congr
  intro b _
  exact map_setBytes_swarMatchFull t b

end Walk

end Wasm.RustStd.HashMap.Table
