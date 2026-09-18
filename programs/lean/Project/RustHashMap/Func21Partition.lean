import Project.RustHashMap.Func21Defs
import Project.RustHashMap.SortPures

/-!
# The strict partition of `quicksort`

Absolute `func 24` is `quicksort`, local `func21`.  WAT lines 5977 to
6151 of `programs/rust/build/rust_hash_map/program.wat` hold the strict
partition, which is the partition that runs in every live case.  This
module proves `twp_strict_partition`, the one stage lemma of that
region.  The fragment names come from `Func21Defs`.

## What the region computes

The region is `partition_lomuto_branchless_cyclic` of the Rust core
sort, with the pivot moved to slot 0 first.

WAT 5977 to 5989 exchange slot 0 and the pivot slot.  WAT 5990 to 6001
set up the scan: local 9 is the base of the tail `buf + 8`, local 10 is
the pivot key, local 12 holds the entry of the first tail slot, and
local 7, the count of keys below the pivot, is zero.

The partition then runs over the tail, which is `len - 1` entries long.
One slot of the tail holds a stale copy, which the model calls the gap.
The gap starts at tail slot 0 and the true entry of the gap slot sits in
local 12.  One turn reads the entry at the cursor, writes it into the
gap slot, moves the gap on by one when the key is below the pivot key,
and writes the new gap entry back to the cursor slot.  The last store of
a turn is deferred: the head of each loop body pays it.

WAT 6132 to 6143 pay the last deferred store and write local 12 into the
gap slot.  WAT 6144 to 6149 make the split index `local 7 + (pivot key >
held key)`.  WAT 6150 and 6151 test the split index against the length,
which the last two instructions of the region leave on the stack; the
test is always false, so the continuation starts with the zero flag.

## The register map of the two scans

| Register | Meaning |
| --- | --- |
| 0 | the buffer, never written here |
| 1 | the length, never written here |
| 6 | the pivot offset, then the pivot address, then the cursor |
| 7 | the count of keys below the pivot key, which is the gap |
| 8 | the address of the slot whose store is deferred |
| 9 | the base of the tail, `buf + 8` |
| 10 | the pivot key |
| 11 | the key at the cursor, then the second cursor address |
| 12 | the entry that the gap slot owes, as one `i64` |
| 13 | the end address `buf + 8 * len` |
| 14 | the last address `buf + 8 * len - 8` |
| 15 | the key of the second cursor, then the held key |

Both loops run the same turn.  They are not a forward scan and a
backward scan: the first loop is the turn unrolled twice and the second
loop is the turn once, which runs the entries that the first loop left.

WAT 6004 to 6021 enter the first loop when `buf + 16 < buf + 8 * len -
8`, which is `3 <= len - 1`, and otherwise set local 8 to the base and
leave the block.  The first loop runs the turns of the cursors `r` and
`r + 1` and goes on while `r + 2 < len - 2`, so it stops with a cursor
of `len - 2` or `len - 1`.  WAT 6091 to 6094 skip the second loop when
the cursor is the end.  The second loop runs one turn and goes on while
the cursor is not the end.
-/

namespace Project.RustHashMap.Func21Partition

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortContracts
open Project.RustHashMap.Func21Defs
open scoped Wasm.SmallStep.Outcome

set_option maxRecDepth 40000

/-! ## The pure model of the cyclic partition

The model works on the tail of the buffer, which is the entry list
without the pivot.  `A` is the buffer, `g` the gap slot, `r` the cursor
and `hv` the entry that the gap slot owes.  `orig` is the input.
-/

/-- The entry of `ps` at `i`.  Outside the list it is `(0, 0)`. -/
def entryAt (ps : List (UInt32 × UInt32)) (i : Nat) : UInt32 × UInt32 :=
  ps.getD i (0, 0)

/-- The key of the entry at `i`. -/
def keyAt (ps : List (UInt32 × UInt32)) (i : Nat) : UInt32 :=
  (entryAt ps i).1

theorem entryAt_eq_getElem (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : entryAt ps i = ps[i] :=
  List.getD_eq_getElem _ _ hi

theorem entryAt_set_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) (q : UInt32 × UInt32) :
    entryAt (ps.set i q) i = q := by
  have hi' : i < (ps.set i q).length := by rw [List.length_set]; exact hi
  rw [entryAt_eq_getElem _ hi', List.getElem_set_self]

theorem entryAt_set_ne (ps : List (UInt32 × UInt32)) {i j : Nat}
    (h : i ≠ j) (q : UInt32 × UInt32) :
    entryAt (ps.set i q) j = entryAt ps j := by
  rw [entryAt, entryAt, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem set_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps.set i (entryAt ps i) = ps := by
  rw [entryAt_eq_getElem ps hi, List.set_getElem_self hi]

/-- The first entry, and the list without it. -/
theorem cons_drop_one (ps : List (UInt32 × UInt32))
    (h : 0 < ps.length) : ps = entryAt ps 0 :: ps.drop 1 := by
  rcases ps with _ | ⟨a, t⟩
  · simp at h
  · rfl

/-- The first entry of the tail is the second entry. -/
theorem entryAt_drop_one (ps : List (UInt32 × UInt32)) :
    entryAt (ps.drop 1) 0 = entryAt ps 1 := by
  rcases ps with _ | ⟨a, t⟩
  · rfl
  · rfl

/-- Move the entry of slot `j` to slot `i` and write `y` at `j`.  The
list keeps its content, because slot `i` held a copy of slot `j`. -/
theorem perm_set_set (A : List (UInt32 × UInt32)) {i j : Nat}
    (hij : i ≠ j) (hi : i < A.length) (hj : j < A.length)
    (y : UInt32 × UInt32) :
    ((A.set i (entryAt A j)).set j y).Perm (A.set i y) := by
  rw [List.perm_iff_count]
  intro e
  have hj' : j < (A.set i (entryAt A j)).length := by
    rw [List.length_set]; exact hj
  rw [List.count_set hj', List.count_set hi, List.count_set hi]
  have hget : (A.set i (entryAt A j))[j]'hj' = A[j] := by
    rw [List.getElem_set_ne hij]
  rw [hget, entryAt_eq_getElem A hj]
  have hle : (if A[i] == e then 1 else 0) ≤ A.count e := by
    split_ifs with h
    · exact List.count_pos_iff.mpr ((beq_iff_eq.mp h) ▸ List.getElem_mem hi)
    · exact Nat.zero_le _
  have hle2 : (if A[j] == e then 1 else 0) ≤ A.count e := by
    split_ifs with h
    · exact List.count_pos_iff.mpr ((beq_iff_eq.mp h) ▸ List.getElem_mem hj)
    · exact Nat.zero_le _
  omega

/-- The gap after the turn that reads slot `r`. -/
def gapNext (pk : UInt32) (A : List (UInt32 × UInt32)) (g r : Nat) :
    Nat := g + (if keyAt A r < pk then 1 else 0)

/-- One turn of the cyclic partition.  The entry at the cursor goes into
the gap slot, the gap moves on by the comparison, and the entry of the
new gap slot goes to the cursor slot. -/
def partStep (pk : UInt32) (A : List (UInt32 × UInt32)) (g r : Nat) :
    List (UInt32 × UInt32) :=
  (A.set g (entryAt A r)).set r
    (entryAt (A.set g (entryAt A r)) (gapNext pk A g r))

/-- The store that the head of a loop body owes: slot `r - 1` takes the
entry of the gap slot. -/
def settle (B : List (UInt32 × UInt32)) (g r : Nat) :
    List (UInt32 × UInt32) := B.set (r - 1) (entryAt B g)

theorem partStep_length (pk : UInt32) (A : List (UInt32 × UInt32))
    (g r : Nat) : (partStep pk A g r).length = A.length := by
  rw [partStep, List.length_set, List.length_set]

theorem gapNext_le (pk : UInt32) (A : List (UInt32 × UInt32))
    (g r : Nat) : gapNext pk A g r ≤ g + 1 := by
  rw [gapNext]; split_ifs <;> omega

theorem le_gapNext (pk : UInt32) (A : List (UInt32 × UInt32))
    (g r : Nat) : g ≤ gapNext pk A g r := by
  rw [gapNext]; split_ifs <;> omega

/-- A turn leaves nothing to settle: the store that the next head owes
writes the entry that is already there. -/
theorem settle_partStep (pk : UInt32) (A : List (UInt32 × UInt32))
    (g r : Nat) (hgr : g < r) (hr : r < A.length) :
    settle (partStep pk A g r) (gapNext pk A g r) (r + 1) =
      partStep pk A g r := by
  have hg : g < A.length := by omega
  set A1 := A.set g (entryAt A r) with hA1
  have hlen1 : A1.length = A.length := by rw [hA1, List.length_set]
  set g' := gapNext pk A g r with hg'
  have hrsub : r + 1 - 1 = r := by omega
  rw [settle, hrsub, partStep, ← hA1, ← hg']
  by_cases hcase : g' = r
  · rw [hcase, entryAt_set_self A1 (by omega) _, List.set_set]
  · rw [entryAt_set_ne A1 (Ne.symm hcase) _, List.set_set]

/-- The state of the partition after the turns of the slots below the
cursor `r`. -/
structure PartInv (pk : UInt32) (orig : List (UInt32 × UInt32))
    (hv : UInt32 × UInt32) (A : List (UInt32 × UInt32)) (g r : Nat) :
    Prop where
  length : A.length = orig.length
  gapLt : g < r
  cursor : r ≤ orig.length
  perm : (A.set g hv).Perm orig
  lows : ∀ i, i < g → keyAt A i < pk
  highs : ∀ i, g < i → i < r → pk ≤ keyAt A i
  tail : ∀ i, r ≤ i → entryAt A i = entryAt orig i

/-- The state at the head of the first scan. -/
theorem PartInv_start (pk : UInt32) (orig : List (UInt32 × UInt32))
    (h1 : 1 ≤ orig.length) :
    PartInv pk orig (entryAt orig 0) orig 0 1 := by
  refine ⟨rfl, by omega, by omega, ?_, by omega, by omega, fun i _ => rfl⟩
  rw [set_entryAt orig (by omega)]

set_option maxHeartbeats 1000000 in
/-- One turn keeps the state of the partition. -/
theorem PartInv_step {pk : UInt32} {orig : List (UInt32 × UInt32)}
    {hv : UInt32 × UInt32} {A : List (UInt32 × UInt32)} {g r : Nat}
    (h : PartInv pk orig hv A g r) (hr : r < orig.length) :
    PartInv pk orig hv (partStep pk A g r) (gapNext pk A g r)
      (r + 1) := by
  have hlenA : A.length = orig.length := h.length
  have hgr : g < r := h.gapLt
  have hrA : r < A.length := by omega
  have hgA : g < A.length := by omega
  set x := entryAt A r with hx
  set A1 := A.set g x with hA1
  have hlen1 : A1.length = A.length := by rw [hA1, List.length_set]
  set g' := gapNext pk A g r with hg'
  have hg'lo : g ≤ g' := by rw [hg', gapNext]; split_ifs <;> omega
  have hg'hi : g' ≤ g + 1 := by rw [hg', gapNext]; split_ifs <;> omega
  have hA2 : partStep pk A g r = A1.set r (entryAt A1 g') := by
    rw [partStep, ← hx, ← hA1, ← hg']
  have hlen2 : (partStep pk A g r).length = A.length := by
    rw [hA2, List.length_set, hlen1]
  have hentry1 : ∀ i, i ≠ g → entryAt A1 i = entryAt A i := by
    intro i hi
    exact entryAt_set_ne A (fun hc => hi hc.symm) x
  have hentry1g : entryAt A1 g = x := entryAt_set_self A hgA x
  have hentry2 : ∀ i, i ≠ r →
      entryAt (partStep pk A g r) i = entryAt A1 i := by
    intro i hi
    rw [hA2]
    exact entryAt_set_ne A1 (fun hc => hi hc.symm) _
  have hentry2r : entryAt (partStep pk A g r) r = entryAt A1 g' := by
    rw [hA2]
    exact entryAt_set_self A1 (by omega) _
  refine ⟨by rw [hlen2, hlenA], by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have hgoal : (partStep pk A g r).set g' hv =
        (A1.set r (entryAt A1 g')).set g' hv := by rw [hA2]
    rw [hgoal]
    by_cases hf : g' = g
    · have hzero : entryAt A1 g' = x := by rw [hf]; exact hentry1g
      rw [hzero, hf]
      have hself : A1.set r x = A1 := by
        have hxr : entryAt A1 r = x := by rw [hentry1 r (by omega), hx]
        rw [← hxr]
        exact set_entryAt A1 (by omega)
      rw [hself, hA1, List.set_set]
      exact h.perm
    · have hf1 : g' = g + 1 := by omega
      have hstep2 : (A1.set r hv).Perm (A.set g hv) := by
        rw [hA1, hx]
        exact perm_set_set A (by omega) hgA hrA hv
      by_cases hrg : g' = r
      · rw [hrg, List.set_set]
        exact hstep2.trans h.perm
      · have hrne : r ≠ g' := fun hc => hrg hc.symm
        have hrlen : r < A1.length := by omega
        have hg'len : g' < A1.length := by omega
        have hstep1 :
            ((A1.set r (entryAt A1 g')).set g' hv).Perm (A1.set r hv) :=
          perm_set_set A1 hrne hrlen hg'len hv
        exact hstep1.trans (hstep2.trans h.perm)
  · intro i hi
    have hir : i ≠ r := by omega
    rw [keyAt, hentry2 i hir]
    by_cases hig : i = g
    · have hf1 : g' = g + 1 := by omega
      have hlt : keyAt A r < pk := by
        by_contra hc
        rw [hg', gapNext, if_neg hc] at hf1
        omega
      rw [hig, hentry1g, hx, ← keyAt]
      exact hlt
    · rw [hentry1 i hig, ← keyAt]
      exact h.lows i (by omega)
  · intro i hi hir
    by_cases hcase : i = r
    · rw [keyAt, hcase, hentry2r]
      by_cases hf : g' = g
      · have hge : ¬ keyAt A r < pk := by
          by_contra hc
          rw [hg', gapNext, if_pos hc] at hf
          omega
        rw [hf, hentry1g, hx, ← keyAt]
        exact UInt32.le_of_not_lt hge
      · have hf1 : g' = g + 1 := by omega
        rw [hentry1 g' (by omega), ← keyAt]
        exact h.highs g' (by omega) (by omega)
    · rw [keyAt, hentry2 i hcase, hentry1 i (by omega), ← keyAt]
      exact h.highs i (by omega) (by omega)
  · intro i hi
    rw [hentry2 i (by omega), hentry1 i (by omega)]
    exact h.tail i (by omega)

/-- Nothing is owed at the head of the first scan. -/
theorem settle_start (B : List (UInt32 × UInt32))
    (h : 0 < B.length) : settle B 0 1 = B := by
  rw [settle]
  exact set_entryAt B h

/-- The pivot of the exchange is the first entry of the result. -/
theorem entryAt_swap_head (ps : List (UInt32 × UInt32)) {i : Nat}
    (h0 : 0 < ps.length) (hi : i < ps.length) :
    entryAt ((ps.set 0 (entryAt ps i)).set i (entryAt ps 0)) 0
      = entryAt ps i := by
  by_cases hz : i = 0
  · subst hz
    rw [List.set_set, set_entryAt ps h0]
  · rw [entryAt_set_ne _ hz, entryAt_set_self ps h0]

/-- The split index that the write back computes. -/
def splitIndex (pk : UInt32) (hv : UInt32 × UInt32) (g : Nat) : Nat :=
  g + (if hv.1 < pk then 1 else 0)

section Final

variable {pk : UInt32} {orig : List (UInt32 × UInt32)}
variable {hv : UInt32 × UInt32} {A : List (UInt32 × UInt32)} {g n : Nat}

theorem splitIndex_le (h : PartInv pk orig hv A g n)
    (hn : n = orig.length) : splitIndex pk hv g ≤ orig.length := by
  have h1 := h.gapLt
  have h2 := h.cursor
  rw [splitIndex]
  split_ifs <;> omega

theorem PartInv_low (h : PartInv pk orig hv A g n)
    (hn : n = orig.length) (i : Nat) (hi : i < splitIndex pk hv g) :
    keyAt (A.set g hv) i < pk := by
  have hlen : A.length = orig.length := h.length
  by_cases hig : i = g
  · have hflag : hv.1 < pk := by
      by_contra hc
      rw [splitIndex, if_neg hc] at hi
      omega
    rw [keyAt, hig, entryAt_set_self A (by
      have h1 := h.gapLt; have h2 := h.cursor; omega) hv]
    exact hflag
  · rw [keyAt, entryAt_set_ne A (fun hc => hig hc.symm) hv, ← keyAt]
    refine h.lows i ?_
    rw [splitIndex] at hi
    split_ifs at hi <;> omega

theorem PartInv_high (h : PartInv pk orig hv A g n)
    (hn : n = orig.length) (i : Nat) (hi : splitIndex pk hv g ≤ i)
    (hin : i < orig.length) : pk ≤ keyAt (A.set g hv) i := by
  have hlen : A.length = orig.length := h.length
  by_cases hig : i = g
  · have hflag : ¬ hv.1 < pk := by
      by_contra hc
      rw [splitIndex, if_pos hc] at hi
      omega
    rw [keyAt, hig, entryAt_set_self A (by
      have h1 := h.gapLt; have h2 := h.cursor; omega) hv]
    exact UInt32.le_of_not_lt hflag
  · rw [keyAt, entryAt_set_ne A (fun hc => hig hc.symm) hv, ← keyAt]
    refine h.highs i ?_ (by omega)
    rw [splitIndex] at hi
    split_ifs at hi <;> omega

/-- Every entry below the split index has a key below the pivot key. -/
theorem PartInv_take (h : PartInv pk orig hv A g n)
    (hn : n = orig.length) :
    ∀ x ∈ (A.set g hv).take (splitIndex pk hv g), x.1 < pk := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i hi
  have hik : i < splitIndex pk hv g :=
    Nat.lt_of_lt_of_le hi (List.length_take_le _ _)
  have hlen : A.length = orig.length := h.length
  have hset : (A.set g hv).length = A.length := List.length_set
  have hiA : i < (A.set g hv).length := by
    rw [List.length_take] at hi
    omega
  have hkey := PartInv_low h hn i hik
  rw [keyAt, entryAt_eq_getElem _ hiA] at hkey
  rw [List.getElem_take]
  exact hkey

/-- Every entry from the split index on has a key at the pivot key or
above it. -/
theorem PartInv_drop (h : PartInv pk orig hv A g n)
    (hn : n = orig.length) :
    ∀ y ∈ (A.set g hv).drop (splitIndex pk hv g), pk ≤ y.1 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i hi
  rw [List.length_drop, List.length_set] at hi
  have hlen : A.length = orig.length := h.length
  have hiA : splitIndex pk hv g + i < (A.set g hv).length := by
    rw [List.length_set]
    omega
  have hkey := PartInv_high h hn (splitIndex pk hv g + i) (by omega)
    (by omega)
  rw [keyAt, entryAt_eq_getElem _ hiA] at hkey
  rw [List.getElem_drop]
  exact hkey

end Final

/-! ## Word and address arithmetic

The lemmas below are copies.  `Func22Proof` and `Func11Proof` state
them privately, so this module cannot import them.
-/

private theorem ofNat_toNat {k : Nat} (h : k < UInt32.size) :
    (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' h

/-- `i32.shl` by three, as the model writes it. -/
private theorem shl_three (x : UInt32) :
    x <<< ((3 : UInt32) % 32) = x <<< 3 := rfl

/-- A shift by three of a small index is a multiplication by eight. -/
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

/-- The address of slot `k` of a buffer, from the index in a register. -/
private theorem index_addr (v : UInt32) (k n : Nat) (hk : k ≤ n)
    (hn : 8 * n < UInt32.size) :
    v + (UInt32.ofNat k <<< ((3 : UInt32) % 32)) =
      v + UInt32.ofNat (8 * k) := by
  have hto : (UInt32.ofNat k).toNat = k := ofNat_toNat (by omega)
  rw [shl_three, shift_three _ (by rw [hto]; omega), hto]

/-- An index step in a register. -/
private theorem index_add (c m : Nat) (hc : c < UInt32.size)
    (h : c + m < UInt32.size) :
    UInt32.ofNat c + UInt32.ofNat m = UInt32.ofNat (c + m) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, ofNat_toNat hc, ofNat_toNat (by omega),
    ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The count step of a turn, which the compiled body adds the other way
round. -/
private theorem index_add_flag (g : Nat) (c : Prop) [Decidable c]
    (h : g + 1 < UInt32.size) :
    (if c then (1 : UInt32) else 0) + UInt32.ofNat g =
      UInt32.ofNat (g + if c then 1 else 0) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl,
      index_add 1 g (by omega) (by omega)]
    congr 1
    omega
  · rw [if_neg hc, if_neg hc]
    rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl,
      index_add 0 g (by omega) (by omega)]
    congr 1
    omega

/-- Two slot addresses of one buffer are equal only for one index. -/
private theorem addr_inj (v : UInt32) (i j n : Nat) (hi : i ≤ n)
    (hj : j ≤ n) (hroom : v.toNat + 8 * n < UInt32.size)
    (h : v + UInt32.ofNat (8 * i) = v + UInt32.ofNat (8 * j)) :
    i = j := by
  have hti : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  have htj : (v + UInt32.ofNat (8 * j)).toNat = v.toNat + 8 * j :=
    Slices.byteOffset_toNat v (8 * j) (by omega)
  rw [h, htj] at hti
  omega

/-- One slot on from `k`. -/
private theorem addr_succ (v : UInt32) (k n : Nat) (hk : k + 1 ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (8 : UInt32) + (v + UInt32.ofNat (8 * k)) =
      v + UInt32.ofNat (8 * (k + 1)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  have hk8 : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have hk1 : (v + UInt32.ofNat (8 * (k + 1))).toNat
      = v.toNat + 8 * (k + 1) :=
    Slices.byteOffset_toNat v (8 * (k + 1)) (by omega)
  rw [UInt32.toNat_add, hk8, hk1,
    show (8 : UInt32).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two slots on from `k`. -/
private theorem addr_succ2 (v : UInt32) (k n : Nat) (hk : k + 2 ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (16 : UInt32) + (v + UInt32.ofNat (8 * k)) =
      v + UInt32.ofNat (8 * (k + 2)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  have hk8 : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have hk1 : (v + UInt32.ofNat (8 * (k + 2))).toNat
      = v.toNat + 8 * (k + 2) :=
    Slices.byteOffset_toNat v (8 * (k + 2)) (by omega)
  rw [UInt32.toNat_add, hk8, hk1,
    show (16 : UInt32).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

/-- One slot back from `k`, which the compiled body writes as an addition
of the wrapped constant. -/
private theorem addr_pred (v : UInt32) (k n : Nat) (hk1 : 1 ≤ k)
    (hk : k ≤ n) (hroom : v.toNat + 8 * n < UInt32.size) :
    (4294967288 : UInt32) + (v + UInt32.ofNat (8 * k)) =
      v + UInt32.ofNat (8 * (k - 1)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  have hk8 : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have hk1' : (v + UInt32.ofNat (8 * (k - 1))).toNat
      = v.toNat + 8 * (k - 1) :=
    Slices.byteOffset_toNat v (8 * (k - 1)) (by omega)
  rw [UInt32.toNat_add, hk8, hk1',
    show (4294967288 : UInt32).toNat = 4294967288 from rfl,
    show 4294967288 + (v.toNat + 8 * k)
      = (v.toNat + 8 * k - 8) + 4294967296 from by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The base of the tail of the buffer. -/
private theorem addr_base (v : UInt32) (n : Nat) (hn : 1 ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (8 : UInt32) + v = v + UInt32.ofNat (8 * 1) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  have h1 : (v + UInt32.ofNat (8 * 1)).toNat = v.toNat + 8 * 1 :=
    Slices.byteOffset_toNat v (8 * 1) (by omega)
  rw [UInt32.toNat_add, h1, show (8 : UInt32).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The address of slot `k`, as the compiled body builds it: the shifted
index first and the base second. -/
private theorem shl_addr (v : UInt32) (k n : Nat) (hk : k ≤ n)
    (hn : 8 * n < UInt32.size) :
    UInt32.ofNat k <<< ((3 : UInt32) % 32) + v =
      v + UInt32.ofNat (8 * k) := by
  rw [UInt32.add_comm]
  exact index_addr v k n hk hn

/-- An index in a register is below the length. -/
private theorem ofNat_lt_len (k : Nat) (len : UInt32)
    (hk : k < len.toNat) : UInt32.ofNat k < len := by
  have hlt : len.toNat < UInt32.size := UInt32.toNat_lt len
  rw [UInt32.lt_iff_toNat_lt, ofNat_toNat (by omega)]
  exact hk

/-- Two slot addresses of one buffer compare as their indices do. -/
private theorem addr_lt_iff (v : UInt32) (i j n : Nat) (hi : i ≤ n)
    (hj : j ≤ n) (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * i) < v + UInt32.ofNat (8 * j)) ↔ i < j := by
  have hti : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  have htj : (v + UInt32.ofNat (8 * j)).toNat = v.toNat + 8 * j :=
    Slices.byteOffset_toNat v (8 * j) (by omega)
  rw [UInt32.lt_iff_toNat_lt, hti, htj]
  omega

/-- The address of tail slot 1, as the compiled body builds it. -/
private theorem addr_buf_two (buf v : UInt32) (n : Nat)
    (hv : v = 8 + buf) (h1 : 1 ≤ n)
    (hroom : buf.toNat + 8 * (n + 1) < UInt32.size) :
    (16 : UInt32) + buf = v + UInt32.ofNat (8 * 1) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  have hv8 : v.toNat = buf.toNat + 8 := by
    rw [hv, UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have h1' : (v + UInt32.ofNat (8 * 1)).toNat = v.toNat + 8 * 1 :=
    Slices.byteOffset_toNat v (8 * 1) (by omega)
  rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl, h1',
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The address of the end of the buffer, as the compiled body builds
it. -/
private theorem addr_buf_end (buf v len : UInt32) (n : Nat)
    (hv : v = 8 + buf) (hlen : len.toNat = n + 1)
    (hroom : buf.toNat + 8 * (n + 1) < UInt32.size) :
    len <<< ((3 : UInt32) % 32) + buf = v + UInt32.ofNat (8 * n) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hshift : len <<< ((3 : UInt32) % 32)
      = UInt32.ofNat (8 * (n + 1)) := by
    rw [shl_three, shift_three len (by rw [hlen]; omega), hlen]
  rw [hshift]
  apply UInt32.toNat_inj.mp
  have hv8 : v.toNat = buf.toNat + 8 := by
    rw [hv, UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hend : (v + UInt32.ofNat (8 * n)).toNat = v.toNat + 8 * n :=
    Slices.byteOffset_toNat v (8 * n) (by omega)
  have hofn : (UInt32.ofNat (8 * (n + 1))).toNat = 8 * (n + 1) :=
    ofNat_toNat (by omega)
  rw [UInt32.toNat_add, hofn, hend, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The address of slot zero is the base. -/
private theorem addr_zero (v : UInt32) :
    v = v + UInt32.ofNat (8 * 0) := by
  rw [show 8 * 0 = 0 from rfl, show UInt32.ofNat 0 = (0 : UInt32)
    from rfl, UInt32.add_zero]

/-! ## One memory step on one entry

The four rules below hide the cell arithmetic of one entry.  They are
copies of the private rules of `Func22Proof`.
-/

private theorem getElem_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps[i] = entryAt ps i :=
  (entryAt_eq_getElem ps hi).symm

private theorem set_pair_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) :
    ps.set i ((entryAt ps i).1, (entryAt ps i).2) = ps :=
  set_entryAt ps hi

/-- Move an owned double word between two names of one address. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

/-- Move an owned word between two names of one address. -/
private theorem wordMove32 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 (α := α) 0 address value ⊢
      pointsTo_u32 0 address' value := by
  rw [haddress]

/-- The four byte addresses of one `i32` cell. -/
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

/-- The eight byte addresses of one `i64` cell. -/
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
/-- `i64.load offset=8` of the whole entry `k + 1`, from the address of
entry `k`.  WAT 5998 is the one load of the region that has an
offset. -/
private theorem twp_entry_read_off8 [WasmSmallStepGS hlc Universal.State]
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
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have hfacts := offset_facts64 (v + UInt32.ofNat (8 * k)) 8 8 rfl
    (by omega)
  have haddr8 : v + UInt32.ofNat (8 * (k + 1))
      = v + UInt32.ofNat (8 * k) + 8 := by
    apply UInt32.toNat_inj.mp
    have h1 : (v + UInt32.ofNat (8 * (k + 1))).toNat
        = v.toNat + 8 * (k + 1) :=
      Slices.byteOffset_toNat v (8 * (k + 1)) (by omega)
    have h2 : (v + UInt32.ofNat (8 * k) + 8).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + (8 : UInt32).toNat :=
      hfacts.1
    rw [h1, h2, hbase, show (8 : UInt32).toNat = 8 from rfl]
    omega
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 haddr8 $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := v + UInt32.ofNat (8 * k)) (offset := 8)
    (Table.pairWord (entryAt ps (k + 1))) hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 haddr8.symm $$ Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps (k + 1)) Hcell
  isimp only [set_entryAt ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

/-- `i32.wrap_i64` of the word of an entry is the key of the entry. -/
private theorem pairWord_low (p : UInt32 × UInt32) :
    UInt32.ofNat ((Table.pairWord p).toNat % 2 ^ 32) = p.1 := by
  have hwrap : UInt32.ofNat ((Table.pairWord p).toNat % 2 ^ 32)
      = (Table.pairWord p).toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32,
      UInt32.toNat_ofNat_of_lt' (by
        have h : (Table.pairWord p).toNat % 2 ^ 32 < 2 ^ 32 :=
          Nat.mod_lt _ (Nat.two_pow_pos 32)
        change (Table.pairWord p).toNat % 2 ^ 32 < 4294967296
        omega)]
  rw [hwrap, ← UInt32.toNat_inj, UInt64.toNat_toUInt32]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · have h4 : i / 8 < 4 := by omega
    have hlen8 : (WordCodec.encodeU32 p.1 ++
        WordCodec.encodeU32 p.2).length ≤ 8 := by
      simp [WordCodec.encodeU32]
    have hlen4 : (WordCodec.encodeU32 p.1).length ≤ 8 := by
      simp [WordCodec.encodeU32]
    have hget : (WordCodec.encodeU32 p.1 ++
          WordCodec.encodeU32 p.2).getD (i / 8) 0
        = (WordCodec.encodeU32 p.1).getD (i / 8) 0 := by
      rw [List.getD_append]
      simp [WordCodec.encodeU32]
      omega
    simp only [hi, decide_true, Bool.true_and]
    rw [Table.pairWord, Table.groupWord,
      Table.u64OfBytesLE_testBit _ hlen8 i, hget,
      ← Table.u64OfBytesLE_testBit _ hlen4 i,
      SipHash.u64OfBytesLE_encodeU32, UInt32.toNat_toUInt64]
  · have hfalse : p.1.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le p.1.toNat_lt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, hfalse]

/-! ## The shape of the fragments

Every fragment of the region, as the list of instructions that the
generated code holds.  Each lemma is `rfl`.
-/

/-- WAT 5977 to 6001. -/
private theorem qsStrictSetup_shape :
    qsStrictSetup =
      [Instruction.localGet 0, .load64 0, .localSet 12, .localGet 0,
        .localGet 0, .localGet 6, .add, .localTee 6, .load64 0, .store64 0,
        .localGet 6, .localGet 12, .store64 0, .localGet 0, .const 8, .add,
        .localSet 9, .localGet 0, .load32 0, .localSet 10, .localGet 0,
        .load64 8, .localSet 12, .const 0, .localSet 7] := by
  rfl

/-- WAT 6004 to 6021. -/
private theorem qsStrictFwdPre_shape :
    qsStrictFwdPre =
      [Instruction.localGet 0, .const 16, .add, .localTee 6, .localGet 0,
        .localGet 1, .const 3, .shl, .add, .localTee 13, .const 4294967288,
        .add, .localTee 14, .ltU, .br_if 0, .localGet 9, .localSet 8,
          .br 1] := by
  rfl

/-- WAT 6023 and 6024. -/
private theorem qsStrictFwdMid_shape :
    qsStrictFwdMid =
      [Instruction.const 0, .localSet 7] := by
  rfl

/-- WAT 6026 to 6080. -/
private theorem qsStrictFwdLoop_shape :
    qsStrictFwdLoop =
      [Instruction.localGet 6, .const 4294967288, .add, .localGet 9,
        .localGet 7, .const 3, .shl, .add, .localTee 8, .load64 0, .store64 0,
        .localGet 6, .load32 0, .localSet 11, .localGet 8, .localGet 6,
        .load64 0, .store64 0, .localGet 6, .localGet 9, .localGet 7,
        .localGet 11, .localGet 10, .ltU, .add, .localTee 7, .const 3, .shl,
        .add, .localTee 8, .load64 0, .store64 0, .localGet 6, .const 8, .add,
        .localTee 11, .load32 0, .localSet 15, .localGet 8, .localGet 11,
        .load64 0, .store64 0, .localGet 7, .localGet 15, .localGet 10, .ltU,
        .add, .localSet 7, .localGet 6, .const 16, .add, .localTee 6,
        .localGet 14, .ltU, .br_if 0] := by
  rfl

/-- WAT 6082 to 6085. -/
private theorem qsStrictFwdTail_shape :
    qsStrictFwdTail =
      [Instruction.localGet 6, .const 4294967288, .add, .localSet 8] := by
  rfl

/-- WAT 6087 to 6089. -/
private theorem qsStrictMid_shape :
    qsStrictMid =
      [Instruction.localGet 12, .wrapI64, .localSet 15] := by
  rfl

/-- WAT 6091 to 6094. -/
private theorem qsStrictBackPre_shape :
    qsStrictBackPre =
      [Instruction.localGet 6, .localGet 13, .eq, .br_if 0] := by
  rfl

/-- WAT 6096 to 6125. -/
private theorem qsStrictBackLoop_shape :
    qsStrictBackLoop =
      [Instruction.localGet 8, .localGet 9, .localGet 7, .const 3, .shl,
        .add, .localTee 11, .load64 0, .store64 0, .localGet 6, .localTee 8,
        .load32 0, .localSet 6, .localGet 11, .localGet 8, .load64 0, .store64
        0, .localGet 7, .localGet 6, .localGet 10, .ltU, .add, .localSet 7,
        .localGet 8, .const 8, .add, .localTee 6, .localGet 13, .ne,
          .br_if 0] := by
  rfl

/-- WAT 6127 to 6130. -/
private theorem qsStrictBackTail_shape :
    qsStrictBackTail =
      [Instruction.localGet 6, .const 4294967288, .add, .localSet 8] := by
  rfl

/-- WAT 6132 to 6151. -/
private theorem qsStrictWriteBack_shape :
    qsStrictWriteBack =
      [Instruction.localGet 8, .localGet 9, .localGet 7, .const 3, .shl,
        .add, .localTee 6, .load64 0, .store64 0, .localGet 6, .localGet 12,
        .store64 0, .localGet 7, .localGet 10, .localGet 15, .gtU, .add,
        .localTee 6, .localGet 1, .geU] := by
  rfl

/-! ## The registers

The region touches the locals 6 to 15.  `Regs` holds every other
register of the body, which the region carries unchanged.  The five
`pad` fields are the locals 16 to 20: they are there because
`Locals.set?` of local 15 only computes when the list of declared
locals starts with sixteen explicit entries.
-/

/-- The registers that the region does not touch. -/
structure Regs where
  buf : UInt32
  len : UInt32
  anc : UInt32
  limit : UInt32
  env : UInt32
  fp : UInt32
  pad16 : Value
  pad17 : Value
  pad18 : Value
  pad19 : Value
  pad20 : Value
  tail : List Value

/-- The locals of the region, with the ten live registers. -/
@[reducible] def qsRegs (f : Regs) (l6 l7 l8 l9 l10 l11 : UInt32)
    (l12 : UInt64) (l13 l14 l15 : UInt32) (values : List Value) :
    Locals :=
  qsLocals f.buf f.len f.anc f.limit f.env
    (.i32 f.fp :: .i32 l6 :: .i32 l7 :: .i32 l8 :: .i32 l9 ::
      .i32 l10 :: .i32 l11 :: .i64 l12 :: .i32 l13 :: .i32 l14 ::
      .i32 l15 :: f.pad16 :: f.pad17 :: f.pad18 :: f.pad19 ::
      f.pad20 :: f.tail) values

/-! ## The write back, WAT 6132 to 6151 -/

set_option maxHeartbeats 2000000 in
/-- The write back pays the last deferred store, puts the held entry in
the gap slot and makes the split index.  The last two instructions test
the split index against the length, and the test is false, so the
continuation starts with the zero flag on the stack. -/
private theorem twp_write_back [WasmSmallStepGS hlc Universal.State]
    {f : Regs} {v pk : UInt32} {hv : UInt32 × UInt32}
    {orig B : List (UInt32 × UInt32)} {g n : Nat}
    {j6 j11 j13 j14 : UInt32} {Rest : HeapIProp}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hn : n = orig.length) (hlenB : B.length = n)
    (hlen : f.len.toNat = n + 1)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hinv : PartInv pk orig hv (settle B g n) g n)
    (hcont : ∀ (lt ge : List (UInt32 × UInt32)) (numLt : Nat),
      lt.length = numLt → numLt ≤ n → (lt ++ ge).Perm orig →
      (∀ x ∈ lt, x.1 < pk) → (∀ y ∈ ge, pk ≤ y.1) →
      iprop(Table.PairSlice 0 v (lt ++ ge) ∗ Rest) ⊢
        WP (.running ⟨qsRegs f (UInt32.ofNat numLt) (UInt32.ofNat g)
              (v + UInt32.ofNat (8 * (n - 1))) v pk j11
              (Table.pairWord hv) j13 j14 hv.1 [.i32 0],
            rest, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v B ∗ Rest) ⊢
      WP (.running ⟨qsRegs f j6 (UInt32.ofNat g)
            (v + UInt32.ofNat (8 * (n - 1))) v pk j11
            (Table.pairWord hv) j13 j14 hv.1 [],
          qsStrictWriteBack ++ rest, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hg : g < n := by
    have h1 := hinv.gapLt
    exact h1
  have hn1 : 1 ≤ n := by omega
  have hsz : UInt32.size = 4294967296 := rfl
  have hsettle : (settle B g n).length = n := by
    rw [settle, List.length_set, hlenB]
  iintro ⟨Hbuf, HRest⟩
  simp only [qsStrictWriteBack_shape, qsRegs, qsLocals, List.cons_append,
    List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
    twp_shl twp_add]
  isimp only [shl_addr v g n (by omega) (by omega)]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_entry_read (k := g) (n := n) (by omega) hlenB hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_entry_write (k := n - 1) (n := n) (q := entryAt B g)
    (by omega) hlenB hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [show B.set (n - 1) (entryAt B g) = settle B g n
    from rfl] at Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_entry_write (k := g) (n := n) (q := hv)
    (by omega) hsettle hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_gtU
    twp_add]
  isimp only [index_add_flag g (pk > hv.1) (by omega)]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  have hsplit : g + (if pk > hv.1 then 1 else 0)
      = splitIndex pk hv g := rfl
  isimp only [hsplit]
  have hlt : UInt32.ofNat (splitIndex pk hv g) < f.len := by
    refine ofNat_lt_len _ _ ?_
    rw [hlen, splitIndex]
    split_ifs <;> omega
  iapply Wasm.SmallStep.twp_geU (result := 0)
    (by rw [if_neg (fun hc => absurd hlt (not_lt_of_ge hc))])
  set out := (settle B g n).set g hv with hout
  set numLt := splitIndex pk hv g with hnumLt
  have hlenOut : out.length = n := by
    rw [hout, List.length_set, hsettle]
  have hnumLe : numLt ≤ n := by
    rw [hnumLt, splitIndex]
    split_ifs <;> omega
  have hsplitList : out = out.take numLt ++ out.drop numLt :=
    (List.take_append_drop _ _).symm
  have hlenTake : (out.take numLt).length = numLt := by
    rw [List.length_take, hlenOut]
    omega
  iapply (hcont (out.take numLt) (out.drop numLt) numLt hlenTake
    hnumLe (by rw [← hsplitList, hout]; exact hinv.perm)
    (PartInv_take hinv hn) (PartInv_drop hinv hn))
  isplitl [Hbuf]
  · irw_exact [← hsplitList] with Hbuf
  · iexact HRest

/-! ## The second scan, WAT 6090 to 6130

The second loop runs one turn of the partition.  It runs the entries
that the first loop left, and it runs every entry when the input is too
short for the first loop.
-/

set_option maxHeartbeats 4000000 in
/-- The block of the second scan, and the write back that follows it. -/
private theorem twp_scan_back [WasmSmallStepGS hlc Universal.State]
    {f : Regs} {v pk : UInt32} {hv : UInt32 × UInt32}
    {orig B : List (UInt32 × UInt32)} {g r n : Nat}
    {j11 j14 k8 : UInt32} {Rest : HeapIProp}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hn : n = orig.length) (hlenB : B.length = n)
    (hlen : f.len.toNat = n + 1)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hrn : r ≤ n) (hk8 : k8 = v + UInt32.ofNat (8 * (r - 1)))
    (hinv : PartInv pk orig hv (settle B g r) g r)
    (hcont : ∀ (lt ge : List (UInt32 × UInt32)) (numLt gf : Nat)
        (k11 : UInt32),
      lt.length = numLt → numLt ≤ n → (lt ++ ge).Perm orig →
      (∀ x ∈ lt, x.1 < pk) → (∀ y ∈ ge, pk ≤ y.1) →
      iprop(Table.PairSlice 0 v (lt ++ ge) ∗ Rest) ⊢
        WP (.running ⟨qsRegs f (UInt32.ofNat numLt) (UInt32.ofNat gf)
              (v + UInt32.ofNat (8 * (n - 1))) v pk k11
              (Table.pairWord hv) (v + UInt32.ofNat (8 * n)) j14 hv.1
              [.i32 0], rest, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v B ∗ Rest) ⊢
      WP (.running ⟨qsRegs f (v + UInt32.ofNat (8 * r)) (UInt32.ofNat g)
            k8 v pk j11
            (Table.pairWord hv) (v + UInt32.ofNat (8 * n)) j14 hv.1 [],
          .block 0 0 qsStrictScanBack :: (qsStrictWriteBack ++ rest),
          arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst hk8
  have hsz : UInt32.size = 4294967296 := rfl
  have hn8 : 8 * n < UInt32.size := by omega
  iintro ⟨Hbuf, HRest⟩
  simp only [qsStrictScanBack_split, qsStrictBackPre_shape,
    qsStrictBackTail_shape, List.cons_append, List.nil_append, qsRegs,
    qsLocals]
  wasm_twp_pures [twp_block]
  wasm_twp_pures [twp_localGet twp_localGet]
  by_cases hend : r = n
  · -- the cursor is the end, so the loop does not run
    subst hend
    iapply Wasm.SmallStep.twp_eq (result := 1) (by rw [if_pos rfl])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    iapply (twp_write_back (j6 := v + UInt32.ofNat (8 * r))
      (j13 := v + UInt32.ofNat (8 * r)) hn hlenB hlen hroom hinv
      (fun lt ge numLt h1 h2 h3 h4 h5 =>
        hcont lt ge numLt g j11 h1 h2 h3 h4 h5))
    isplitl_exact Hbuf
    · iexact HRest
  · -- the loop runs
    have hrlt : r < n := by omega
    have hne : v + UInt32.ofNat (8 * r) ≠ v + UInt32.ofNat (8 * n) :=
      fun hc => hend (addr_inj v r n n (by omega) (by omega) hroom hc)
    iapply Wasm.SmallStep.twp_eq (result := 0) (by rw [if_neg hne])
    iapply Wasm.SmallStep.twp_brIfZero
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := List (UInt32 × UInt32) × Nat × Nat × UInt32)
      (measure := fun i => n - i.2.2.1)
      (locals := fun i => qsRegs f (v + UInt32.ofNat (8 * i.2.2.1))
        (UInt32.ofNat i.2.1) (v + UInt32.ofNat (8 * (i.2.2.1 - 1))) v pk
        i.2.2.2 (Table.pairWord hv) (v + UInt32.ofNat (8 * n)) j14 hv.1
        [])
      (I := fun i => iprop(
        ⌜PartInv pk orig hv (settle i.1 i.2.1 i.2.2.1) i.2.1 i.2.2.1 ∧
          i.1.length = n ∧ i.2.2.1 < n⌝ ∗
        Table.PairSlice 0 v i.1 ∗ Rest))
      (initial := (B, g, r, j11))
      (initialLocals := qsRegs f (v + UInt32.ofNat (8 * r))
        (UInt32.ofNat g) (v + UInt32.ofNat (8 * (r - 1))) v pk j11
        (Table.pairWord hv) (v + UInt32.ofNat (8 * n)) j14 hv.1 [])
      rfl rfl
    · intro i
      obtain ⟨Bi, gi, ri, k11⟩ := i
      iintro Hrec ⟨%hstate, Hbuf, HRest⟩
      obtain ⟨hinvi0, hlenBi0, hrin0⟩ := hstate
      have hinvi : PartInv pk orig hv (settle Bi gi ri) gi ri := hinvi0
      have hlenBi : Bi.length = n := hlenBi0
      have hrin : ri < n := hrin0
      have hgi : gi < ri := hinvi.gapLt
      have hlenA : (settle Bi gi ri).length = n := by
        rw [settle, List.length_set, hlenBi]
      simp only [Wasm.SmallStep.loopBodyExpr, qsStrictBackLoop_shape,
        qsRegs, qsLocals]
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
        twp_shl twp_add]
      isimp only [shl_addr v gi n (by omega) hn8]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_entry_read (k := gi) (n := n) (by omega) hlenBi hroom
        rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := ri - 1) (n := n)
        (q := entryAt Bi gi) (by omega) hlenBi hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      isimp only [show Bi.set (ri - 1) (entryAt Bi gi)
        = settle Bi gi ri from rfl] at Hbuf
      wasm_twp_pures [twp_localGet]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_key_read (k := ri) (n := n) (by omega) hlenA hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply twp_entry_read (k := ri) (n := n) (by omega) hlenA hroom
        rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := gi) (n := n)
        (q := entryAt (settle Bi gi ri) ri) (by omega) hlenA hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ltU
        twp_add]
      isimp only [index_add_flag gi
        ((entryAt (settle Bi gi ri) ri).1 < pk) (by omega)]
      isimp only [show gi + (if (entryAt (settle Bi gi ri) ri).1 < pk
          then 1 else 0) = gapNext pk (settle Bi gi ri) gi ri from rfl]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [addr_succ v ri n (by omega) hroom]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      have hnext : PartInv pk orig hv
          (partStep pk (settle Bi gi ri) gi ri)
          (gapNext pk (settle Bi gi ri) gi ri) (ri + 1) :=
        PartInv_step hinvi (by omega)
      have hfold : settle
          ((settle Bi gi ri).set gi (entryAt (settle Bi gi ri) ri))
          (gapNext pk (settle Bi gi ri) gi ri) (ri + 1)
          = partStep pk (settle Bi gi ri) gi ri := by
        rw [settle, partStep, Nat.add_sub_cancel]
      have hlenNew : ((settle Bi gi ri).set gi
          (entryAt (settle Bi gi ri) ri)).length = n := by
        rw [List.length_set, hlenA]
      by_cases hlast : ri + 1 = n
      · -- the cursor reaches the end
        iapply Wasm.SmallStep.twp_ne (result := 0)
          (by rw [if_neg (by rw [hlast]; exact fun hc => hc rfl)])
        iapply Wasm.SmallStep.twp_brIfZero
        wasm_twp_pures [twp_exitControl] using
          [List.take_zero, List.nil_append, List.drop_zero]
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [hlast]
        isimp only [addr_pred v n n (by omega) (by omega) hroom]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_exitControl] using
          [List.take_zero, List.nil_append, List.drop_zero]
        iapply (twp_write_back (j6 := v + UInt32.ofNat (8 * n))
          (j11 := v + UInt32.ofNat (8 * gi))
          (j13 := v + UInt32.ofNat (8 * n))
          (g := gapNext pk (settle Bi gi ri) gi ri)
          hn hlenNew hlen hroom (by rw [← hlast, hfold]; exact hnext)
          (fun lt ge numLt h1 h2 h3 h4 h5 =>
            hcont lt ge numLt (gapNext pk (settle Bi gi ri) gi ri)
              (v + UInt32.ofNat (8 * gi)) h1 h2 h3 h4 h5))
        isplitl_exact Hbuf
        iexact HRest
      · -- one more turn
        have hne2 : v + UInt32.ofNat (8 * (ri + 1))
            ≠ v + UInt32.ofNat (8 * n) := fun hc =>
          hlast (addr_inj v (ri + 1) n n (by omega) (by omega) hroom hc)
        iapply Wasm.SmallStep.twp_ne (result := 1) (by rw [if_pos hne2])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        ihave Hgo := Hrec $$ %(((settle Bi gi ri).set gi
            (entryAt (settle Bi gi ri) ri),
          gapNext pk (settle Bi gi ri) gi ri, ri + 1,
          v + UInt32.ofNat (8 * gi)) :
          List (UInt32 × UInt32) × Nat × Nat × UInt32)
          %(show n - (ri + 1) < n - ri by omega)
        isimp only [Wasm.SmallStep.loopBodyExpr, qsRegs, qsLocals,
          Nat.add_sub_cancel] at Hgo
        iapply Hgo
        isplitl_pureexact (⟨by rw [hfold]; exact hnext, hlenNew,
          by omega⟩ :
          PartInv pk orig hv (settle
              ((settle Bi gi ri).set gi (entryAt (settle Bi gi ri) ri))
              (gapNext pk (settle Bi gi ri) gi ri) (ri + 1))
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1) ∧
          ((settle Bi gi ri).set gi
              (entryAt (settle Bi gi ri) ri)).length = n ∧
          ri + 1 < n)
        isplitl_exact Hbuf
        iexact HRest
    · isplitl_pureexact (⟨hinv, hlenB, hrlt⟩ :
        PartInv pk orig hv (settle B g r) g r ∧ B.length = n ∧ r < n)
      isplitl_exact Hbuf
      iexact HRest

/-! ## The first scan, WAT 6002 to 6089

The first loop runs two turns of the partition in one pass.  It runs
only when the tail holds three entries or more, and it stops with a
cursor of `n - 1` or `n`.  The three instructions of WAT 6087 to 6089
take the key of the held entry out of local 12.
-/

set_option maxHeartbeats 4000000 in
/-- The block of the first scan, the three instructions that follow it,
the second scan and the write back. -/
private theorem twp_scan_fwd [WasmSmallStepGS hlc Universal.State]
    {f : Regs} {v pk : UInt32} {hv : UInt32 × UInt32}
    {orig B : List (UInt32 × UInt32)} {n : Nat}
    {j6 j8 j11 j13 j14 j15 : UInt32} {Rest : HeapIProp}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hn : n = orig.length) (hlenB : B.length = n) (h1n : 1 ≤ n)
    (hlen : f.len.toNat = n + 1) (hvbuf : v = 8 + f.buf)
    (hroomBuf : f.buf.toNat + 8 * (n + 1) < UInt32.size)
    (hinv : PartInv pk orig hv (settle B 0 1) 0 1)
    (hcont : ∀ (lt ge : List (UInt32 × UInt32)) (numLt gf : Nat)
        (k11 k14 : UInt32),
      lt.length = numLt → numLt ≤ n → (lt ++ ge).Perm orig →
      (∀ x ∈ lt, x.1 < pk) → (∀ y ∈ ge, pk ≤ y.1) →
      iprop(Table.PairSlice 0 v (lt ++ ge) ∗ Rest) ⊢
        WP (.running ⟨qsRegs f (UInt32.ofNat numLt) (UInt32.ofNat gf)
              (v + UInt32.ofNat (8 * (n - 1))) v pk k11
              (Table.pairWord hv) (v + UInt32.ofNat (8 * n)) k14 hv.1
              [.i32 0], rest, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v B ∗ Rest) ⊢
      WP (.running ⟨qsRegs f j6 0 j8 v pk j11 (Table.pairWord hv) j13
            j14 j15 [],
          .block 0 0 qsStrictScanFwd :: (qsStrictMid ++
            (.block 0 0 qsStrictScanBack :: (qsStrictWriteBack ++ rest))),
          arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hvtoNat : v.toNat = f.buf.toNat + 8 := by
    rw [hvbuf, UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hroom : v.toNat + 8 * n < UInt32.size := by omega
  have hn8 : 8 * n < UInt32.size := by omega
  have hzero : (0 : UInt32) = UInt32.ofNat 0 := rfl
  iintro ⟨Hbuf, HRest⟩
  simp only [qsStrictScanFwd_split, qsStrictFwdPre_shape,
    qsStrictFwdMid_shape, qsStrictFwdTail_shape, qsStrictMid_shape,
    List.cons_append, List.nil_append, qsRegs, qsLocals]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const twp_add]
  isimp only [addr_buf_two f.buf v n hvbuf h1n hroomBuf]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
  isimp only [addr_buf_end f.buf v f.len n hvbuf hlen hroomBuf]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const twp_add]
  isimp only [addr_pred v n n (by omega) (by omega) hroom]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  by_cases hbig : 3 ≤ n
  · -- the tail holds three entries or more, so the loop runs
    iapply Wasm.SmallStep.twp_ltU (result := 1)
      (by rw [if_pos ((addr_lt_iff v 1 (n - 1) n (by omega) (by omega)
        hroom).mpr (by omega))])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := List (UInt32 × UInt32) × Nat × Nat ×
        (UInt32 × UInt32 × UInt32))
      (measure := fun i => n - i.2.2.1)
      (locals := fun i => qsRegs f (v + UInt32.ofNat (8 * i.2.2.1))
        (UInt32.ofNat i.2.1) i.2.2.2.1 v pk i.2.2.2.2.1
        (Table.pairWord hv) (v + UInt32.ofNat (8 * n))
        (v + UInt32.ofNat (8 * (n - 1))) i.2.2.2.2.2 [])
      (I := fun i => iprop(
        ⌜PartInv pk orig hv (settle i.1 i.2.1 i.2.2.1) i.2.1 i.2.2.1 ∧
          i.1.length = n ∧ i.2.2.1 + 2 ≤ n⌝ ∗
        Table.PairSlice 0 v i.1 ∗ Rest))
      (initial := (B, 0, 1, (j8, j11, j15)))
      (initialLocals := qsRegs f (v + UInt32.ofNat (8 * 1))
        0 j8 v pk j11 (Table.pairWord hv)
        (v + UInt32.ofNat (8 * n)) (v + UInt32.ofNat (8 * (n - 1))) j15
        [])
      rfl rfl
    · intro i
      obtain ⟨Bi, gi, ri, k8, k11, k15⟩ := i
      iintro Hrec ⟨%hstate, Hbuf, HRest⟩
      obtain ⟨hinvi0, hlenBi0, hrin0⟩ := hstate
      have hinvi : PartInv pk orig hv (settle Bi gi ri) gi ri := hinvi0
      have hlenBi : Bi.length = n := hlenBi0
      have hrin : ri + 2 ≤ n := hrin0
      have hgi : gi < ri := hinvi.gapLt
      have hlenA : (settle Bi gi ri).length = n := by
        rw [settle, List.length_set, hlenBi]
      simp only [Wasm.SmallStep.loopBodyExpr, qsStrictFwdLoop_shape,
        qsRegs, qsLocals]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [addr_pred v ri n (by omega) (by omega) hroom]
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl
        twp_add]
      isimp only [shl_addr v gi n (by omega) hn8]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_entry_read (k := gi) (n := n) (by omega) hlenBi hroom
        rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := ri - 1) (n := n)
        (q := entryAt Bi gi) (by omega) hlenBi hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      isimp only [show Bi.set (ri - 1) (entryAt Bi gi)
        = settle Bi gi ri from rfl] at Hbuf
      wasm_twp_pures [twp_localGet]
      iapply twp_key_read (k := ri) (n := n) (by omega) hlenA hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply twp_entry_read (k := ri) (n := n) (by omega) hlenA hroom
        rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := gi) (n := n)
        (q := entryAt (settle Bi gi ri) ri) (by omega) hlenA hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet
        twp_localGet twp_localGet twp_ltU twp_add]
      isimp only [index_add_flag gi
        ((entryAt (settle Bi gi ri) ri).1 < pk) (by omega)]
      isimp only [show gi + (if (entryAt (settle Bi gi ri) ri).1 < pk
          then 1 else 0) = gapNext pk (settle Bi gi ri) gi ri from rfl]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      have hg' : gapNext pk (settle Bi gi ri) gi ri ≤ gi + 1 :=
        gapNext_le _ _ _ _
      have hlen1 : ((settle Bi gi ri).set gi
          (entryAt (settle Bi gi ri) ri)).length = n := by
        rw [List.length_set, hlenA]
      wasm_twp_pures [twp_const twp_shl twp_add]
      isimp only [shl_addr v (gapNext pk (settle Bi gi ri) gi ri) n
        (by omega) hn8]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_entry_read (k := gapNext pk (settle Bi gi ri) gi ri)
        (n := n) (by omega) hlen1 hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := ri) (n := n)
        (q := entryAt ((settle Bi gi ri).set gi
          (entryAt (settle Bi gi ri) ri))
          (gapNext pk (settle Bi gi ri) gi ri)) (by omega) hlen1 hroom
        rfl
      isplitl_exact Hbuf
      iintro Hbuf
      isimp only [show ((settle Bi gi ri).set gi
          (entryAt (settle Bi gi ri) ri)).set ri
          (entryAt ((settle Bi gi ri).set gi
            (entryAt (settle Bi gi ri) ri))
            (gapNext pk (settle Bi gi ri) gi ri))
          = partStep pk (settle Bi gi ri) gi ri from rfl] at Hbuf
      have hlen2 : (partStep pk (settle Bi gi ri) gi ri).length = n := by
        rw [partStep_length, hlenA]
      have hstep1 : PartInv pk orig hv
          (partStep pk (settle Bi gi ri) gi ri)
          (gapNext pk (settle Bi gi ri) gi ri) (ri + 1) :=
        PartInv_step hinvi (by omega)
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [addr_succ v ri n (by omega) hroom]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_key_read (k := ri + 1) (n := n) (by omega) hlen2 hroom
        rfl
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply twp_entry_read (k := ri + 1) (n := n) (by omega) hlen2
        hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := gapNext pk (settle Bi gi ri) gi ri)
        (n := n) (q := entryAt (partStep pk (settle Bi gi ri) gi ri)
          (ri + 1)) (by omega) hlen2 hroom rfl
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ltU
        twp_add]
      isimp only [index_add_flag (gapNext pk (settle Bi gi ri) gi ri)
        ((entryAt (partStep pk (settle Bi gi ri) gi ri) (ri + 1)).1 < pk)
        (by omega)]
      isimp only [show gapNext pk (settle Bi gi ri) gi ri +
          (if (entryAt (partStep pk (settle Bi gi ri) gi ri)
              (ri + 1)).1 < pk then 1 else 0)
          = gapNext pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1) from rfl]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [addr_succ2 v ri n (by omega) hroom]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      have hstep2 : PartInv pk orig hv
          (partStep pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1))
          (gapNext pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1)) (ri + 2) :=
        PartInv_step hstep1 (by omega)
      have hfold : settle
          ((partStep pk (settle Bi gi ri) gi ri).set
            (gapNext pk (settle Bi gi ri) gi ri)
            (entryAt (partStep pk (settle Bi gi ri) gi ri) (ri + 1)))
          (gapNext pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1)) (ri + 2)
          = partStep pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1) := by
        rw [settle, partStep]
        congr 1
      have hlen3 : ((partStep pk (settle Bi gi ri) gi ri).set
          (gapNext pk (settle Bi gi ri) gi ri)
          (entryAt (partStep pk (settle Bi gi ri) gi ri)
            (ri + 1))).length = n := by
        rw [List.length_set, hlen2]
      by_cases hmore : ri + 2 + 2 ≤ n
      · -- two more turns
        iapply Wasm.SmallStep.twp_ltU (result := 1)
          (by rw [if_pos ((addr_lt_iff v (ri + 2) (n - 1) n (by omega)
            (by omega) hroom).mpr (by omega))])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        ihave Hgo := Hrec $$ %(((partStep pk (settle Bi gi ri) gi ri).set
            (gapNext pk (settle Bi gi ri) gi ri)
            (entryAt (partStep pk (settle Bi gi ri) gi ri) (ri + 1)),
          gapNext pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1), ri + 2,
          (v + UInt32.ofNat
            (8 * gapNext pk (settle Bi gi ri) gi ri),
            v + UInt32.ofNat (8 * (ri + 1)),
            (entryAt (partStep pk (settle Bi gi ri) gi ri) (ri + 1)).1)) :
          List (UInt32 × UInt32) × Nat × Nat ×
            (UInt32 × UInt32 × UInt32))
          %(show n - (ri + 2) < n - ri by omega)
        isimp only [Wasm.SmallStep.loopBodyExpr, qsRegs, qsLocals,
          Nat.add_sub_cancel] at Hgo
        iapply Hgo
        isplitl_pureexact (⟨by rw [hfold]; exact hstep2, hlen3,
          by omega⟩ :
          PartInv pk orig hv (settle
              ((partStep pk (settle Bi gi ri) gi ri).set
                (gapNext pk (settle Bi gi ri) gi ri)
                (entryAt (partStep pk (settle Bi gi ri) gi ri)
                  (ri + 1)))
              (gapNext pk (partStep pk (settle Bi gi ri) gi ri)
                (gapNext pk (settle Bi gi ri) gi ri) (ri + 1)) (ri + 2))
            (gapNext pk (partStep pk (settle Bi gi ri) gi ri)
              (gapNext pk (settle Bi gi ri) gi ri) (ri + 1)) (ri + 2) ∧
          ((partStep pk (settle Bi gi ri) gi ri).set
              (gapNext pk (settle Bi gi ri) gi ri)
              (entryAt (partStep pk (settle Bi gi ri) gi ri)
                (ri + 1))).length = n ∧
          ri + 2 + 2 ≤ n)
        isplitl_exact Hbuf
        iexact HRest
      · -- the loop stops
        have hstop : ¬ (ri + 2 < n - 1) := by omega
        iapply Wasm.SmallStep.twp_ltU (result := 0)
          (by rw [if_neg (fun hc => hstop ((addr_lt_iff v (ri + 2)
            (n - 1) n (by omega) (by omega) hroom).mp hc))])
        iapply Wasm.SmallStep.twp_brIfZero
        wasm_twp_pures [twp_exitControl] using
          [List.take_zero, List.nil_append, List.drop_zero]
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [addr_pred v (ri + 2) n (by omega) (by omega) hroom]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_exitControl] using
          [List.take_zero, List.nil_append, List.drop_zero]
        wasm_twp_pures [twp_localGet twp_wrapI64]
        isimp only [pairWord_low hv]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        iapply (twp_scan_back (r := ri + 2)
          (g := gapNext pk (partStep pk (settle Bi gi ri) gi ri)
            (gapNext pk (settle Bi gi ri) gi ri) (ri + 1))
          (j11 := v + UInt32.ofNat (8 * (ri + 1)))
          (j14 := v + UInt32.ofNat (8 * (n - 1)))
          hn hlen3 hlen hroom (by omega) rfl
          (by rw [hfold]; exact hstep2)
          (fun lt ge numLt gf k11 h1 h2 h3 h4 h5 =>
            hcont lt ge numLt gf k11
              (v + UInt32.ofNat (8 * (n - 1))) h1 h2 h3 h4 h5))
        isplitl_exact Hbuf
        iexact HRest
    · isplitl_pureexact (⟨hinv, hlenB, by omega⟩ :
        PartInv pk orig hv (settle B 0 1) 0 1 ∧ B.length = n ∧
          1 + 2 ≤ n)
      isplitl_exact Hbuf
      iexact HRest
  · -- the tail is too short for the first loop
    have hsmall : ¬ (1 < n - 1) := by omega
    iapply Wasm.SmallStep.twp_ltU (result := 0)
      (by rw [if_neg (fun hc => hsmall ((addr_lt_iff v 1 (n - 1) n
        (by omega) (by omega) hroom).mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_br rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    wasm_twp_pures [twp_localGet twp_wrapI64]
    isimp only [pairWord_low hv]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    isimp only [hzero]
    iapply (twp_scan_back (r := 1) (g := 0) (B := B) (k8 := v)
      (j11 := j11) (j14 := v + UInt32.ofNat (8 * (n - 1)))
      hn hlenB hlen hroom (by omega)
      (by rw [show 8 * (1 - 1) = 0 from rfl,
        show UInt32.ofNat 0 = (0 : UInt32) from rfl, UInt32.add_zero])
      hinv
      (fun lt ge numLt gf k11 h1 h2 h3 h4 h5 =>
        hcont lt ge numLt gf k11 (v + UInt32.ofNat (8 * (n - 1)))
          h1 h2 h3 h4 h5))
    isplitl_exact Hbuf
    iexact HRest

/-! ## The stage lemma, WAT 5977 to 6151 -/

set_option maxHeartbeats 4000000 in
/-- The strict partition of the `quicksort` body.  The pivot is the
entry at `ip`.  WAT 5977 to 5989 put it in slot 0, and the partition
runs over the other `len - 1` entries.  The buffer that the region
leaves is the pivot and then the two parts, and local 6 holds the length
of the first part.  The last instruction of the region is the test of
that length against the length of the buffer, which is false, so the
continuation starts with the zero flag on the stack.  The second part is
not sorted, and the WAT gives it the bound `pivot key at or below the
key`, not the strict bound. -/
theorem twp_strict_partition [WasmSmallStepGS hlc Universal.State]
    {f : Regs} {ip : Nat} {j7 j8 j9 j10 j11 j13 j14 j15 : UInt32}
    {j12 : UInt64} {pairs : List (UInt32 × UInt32)} {Rest : HeapIProp}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : pairs.length = f.len.toNat) (h2 : 2 ≤ f.len.toNat)
    (hip : ip < f.len.toNat)
    (hroom : f.buf.toNat + 8 * f.len.toNat < UInt32.size)
    (hcont : ∀ (lt ge : List (UInt32 × UInt32)) (numLt : Nat)
        (k7 k8 k9 k10 k11 k13 k14 k15 : UInt32) (k12 : UInt64),
      lt.length = numLt → numLt < f.len.toNat →
      (entryAt pairs ip :: (lt ++ ge)).Perm pairs →
      (∀ x ∈ lt, x.1 < (entryAt pairs ip).1) →
      (∀ y ∈ ge, (entryAt pairs ip).1 ≤ y.1) →
      iprop(Table.PairSlice 0 f.buf (entryAt pairs ip :: (lt ++ ge)) ∗
        Rest) ⊢
        WP (.running ⟨qsRegs f (UInt32.ofNat numLt) k7 k8 k9 k10 k11 k12
              k13 k14 k15 [.i32 0], rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 f.buf pairs ∗ Rest) ⊢
      WP (.running ⟨qsRegs f (UInt32.ofNat (8 * ip)) j7 j8 j9 j10 j11
            j12 j13 j14 j15 [], qsStrictPartition ++ rest, arity,
          remainder, controls, calls⟩ : Expr Universal.State) @ s; E
        [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  set n := f.len.toNat - 1 with hndef
  have hn1 : f.len.toNat = n + 1 := by omega
  have h1n : 1 ≤ n := by omega
  have hlenN : pairs.length = n + 1 := by omega
  have hip' : ip < n + 1 := by omega
  have h0 : 0 < pairs.length := by omega
  have hipl : ip < pairs.length := by omega
  set p := entryAt pairs ip with hp
  set ps2 := (pairs.set 0 p).set ip (entryAt pairs 0) with hps2
  have hlen2 : ps2.length = n + 1 := by
    rw [hps2, List.length_set, List.length_set, hlenN]
  have hperm : ps2.Perm pairs := by
    have hswap : ps2 = Table.swapAt pairs 0 ip := by
      rw [hps2, Table.swapAt_eq_set_set pairs h0 hipl, hp,
        entryAt_eq_getElem pairs hipl, entryAt_eq_getElem pairs h0]
    rw [hswap]
    exact Table.swapAt_perm pairs h0 hipl
  have hhead : entryAt ps2 0 = p := by
    rw [hps2, hp]
    exact entryAt_swap_head pairs h0 hipl
  set B0 := ps2.drop 1 with hB0
  have hcons : ps2 = p :: B0 := by
    have hc := cons_drop_one ps2 (show 0 < ps2.length by omega)
    rw [hhead] at hc
    exact hc
  have hlenB0 : B0.length = n := by
    have hd : B0.length = ps2.length - 1 := by
      rw [hB0]
      exact List.length_drop
    omega
  set hv := entryAt B0 0 with hhv
  set v := 8 + f.buf with hvdef
  have hvtoNat : v.toNat = f.buf.toNat + 8 := by
    rw [hvdef, UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hroomv : v.toNat + 8 * n < UInt32.size := by omega
  have hentry1 : entryAt ps2 1 = hv := by
    rw [hhv, hB0]
    exact (entryAt_drop_one ps2).symm
  have hlenSet : (pairs.set 0 p).length = n + 1 := by
    have hs : (pairs.set 0 p).length = pairs.length :=
      List.length_set
    omega
  iintro ⟨Hbuf, HRest⟩
  simp only [qsStrictPartition_split, qsStrictSetup_shape,
    List.cons_append, List.nil_append, List.append_assoc, qsRegs,
    qsLocals]
  wasm_twp_pures [twp_localGet]
  iapply twp_entry_read (k := 0) (n := n + 1) (by omega) hlenN
    (by omega) (addr_zero f.buf)
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_add]
  isimp only [show UInt32.ofNat (8 * ip) + f.buf
    = f.buf + UInt32.ofNat (8 * ip) from UInt32.add_comm _ _]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_entry_read (k := ip) (n := n + 1) (by omega) hlenN
    (by omega) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_entry_write (k := 0) (n := n + 1) (q := entryAt pairs ip)
    (by omega) hlenN (by omega) (addr_zero f.buf)
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_entry_write (k := ip) (n := n + 1)
    (q := entryAt pairs 0) (by omega) hlenSet (by omega) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← hp, ← hps2] at Hbuf
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [← hvdef]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_read (k := 0) (n := n + 1) (by omega) hlen2 (by omega)
    (addr_zero f.buf)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [hhead]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_entry_read_off8 (k := 0) (n := n + 1) (by omega) hlen2
    (by omega) (addr_zero f.buf)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [show (0 : Nat) + 1 = 1 from rfl, hentry1]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  isimp only [hcons] at Hbuf
  icases (Table.PairSlice_cons 0 f.buf p B0).mp $$ Hbuf with
    ⟨⟨%hnowrap, Hpivot⟩, Hbuf⟩
  isimp only [show f.buf + 8 = v from UInt32.add_comm _ _] at Hbuf
  iapply (twp_scan_fwd (v := v) (pk := p.1) (hv := hv) (orig := B0)
    (B := B0) (n := n) (Rest := iprop(
      pointsTo_u64 0 f.buf (Table.pairWord p) ∗ Rest))
    hlenB0.symm hlenB0 h1n hn1 hvdef (by omega)
    (by rw [settle_start B0 (by omega)]
        exact PartInv_start p.1 B0 (by omega)))
  · iintro %lt %ge %numLt %gf %k11 %k14 %hlt %hnum %hpermB %hlow %hhigh
    iintro ⟨Hbuf, Hpivot, HRest⟩
    iapply (hcont lt ge numLt (UInt32.ofNat gf)
      (v + UInt32.ofNat (8 * (n - 1))) v p.1 k11
      (v + UInt32.ofNat (8 * n)) k14 hv.1 (Table.pairWord hv) hlt
      (by omega) ?_ hlow hhigh)
    · rw [hp] at hcons ⊢
      refine List.Perm.trans ?_ hperm
      rw [hcons]
      exact (hpermB.cons p)
    · isplitl [Hbuf Hpivot]
      · iapply (Table.PairSlice_cons 0 f.buf p (lt ++ ge)).mpr
        isplitl [Hpivot]
        · isplitl_pureexact hnowrap
          iexact Hpivot
        · irw_exact [show v = f.buf + 8 from (UInt32.add_comm _ _).symm]
            with Hbuf
      · iexact HRest
  · isplitl_exact Hbuf
    isplitl_exact Hpivot
    iexact HRest

end Project.RustHashMap.Func21Partition
