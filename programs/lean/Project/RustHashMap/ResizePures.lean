import Project.RustHashMap.Func14Capacity
import CodeLib.RustStd.HashMap.ResizeWalk
import CodeLib.RustStd.HashMap.EraseWasm

/-!
# The model side of the resize arm of absolute `func 17`

`Project.RustHashMap.Func14Proof` proves absolute `func 17` on the path
that `collect_entries` takes, where the old table is the static empty
singleton.  On that path three regions are dead.  The path of absolute
`func 18` keeps one of them alive: the resize walk of WAT lines 3746 to
4083, which moves every full bucket of the old table into the fresh one.

This module holds the pure facts that the walk proof needs.  It mentions
no separation logic.

## The decision

The contract gives `Clean t` and `t.growthLeft = 0`.  Those two say that
`t.items` is the full capacity of the old table, so the reserve is a
resize and never a rehash in place.  `reserve_one_eq` names the capacity
`resizeCap t`, and `resize_spec` reads the result off
`Table.WF.resize`.

## The order of the walk

The model folds over `Table.fullIndices`, the ascending list of full
buckets.  The compiled loop walks the control bytes one group of eight at
a time, and inside a group it takes the lowest set byte first.
`CodeLib.RustStd.HashMap.ResizeWalk.walk_eq_fullIndices` shows the two
orders agree for a bucket count that eight divides, and
`walk_eq_fullIndices_small` does the same for four buckets.

`walkFrom` and `walkRem` below name the two states of the loop: `walkFrom
t n b` is the work left when the loop starts group `b`, and `walkRem t n b
msk` is the work left when the loop holds the mask `msk` inside group `b`.
`walkFrom_zero` starts the walk, `walkRem_full` enters a group,
`walkRem_cons` takes one bucket, `walkRem_zero` leaves a group and
`walkFrom_skip` steps over a group with no full bucket.

## The mask the compiled code holds

The group-advance loop of WAT 3802 to 3818 keeps `group & REP80`, the
special bytes, and stops when that word is not `REP80`.  WAT 3819 to 3822
turns it into the full mask with one more `xor`.  `and_xor_self` and
`swarMatchFull_eq_zero_iff` are the two facts that reading needs.
-/

namespace Project.RustHashMap.ResizePures

open Wasm
open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.Table
open Project.RustHashMap.EntryContracts

/-! ## Bit words -/

/-- No bit at or above 64 of a `UInt64` is set. -/
theorem testBit_high {x : UInt64} {i : Nat} (hi : 64 ≤ i) :
    x.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (UInt64.toNat_lt x)
      (Nat.pow_le_pow_right (by decide) hi))

/-- `(a & m) ^ m` clears the bits of `a` inside `m` and drops the rest.
The compiled code writes the full mask that way at WAT 3819 to 3822. -/
theorem and_xor_self (a m : UInt64) : (a &&& m) ^^^ m = ~~~a &&& m := by
  rw [not_eq_xor_neg_one]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_xor, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor]
  by_cases hi : i < 64
  · have hall : (18446744073709551615 : UInt64).toNat.testBit i = true := by
      rw [show (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 from rfl,
        Nat.testBit_two_pow_sub_one, decide_eq_true hi]
    rw [hall]
    cases a.toNat.testBit i <;> cases m.toNat.testBit i <;> rfl
  · rw [testBit_high (x := a) (by omega), testBit_high (x := m) (by omega)]
    simp

/-- Two words differ exactly when their `xor` has a set bit. -/
theorem xor_eq_zero_iff (x y : UInt64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg UInt64.toNat h
    rw [UInt64.toNat_xor, show (0 : UInt64).toNat = 0 from rfl] at h'
    apply UInt64.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro i
    have hb := congrArg (fun n => Nat.testBit n i) h'
    simp only [Nat.testBit_xor, Nat.zero_testBit] at hb
    cases hx : x.toNat.testBit i <;> cases hy : y.toNat.testBit i <;>
      rw [hx, hy] at hb <;> first | rfl | simp at hb
  · intro h
    subst h
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_xor, show (0 : UInt64).toNat = 0 from rfl]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.zero_testBit, Bool.xor_self]

/-- The group-advance loop of WAT 3802 to 3818 stops when the special mask
is not `REP80`.  That is exactly when the group holds a full byte. -/
theorem swarMatchFull_eq_zero_iff (g : UInt64) :
    swarMatchFull g = 0 ↔ g &&& REP80 = REP80 := by
  unfold swarMatchFull
  rw [← and_xor_self g REP80, xor_eq_zero_iff]

/-- An empty mask flags no byte. -/
theorem setBytes_zero : setBytes 0 = [] := by decide

/-! ## The decision of `reserve` -/

section Model

variable {K V : Type} {hash : K → UInt64} {t : Table K V}

/-- The capacity that the resize of a clean and full table asks for. -/
def resizeCap (t : Table K V) : Nat :=
  Table.bucketMaskToCapacity (t.buckets - 1) + 1

/-- A clean table with no growth left holds its full capacity. -/
theorem items_eq_fullCap (hcl : Clean t) (hg : t.growthLeft = 0) :
    t.items = Table.bucketMaskToCapacity (t.buckets - 1) := by
  have h := hcl.2
  omega

theorem resizeCap_eq_items_succ (hcl : Clean t) (hg : t.growthLeft = 0) :
    resizeCap t = t.items + 1 := by
  have h := items_eq_fullCap hcl hg
  unfold resizeCap
  omega

/-- The reserve of one item on a clean and full table is a resize to the
next capacity.  The rehash-in-place arm of WAT 3116 to 3640 is dead. -/
theorem reserve_one_eq (hcl : Clean t) (hg : t.growthLeft = 0) :
    Table.reserve hash t 1 = Table.resize hash t (resizeCap t) := by
  rw [reserve_eq_resize hcl (by omega)]
  have h := items_eq_fullCap hcl hg
  congr 1
  unfold resizeCap
  omega

/-- The capacity of the resize takes the general form of the sizing. -/
theorem capBuckets_resizeCap (t : Table K V) :
    capBuckets (resizeCap t) = Table.capacityToBuckets (resizeCap t) := by
  unfold capBuckets
  rw [if_neg (by unfold resizeCap; omega)]

/-- The bucket count of the fresh table, as the compiled code computes it
from the capacity. -/
theorem resize_buckets_bound (hcl : Clean t) (hg : t.growthLeft = 0)
    (hmax : t.items + 1 ≤ maxTableCapacity) :
    resizeCap t ≤ maxTableCapacity ∧ 1 ≤ resizeCap t := by
  rw [resizeCap_eq_items_succ hcl hg]
  omega

/-- The fresh table of the resize is well formed, clean, and has the
bucket count and the item count the compiled code writes back. -/
theorem resize_spec (hw : WF hash t) (hcl : Clean t) (hg : t.growthLeft = 0)
    (hmax : t.items + 1 ≤ maxTableCapacity) :
    WF hash (Table.reserve hash t 1) ∧ Clean (Table.reserve hash t 1) ∧
      (Table.reserve hash t 1).buckets
        = Table.capacityToBuckets (resizeCap t) ∧
      (Table.reserve hash t 1).items = t.items := by
  obtain ⟨hle, hone⟩ := resize_buckets_bound hcl hg hmax
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  rw [hmaxEq] at hle
  have hbound : resizeCap t * 8 / 7 ≤ 2 ^ 32 := by
    have h1 : resizeCap t * 8 ≤ 939524096 := by omega
    have h2 : resizeCap t * 8 / 7 ≤ 939524096 :=
      le_trans (Nat.div_le_self _ 7) h1
    have h3 : (939524096 : Nat) ≤ 2 ^ 32 := by norm_num
    omega
  obtain ⟨hs, hcapLe⟩ := capBuckets_spec (cap := resizeCap t) hbound
  have hitems : t.items
      ≤ Table.bucketMaskToCapacity (capBuckets (resizeCap t) - 1) := by
    have := resizeCap_eq_items_succ hcl hg
    omega
  rw [reserve_one_eq hcl hg]
  obtain ⟨hw', hcl', hb', hi', -⟩ := hw.resize hs hitems
  exact ⟨hw', hcl', by rw [hb', capBuckets_resizeCap t], hi'⟩

/-! ## The order of the walk -/

/-- The full buckets of group `b` of the old table, as bucket numbers.
The compiled loop reads that group at WAT 3808 to 3813. -/
def groupRun (t : Table K V) (b : Nat) : List Nat :=
  (setBytes (swarMatchFull (groupWord (groupAt t (8 * b))))).map
    (fun j => 8 * b + j)

/-- The buckets the walk still has to move when it starts group `b`. -/
def walkFrom (t : Table K V) (n b : Nat) : List Nat :=
  ((List.range n).drop b).flatMap (groupRun t)

/-- The buckets the walk still has to move while it holds the mask `msk`
inside group `b`. -/
def walkRem (t : Table K V) (n b : Nat) (msk : UInt64) : List Nat :=
  (setBytes msk).map (fun j => 8 * b + j) ++ walkFrom t n (b + 1)

theorem walkFrom_nil (t : Table K V) (n : Nat) : walkFrom t n n = [] := by
  unfold walkFrom
  rw [List.drop_eq_nil_of_le (by rw [List.length_range])]
  rfl

/-- The walk enters group `b` and leaves the groups after it. -/
theorem walkFrom_cons (t : Table K V) {n b : Nat} (hb : b < n) :
    walkFrom t n b = groupRun t b ++ walkFrom t n (b + 1) := by
  unfold walkFrom
  rw [List.drop_eq_getElem_cons (by rw [List.length_range]; exact hb),
    List.getElem_range, List.flatMap_cons]

/-- A group with no full byte costs the walk nothing. -/
theorem walkFrom_skip (t : Table K V) {n b : Nat} (hb : b < n)
    (hzero : swarMatchFull (groupWord (groupAt t (8 * b))) = 0) :
    walkFrom t n b = walkFrom t n (b + 1) := by
  rw [walkFrom_cons t hb]
  unfold groupRun
  rw [hzero, setBytes_zero, List.map_nil, List.nil_append]

/-- The mask that the compiled code builds when it enters group `b` leaves
exactly the work of that group. -/
theorem walkRem_full (t : Table K V) {n b : Nat} (hb : b < n) :
    walkRem t n b (swarMatchFull (groupWord (groupAt t (8 * b))))
      = walkFrom t n b := by
  rw [walkFrom_cons t hb]
  rfl

/-- An empty mask leaves the group. -/
theorem walkRem_zero (t : Table K V) (n b : Nat) :
    walkRem t n b 0 = walkFrom t n (b + 1) := by
  unfold walkRem
  rw [setBytes_zero, List.map_nil, List.nil_append]

/-- One turn of the walk: the lowest flagged byte of the mask is the next
bucket, and `mask & (mask - 1)` is the rest.  The compiled code takes the
lowest byte at WAT 3826 to 3838 and clears it at WAT 4044 to 4047. -/
theorem walkRem_cons (t : Table K V) (n b : Nat) {msk : UInt64}
    (hmask : msk &&& REP80 = msk) {j0 : Nat}
    (hlow : lowestSetByte msk = some j0) :
    walkRem t n b msk
      = (8 * b + j0)
          :: walkRem t n b (msk &&& (msk + 18446744073709551615)) := by
  unfold walkRem
  rw [setBytes_iterNext hmask hlow, List.map_cons, List.cons_append]

/-! ## The whole walk -/

/-- The groups of a table whose bucket count eight divides. -/
theorem walkFrom_zero_big (hb : t.buckets = 8 * n) :
    walkFrom t n 0 = Table.fullIndices t := by
  unfold walkFrom
  rw [List.drop_zero]
  exact walk_eq_fullIndices t hb

/-- The one group of a table with fewer than eight buckets. -/
theorem walkFrom_zero_small (hw : Layout hash t) (hsmall : t.buckets < 8) :
    walkFrom t 1 0 = Table.fullIndices t := by
  unfold walkFrom groupRun
  rw [List.drop_zero, show List.range 1 = [0] from rfl, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Nat.mul_zero]
  simp only [Nat.zero_add, List.map_id_fun', id_eq]
  exact walk_eq_fullIndices_small hw hsmall

/-- The number of groups the walk reads. -/
def walkGroups (t : Table K V) : Nat :=
  if t.buckets < 8 then 1 else t.buckets / 8

/-- The walk starts with the whole ascending list of full buckets, for
either bucket count the contract allows. -/
theorem walkFrom_zero (hw : Layout hash t) :
    walkFrom t (walkGroups t) 0 = Table.fullIndices t := by
  unfold walkGroups
  by_cases hsmall : t.buckets < 8
  · rw [if_pos hsmall]
    exact walkFrom_zero_small hw hsmall
  · rw [if_neg hsmall]
    refine walkFrom_zero_big ?_
    obtain ⟨m, hm, hm1, hpow⟩ := hw.shape
    have h8 : 8 ≤ t.buckets := by omega
    have hdvd : 8 ∣ t.buckets := by
      have hm3 : 3 ≤ m := by
        by_contra hlt
        interval_cases m <;> omega
      rw [hpow, show m = 3 + (m - 3) by omega, Nat.pow_add]
      exact Dvd.intro _ rfl
    omega

/-! ## The fold of `resize` -/

/-- The table that the walk builds, before the two counters. -/
def movedTable (hash : K → UInt64) (t : Table K V) : Table K V :=
  (Table.fullIndices t).foldl (Table.moveStep hash t)
    (Table.withCapacity (resizeCap t))

/-- The answer of the contract, field by field.  The compiled code writes
the control pointer, the mask and the growth counter at WAT 4085 to 4092
and leaves the item count alone. -/
theorem reserve_one_fields (hcl : Clean t) (hg : t.growthLeft = 0) :
    Table.reserve hash t 1 =
      withCounters (movedTable hash t) t.items
        ((movedTable hash t).growthLeft - t.items) := by
  rw [reserve_one_eq hcl hg, resize_eq]
  rfl

/-- The growth counter of the fresh table never moves while the walk
runs. -/
theorem movedTable_growthLeft (hash : K → UInt64) (t : Table K V) :
    (movedTable hash t).growthLeft
      = Table.bucketMaskToCapacity (capBuckets (resizeCap t) - 1) := by
  unfold movedTable
  rw [foldl_moveStep_growthLeft, withCapacity_eq]
  rfl

/-- Every field of `place`, which is the write of one turn of the walk. -/
theorem place_fields (n : Table K V) (i : Nat) (tag : UInt8) (kv : K × V) :
    Table.place n i tag kv =
      { buckets := n.buckets,
        ctrl := (n.ctrl.set i tag).set (Table.index2 n.buckets i) tag,
        slots := n.slots.set i (some kv),
        items := n.items,
        growthLeft := n.growthLeft } := rfl

/-- The fold of `resize` starts on the fresh table. -/
theorem moveInv_start (t : Table K V) {cap : Nat}
    (hs : Shape (capBuckets cap)) :
    MoveInv hash t (capBuckets cap) [] (Table.withCapacity cap) := by
  rw [withCapacity_eq]
  exact ⟨layout_newEmpty hs hash, rfl, fun i _ _ => ctrlAt_newEmpty _ i,
    by rw [toList_newEmpty]; exact List.Perm.refl _⟩

/-- One turn of the fold, with every fact the compiled loop needs: the pair
of the old bucket, the insert index, the `EMPTY` byte at that index, and
the probe history that the insert loop of WAT 3988 to 4013 walks. -/
theorem moveStep_spec (hw : Layout hash t) {b₀ : Nat}
    (hcap : (Table.toList t).length
      ≤ Table.bucketMaskToCapacity (b₀ - 1))
    {l₁ l₂ : List Nat} {i : Nat}
    (hlist : l₁ ++ i :: l₂ = Table.fullIndices t)
    {n : Table K V} (hinv : MoveInv hash t b₀ l₁ n) :
    ∃ k v, t.slotAt i = some (k, v) ∧
      Table.findInsertIndex n (hash k) < n.buckets ∧
      n.ctrlAt (Table.findInsertIndex n (hash k)) = Table.EMPTY ∧
      (∃ m, Table.InWindow n (hash k) m
          (Table.findInsertIndex n (hash k)) ∧
        ∀ m', m' < m →
          Table.matchEmpty (Table.window n (hash k) m') = false) ∧
      Table.moveStep hash t n i
        = Table.place n (Table.findInsertIndex n (hash k))
            (Table.h2 (hash k)) (k, v) := by
  obtain ⟨hln, hb, hsp, hperm⟩ := hinv
  have hi : i ∈ Table.fullIndices t := by
    rw [← hlist]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨hib, hif⟩ := mem_fullIndices.1 hi
  obtain ⟨⟨k, v⟩, hs⟩ :=
    Option.isSome_iff_exists.1 ((hw.full_iff i hib).1 hif)
  have hlen : (Table.toList n).length < n.buckets := by
    have e1 : (Table.toList n).length = (l₁.filterMap t.slotAt).length :=
      hperm.length_eq
    have e2 : (l₁.filterMap t.slotAt).length ≤ l₁.length :=
      List.length_filterMap_le _ _
    have e3 := length_fullIndices hw
    have e4 : (l₁ ++ i :: l₂).length = (Table.fullIndices t).length := by
      rw [hlist]
    rw [List.length_append, List.length_cons] at e4
    have e5 := hln.shape.cap_lt
    rw [hb] at e5 ⊢
    omega
  obtain ⟨e, he, hemp⟩ := hln.exists_empty_of_lt hsp hlen
  obtain ⟨hlt, hsp', m, hin, hnoemp⟩ :=
    hln.findInsertIndex_spec (hash k) he hemp
  exact ⟨k, v, hs, hlt, hsp _ hlt hsp', ⟨m, hin, hnoemp⟩, by
    simp only [Table.moveStep, hs]⟩

end Model

end Project.RustHashMap.ResizePures
