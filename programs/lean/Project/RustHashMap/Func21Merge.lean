import Project.RustHashMap.Func21Region

/-!
# The merge of the `quicksort` small sort

Absolute `func 24` is `quicksort`, local `func21`.  WAT lines 8503 to
8652 of `programs/rust/build/rust_hash_map/program.wat` hold the merge
half of the small sort.  `Project.RustHashMap.Func21Region` proves the
region half, WAT 6193 to 8501, and hands this module two sorted runs.

## What the merge computes

A length of 18 or more splits the buffer into two regions, the first
`len / 2` entries and the rest.  The region loop sorts each region on
its own, so the buffer holds `L ++ Rt` with `L` and `Rt` in key order.
The merge writes the two runs into the frame and copies the frame back.

The merge is bidirectional.  One loop turn takes one entry off the two
fronts and writes it up from the frame base, and takes one entry off the
two backs and writes it down from the frame end.  The loop makes
`len / 2` turns.  An odd length leaves one entry, which WAT 8601 to 8630
moves with one more forward step.

`SortModels.bimerge` is the model of that run: `mergeUp` of
`(len + 1) / 2` entries, then `mergeDown` of `len / 2` entries.  The
buffer is never written while the merge runs, so the forward half and
the backward half read the same two runs and never see each other.  That
is why the model is two separate `mergeTake` calls.

## What the pure theorems say

* `bimerge_exhausts` says the two halves meet exactly.  Both pointer
  tests of WAT 8632 to 8641 are therefore dead, which is the arm
  X-F24-ORDER of `Analysis/scope-and-exclusions.md`.
* `bimerge_perm` and `bimerge_sorted` say the result is a sorted
  permutation of `L ++ Rt`.
* `bimerge_length` says the result has the length of both runs.

The route is one induction, `mergeTake_spec`.  It says that `n` steps of
a merge of two runs that are in the order `R` leave the suffixes
`l.drop a` and `r.drop b` with `a + b = n`, take a permutation of
`l.take a ++ r.take b`, and put every taken key below every key that is
left.  `mergeUp` is that lemma for the key order and `mergeDown` is the
same lemma for the reverse key order on the reversed runs.

`merge_partition` then closes the two halves against each other: the
forward half takes the smallest keys and the backward half the greatest,
the two counts add up to the whole length, and distinct keys leave no
room for an overlap or a gap.

## What the three run theorems say

* `twp_merge_loop` runs the merge loop, WAT 8524 to 8595.
* `twp_merge_tail` runs WAT 8597 to 8652, which is the odd middle, the
  two dead pointer tests and the copy back.
* `twp_merge` runs WAT 8503 to 8652 and leaves `bimerge L Rt` in the
  buffer.
* `twp_small_sort` runs the whole small sort, WAT 6193 to 8652, for
  every length below 33.
-/

namespace Project.RustHashMap.Func21Merge

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.Table
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.SortPures
open Project.RustHashMap.Func21Defs
open Project.RustHashMap.Func21Region
open scoped Wasm.SmallStep.Outcome

set_option maxRecDepth 40000

/-! ## The model of the bidirectional merge -/

private theorem mergeTake_nil_nil
    (lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool) (n : Nat) :
    mergeTake lt n [] [] = ([], [], []) := by
  cases n <;> rfl

set_option maxHeartbeats 2000000 in
private theorem mergeTake_taken_length
    (lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool) (n : Nat) :
    ∀ l r : List (UInt32 × UInt32),
      (mergeTake lt n l r).1.length = min n (l.length + r.length) := by
  induction n with
  | zero => intro l r; simp [mergeTake]
  | succ n ih =>
    intro l r
    match l, r with
    | [], [] => simp [mergeTake]
    | x :: xs, [] =>
      simp only [mergeTake, List.length_cons, ih xs [], List.length_nil]
      omega
    | [], y :: ys =>
      simp only [mergeTake, List.length_cons, ih [] ys, List.length_nil]
      omega
    | x :: xs, y :: ys =>
      by_cases h : lt y x
      · simp only [mergeTake, h, if_true, List.length_cons,
          ih (x :: xs) ys, List.length_cons]
        omega
      · simp only [mergeTake, h, if_false, Bool.false_eq_true,
          List.length_cons, ih xs (y :: ys), List.length_cons]
        omega

private theorem mergeTake_add
    (lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool) (i : Nat) :
    ∀ (j : Nat) (l r : List (UInt32 × UInt32)),
      mergeTake lt (i + j) l r =
        ((mergeTake lt i l r).1
            ++ (mergeTake lt j (mergeTake lt i l r).2.1
                  (mergeTake lt i l r).2.2).1,
          (mergeTake lt j (mergeTake lt i l r).2.1
            (mergeTake lt i l r).2.2).2.1,
          (mergeTake lt j (mergeTake lt i l r).2.1
            (mergeTake lt i l r).2.2).2.2) := by
  induction i with
  | zero => intro j l r; simp [mergeTake]
  | succ i ih =>
    intro j l r
    match l, r with
    | [], [] => simp [mergeTake_nil_nil]
    | x :: xs, [] =>
      rw [show i + 1 + j = (i + j) + 1 from by omega]
      simp only [mergeTake]
      rw [show i + j = i + j from rfl]
      simp only [ih j xs []]
      simp
    | [], y :: ys =>
      rw [show i + 1 + j = (i + j) + 1 from by omega]
      simp only [mergeTake]
      simp only [ih j [] ys]
      simp
    | x :: xs, y :: ys =>
      rw [show i + 1 + j = (i + j) + 1 from by omega]
      simp only [mergeTake]
      by_cases h : lt y x
      · simp only [h, if_true]
        simp only [ih j (x :: xs) ys]
        simp
      · simp only [h, if_false, Bool.false_eq_true]
        simp only [ih j xs (y :: ys)]
        simp

set_option maxHeartbeats 2000000 in
private theorem mergeTake_spec
    {R : (UInt32 × UInt32) → (UInt32 × UInt32) → Prop}
    {lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hlt : ∀ x y, lt y x = true → R y x)
    (hge : ∀ x y, lt y x = false → R x y) (n : Nat) :
    ∀ l r : List (UInt32 × UInt32), l.Pairwise R → r.Pairwise R →
      ∃ a b : Nat, a ≤ l.length ∧ b ≤ r.length ∧
        a + b = min n (l.length + r.length) ∧
        (mergeTake lt n l r).2.1 = l.drop a ∧
        (mergeTake lt n l r).2.2 = r.drop b ∧
        (mergeTake lt n l r).1.Perm (l.take a ++ r.take b) ∧
        (mergeTake lt n l r).1.Pairwise R ∧
        (∀ u ∈ (mergeTake lt n l r).1,
          ∀ v ∈ l.drop a ++ r.drop b, R u v) := by
  induction n with
  | zero =>
    intro l r _ _
    exact ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by simp,
      by simp [mergeTake], by simp [mergeTake], by simp [mergeTake],
      by simp [mergeTake], by simp [mergeTake]⟩
  | succ n ih =>
    intro l r hl hr
    match l, r with
    | [], [] =>
      exact ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by simp,
        by simp [mergeTake], by simp [mergeTake], by simp [mergeTake],
        by simp [mergeTake], by simp [mergeTake]⟩
    | x :: xs, [] =>
      obtain ⟨a, b, ha, hb, hab, h1, h2, h3, h4, h5⟩ :=
        ih xs [] (List.Pairwise.of_cons hl) hr
      have hb0 : b = 0 := Nat.le_zero.mp hb
      subst hb0
      refine ⟨a + 1, 0, by simp at ha ⊢; omega, Nat.zero_le _, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.length_nil] at ha ⊢
        omega
      · simp only [mergeTake, h1, List.drop_succ_cons]
      · simp only [mergeTake, h2]
      · simp only [mergeTake]
        refine List.Perm.trans (List.Perm.cons x h3) ?_
        simp
      · simp only [mergeTake]
        refine List.pairwise_cons.mpr ⟨?_, h4⟩
        intro z hz
        have hz' : z ∈ xs.take a ++ ([] : List (UInt32 × UInt32)).take 0 :=
          h3.mem_iff.mp hz
        simp only [List.take_nil, List.append_nil] at hz'
        exact (List.pairwise_cons.mp hl).1 z (List.mem_of_mem_take hz')
      · intro u hu v hv
        simp only [mergeTake] at hu
        simp only [List.drop_succ_cons, List.drop_nil,
          List.append_nil] at hv
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact (List.pairwise_cons.mp hl).1 v (List.mem_of_mem_drop hv)
        · exact h5 u hu' v (by simp [hv])
    | [], y :: ys =>
      obtain ⟨a, b, ha, hb, hab, h1, h2, h3, h4, h5⟩ :=
        ih [] ys hl (List.Pairwise.of_cons hr)
      have ha0 : a = 0 := Nat.le_zero.mp ha
      subst ha0
      have hab2 : 0 + b = min n (0 + ys.length) := hab
      refine ⟨0, b + 1, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show b + 1 ≤ ys.length + 1
        omega
      · show 0 + (b + 1) = min (n + 1) (0 + (ys.length + 1))
        omega
      · simp only [mergeTake, h1]
      · simp only [mergeTake, h2, List.drop_succ_cons]
      · simp only [mergeTake]
        refine List.Perm.trans (List.Perm.cons y h3) ?_
        simp
      · simp only [mergeTake]
        refine List.pairwise_cons.mpr ⟨?_, h4⟩
        intro z hz
        have hz' : z ∈ ([] : List (UInt32 × UInt32)).take 0 ++ ys.take b :=
          h3.mem_iff.mp hz
        simp only [List.take_nil, List.nil_append] at hz'
        exact (List.pairwise_cons.mp hr).1 z (List.mem_of_mem_take hz')
      · intro u hu v hv
        simp only [mergeTake] at hu
        simp only [List.drop_succ_cons, List.drop_nil,
          List.nil_append] at hv
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact (List.pairwise_cons.mp hr).1 v (List.mem_of_mem_drop hv)
        · exact h5 u hu' v (by simp [hv])
    | x :: xs, y :: ys =>
      by_cases hc : lt y x
      · obtain ⟨a, b, ha, hb, hab, h1, h2, h3, h4, h5⟩ :=
          ih (x :: xs) ys hl (List.Pairwise.of_cons hr)
        have hyx : R y x := hlt x y hc
        have hyall : ∀ z ∈ x :: xs, R y z := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hyx
          · exact htrans _ _ _ hyx ((List.pairwise_cons.mp hl).1 z hz')
        have hyys : ∀ z ∈ ys, R y z :=
          fun z hz => (List.pairwise_cons.mp hr).1 z hz
        refine ⟨a, b + 1, ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons] at hb ⊢
          omega
        · simp only [List.length_cons] at hab ⊢
          omega
        · simp only [mergeTake, hc, if_true, h1]
        · simp only [mergeTake, hc, if_true, h2, List.drop_succ_cons]
        · simp only [mergeTake, hc, if_true]
          refine List.Perm.trans (List.Perm.cons y h3) ?_
          refine List.Perm.symm ?_
          simp only [List.take_succ_cons]
          exact (List.perm_middle (a := y) (l₁ := (x :: xs).take a)
            (l₂ := ys.take b))
        · simp only [mergeTake, hc, if_true]
          refine List.pairwise_cons.mpr ⟨?_, h4⟩
          intro z hz
          have hz' : z ∈ (x :: xs).take a ++ ys.take b := h3.mem_iff.mp hz
          rcases List.mem_append.mp hz' with hz1 | hz2
          · exact hyall z (List.mem_of_mem_take hz1)
          · exact hyys z (List.mem_of_mem_take hz2)
        · intro u hu v hv
          simp only [mergeTake, hc, if_true] at hu
          simp only [List.drop_succ_cons] at hv
          rcases List.mem_cons.mp hu with rfl | hu'
          · rcases List.mem_append.mp hv with hv1 | hv2
            · exact hyall v (List.mem_of_mem_drop hv1)
            · exact hyys v (List.mem_of_mem_drop hv2)
          · exact h5 u hu' v hv
      · obtain ⟨a, b, ha, hb, hab, h1, h2, h3, h4, h5⟩ :=
          ih xs (y :: ys) (List.Pairwise.of_cons hl) hr
        have hxy : R x y := hge x y (by simpa using hc)
        have hxxs : ∀ z ∈ xs, R x z :=
          fun z hz => (List.pairwise_cons.mp hl).1 z hz
        have hxall : ∀ z ∈ y :: ys, R x z := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hxy
          · exact htrans _ _ _ hxy ((List.pairwise_cons.mp hr).1 z hz')
        refine ⟨a + 1, b, ?_, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons] at ha ⊢
          omega
        · simp only [List.length_cons] at hab ⊢
          omega
        · simp only [mergeTake, hc, if_false, Bool.false_eq_true, h1,
            List.drop_succ_cons]
        · simp only [mergeTake, hc, if_false, Bool.false_eq_true, h2]
        · simp only [mergeTake, hc, if_false, Bool.false_eq_true]
          simp only [List.take_succ_cons, List.cons_append]
          exact List.Perm.cons x h3
        · simp only [mergeTake, hc, if_false, Bool.false_eq_true]
          refine List.pairwise_cons.mpr ⟨?_, h4⟩
          intro z hz
          have hz' : z ∈ xs.take a ++ (y :: ys).take b := h3.mem_iff.mp hz
          rcases List.mem_append.mp hz' with hz1 | hz2
          · exact hxxs z (List.mem_of_mem_take hz1)
          · exact hxall z (List.mem_of_mem_take hz2)
        · intro u hu v hv
          simp only [mergeTake, hc, if_false, Bool.false_eq_true] at hu
          simp only [List.drop_succ_cons] at hv
          rcases List.mem_cons.mp hu with rfl | hu'
          · rcases List.mem_append.mp hv with hv1 | hv2
            · exact hxxs v (List.mem_of_mem_drop hv1)
            · exact hxall v (List.mem_of_mem_drop hv2)
          · exact h5 u hu' v hv

/-! ## Helpers -/

private theorem mem_take_of_lt (l : List (UInt32 × UInt32)) {i k : Nat}
    (hi : i < l.length) (hik : i < k) : l[i] ∈ l.take k := by
  have h1 : i < (l.take k).length := by simp; omega
  have h2 := List.getElem_mem h1
  rwa [List.getElem_take] at h2

private theorem mem_drop_of_le (l : List (UInt32 × UInt32)) {i k : Nat}
    (hi : i < l.length) (hik : k ≤ i) : l[i] ∈ l.drop k := by
  have hik' : k + (i - k) = i := by omega
  have h1 : i - k < (l.drop k).length := by simp; omega
  have h2 := List.getElem_mem h1
  simp only [List.getElem_drop, hik'] at h2
  exact h2

private theorem reverse_take_eq (l : List (UInt32 × UInt32)) (p : Nat) :
    l.reverse.take (l.length - p) = (l.drop p).reverse := by
  have hl : l.reverse = (l.drop p).reverse ++ (l.take p).reverse := by
    conv_lhs => rw [← List.take_append_drop p l]
    rw [List.reverse_append]
  have hlen : (l.drop p).reverse.length = l.length - p := by simp
  conv_lhs => rw [hl]
  rw [← hlen, List.take_left]

private theorem reverse_drop_eq (l : List (UInt32 × UInt32)) (p : Nat) :
    l.reverse.drop (l.length - p) = (l.take p).reverse := by
  have hl : l.reverse = (l.drop p).reverse ++ (l.take p).reverse := by
    conv_lhs => rw [← List.take_append_drop p l]
    rw [List.reverse_append]
  have hlen : (l.drop p).reverse.length = l.length - p := by simp
  conv_lhs => rw [hl]
  rw [← hlen, List.drop_left]

/-! ## The forward half -/

private theorem mergeUp_spec (n : Nat) (l r : List (UInt32 × UInt32))
    (hl : SortedByKey l) (hr : SortedByKey r) :
    ∃ a b : Nat, a ≤ l.length ∧ b ≤ r.length ∧
      a + b = min n (l.length + r.length) ∧
      (mergeUp n l r).2.1 = l.drop a ∧
      (mergeUp n l r).2.2 = r.drop b ∧
      (mergeUp n l r).1.Perm (l.take a ++ r.take b) ∧
      SortedByKey (mergeUp n l r).1 ∧
      (∀ u ∈ (mergeUp n l r).1,
        ∀ v ∈ l.drop a ++ r.drop b, u.1 ≤ v.1) :=
  mergeTake_spec (R := fun a b => a.1 ≤ b.1) (lt := keyLt)
    (fun _ _ _ hab hbc => UInt32.le_trans hab hbc)
    (fun x y h => UInt32.le_of_lt (by
      simpa only [keyLt, decide_eq_true_eq] using h))
    (fun x y h => by
      have h' : ¬ (y.1 < x.1) := by
        simpa only [keyLt, decide_eq_false_iff_not] using h
      exact UInt32.not_lt.mp h')
    n l r hl hr

/-! ## The backward half -/

private theorem mergeDown_spec (n : Nat) (l r : List (UInt32 × UInt32))
    (hl : SortedByKey l) (hr : SortedByKey r) :
    ∃ a b : Nat, a ≤ l.length ∧ b ≤ r.length ∧
      a + b = min n (l.length + r.length) ∧
      (mergeDown n l r).2.1 = l.take (l.length - a) ∧
      (mergeDown n l r).2.2 = r.take (r.length - b) ∧
      (mergeDown n l r).1.Perm
        (l.drop (l.length - a) ++ r.drop (r.length - b)) ∧
      SortedByKey (mergeDown n l r).1 ∧
      (∀ u ∈ (mergeDown n l r).1,
        ∀ v ∈ l.take (l.length - a) ++ r.take (r.length - b),
          v.1 ≤ u.1) := by
  have hlr : l.reverse.Pairwise (fun a b => b.1 ≤ a.1) :=
    List.pairwise_reverse.mpr hl
  have hrr : r.reverse.Pairwise (fun a b => b.1 ≤ a.1) :=
    List.pairwise_reverse.mpr hr
  obtain ⟨a, b, ha, hb, hab, h1, h2, h3, h4, h5⟩ :=
    mergeTake_spec (R := fun a b => b.1 ≤ a.1) (lt := keyGt)
      (fun _ _ _ hab hbc => UInt32.le_trans hbc hab)
      (fun x y h => UInt32.le_of_lt (by
        simpa only [keyGt, decide_eq_true_eq] using h))
      (fun x y h => by
        have h' : ¬ (x.1 < y.1) := by
          simpa only [keyGt, decide_eq_false_iff_not] using h
        exact UInt32.not_lt.mp h')
      n l.reverse r.reverse hlr hrr
  simp only [List.length_reverse] at ha hb hab
  have hda : l.reverse.drop a = (l.take (l.length - a)).reverse := by
    have := reverse_drop_eq l (l.length - a)
    rwa [show l.length - (l.length - a) = a from by omega] at this
  have hdb : r.reverse.drop b = (r.take (r.length - b)).reverse := by
    have := reverse_drop_eq r (r.length - b)
    rwa [show r.length - (r.length - b) = b from by omega] at this
  have hta : l.reverse.take a = (l.drop (l.length - a)).reverse := by
    have := reverse_take_eq l (l.length - a)
    rwa [show l.length - (l.length - a) = a from by omega] at this
  have htb : r.reverse.take b = (r.drop (r.length - b)).reverse := by
    have := reverse_take_eq r (r.length - b)
    rwa [show r.length - (r.length - b) = b from by omega] at this
  refine ⟨a, b, ha, hb, hab, ?_, ?_, ?_, ?_, ?_⟩
  · show (mergeTake keyGt n l.reverse r.reverse).2.1.reverse = _
    rw [h1, hda, List.reverse_reverse]
  · show (mergeTake keyGt n l.reverse r.reverse).2.2.reverse = _
    rw [h2, hdb, List.reverse_reverse]
  · show (mergeTake keyGt n l.reverse r.reverse).1.reverse.Perm _
    refine (List.reverse_perm _).trans (h3.trans ?_)
    rw [hta, htb]
    exact ((List.reverse_perm _).append (List.reverse_perm _))
  · show SortedByKey (mergeTake keyGt n l.reverse r.reverse).1.reverse
    exact List.pairwise_reverse.mpr h4
  · intro u hu v hv
    have hu' : u ∈ (mergeTake keyGt n l.reverse r.reverse).1 := by
      have : u ∈ (mergeTake keyGt n l.reverse r.reverse).1.reverse := hu
      rwa [List.mem_reverse] at this
    refine h5 u hu' v ?_
    rw [hda, hdb]
    rcases List.mem_append.mp hv with hv1 | hv2
    · exact List.mem_append_left _ (List.mem_reverse.mpr hv1)
    · exact List.mem_append_right _ (List.mem_reverse.mpr hv2)

/-! ## The two halves meet -/

private theorem key_ne (l r : List (UInt32 × UInt32)) (hn : NodupKeys (l ++ r))
    {x y : (UInt32 × UInt32)} (hx : x ∈ l) (hy : y ∈ r) : x.1 ≠ y.1 := by
  have h2 : ((l.map Prod.fst) ++ (r.map Prod.fst)).Nodup := by
    have h1 : ((l ++ r).map Prod.fst).Nodup := hn
    rwa [List.map_append] at h1
  exact (List.nodup_append.mp h2).2.2 x.1 (List.mem_map_of_mem hx)
    y.1 (List.mem_map_of_mem hy)

set_option maxHeartbeats 2000000 in
private theorem merge_partition (l r : List (UInt32 × UInt32))
    (hn : NodupKeys (l ++ r)) {n1 n2 p q p' q' : Nat}
    (hsum : n1 + n2 = l.length + r.length)
    (hp : p ≤ l.length) (hq : q ≤ r.length) (hpq : p + q = n1)
    (hp' : p' ≤ l.length) (hq' : q' ≤ r.length) (hpq' : p' + q' = n2)
    (hup : ∀ u ∈ l.take p ++ r.take q,
      ∀ v ∈ l.drop p ++ r.drop q, u.1 ≤ v.1)
    (hdown : ∀ u ∈ l.drop (l.length - p') ++ r.drop (r.length - q'),
      ∀ v ∈ l.take (l.length - p') ++ r.take (r.length - q'),
        v.1 ≤ u.1) :
    p + p' = l.length ∧ q + q' = r.length := by
  have hkey : p + p' = l.length := by
    rcases Nat.lt_trichotomy (p + p') l.length with hlt | heq | hgt
    · exfalso
      have hi : p < l.length - p' := by omega
      have hil : p < l.length := by omega
      have hj : r.length - q' < q := by omega
      have hjr : r.length - q' < r.length := by omega
      have hx1 : l[p] ∈ l.drop p := mem_drop_of_le l hil (Nat.le_refl p)
      have hx2 : l[p] ∈ l.take (l.length - p') :=
        mem_take_of_lt l hil hi
      have hy1 : r[r.length - q'] ∈ r.take q := mem_take_of_lt r hjr hj
      have hy2 : r[r.length - q'] ∈ r.drop (r.length - q') :=
        mem_drop_of_le r hjr (Nat.le_refl _)
      have hle1 : (r[r.length - q']).1 ≤ (l[p]).1 :=
        hup _ (List.mem_append_right _ hy1) _
          (List.mem_append_left _ hx1)
      have hle2 : (l[p]).1 ≤ (r[r.length - q']).1 :=
        hdown _ (List.mem_append_right _ hy2) _
          (List.mem_append_left _ hx2)
      exact key_ne l r hn (List.getElem_mem hil) (List.getElem_mem hjr)
        (UInt32.le_antisymm hle2 hle1)
    · exact heq
    · exfalso
      have hi : l.length - p' < p := by omega
      have hil : l.length - p' < l.length := by omega
      have hj : q < r.length - q' := by omega
      have hjr : q < r.length := by omega
      have hx1 : l[l.length - p'] ∈ l.take p := mem_take_of_lt l hil hi
      have hx2 : l[l.length - p'] ∈ l.drop (l.length - p') :=
        mem_drop_of_le l hil (Nat.le_refl _)
      have hy1 : r[q] ∈ r.drop q := mem_drop_of_le r hjr (Nat.le_refl q)
      have hy2 : r[q] ∈ r.take (r.length - q') := mem_take_of_lt r hjr hj
      have hle1 : (l[l.length - p']).1 ≤ (r[q]).1 :=
        hup _ (List.mem_append_left _ hx1) _
          (List.mem_append_right _ hy1)
      have hle2 : (r[q]).1 ≤ (l[l.length - p']).1 :=
        hdown _ (List.mem_append_left _ hx2) _
          (List.mem_append_right _ hy2)
      exact key_ne l r hn (List.getElem_mem hil) (List.getElem_mem hjr)
        (UInt32.le_antisymm hle1 hle2)
  exact ⟨hkey, by omega⟩

/-! ## The four facts of the bidirectional merge -/

set_option maxHeartbeats 2000000 in
private theorem bimerge_facts (l r : List (UInt32 × UInt32))
    (hl : SortedByKey l) (hr : SortedByKey r)
    (hn : NodupKeys (l ++ r)) :
    BimergeExhausts l r ∧ (bimerge l r).Perm (l ++ r) ∧
      SortedByKey (bimerge l r) ∧
      (bimerge l r).length = l.length + r.length := by
  obtain ⟨p, q, hp, hq, hpq, hu1, hu2, hu3, hu4, hu5⟩ :=
    mergeUp_spec ((l.length + r.length + 1) / 2) l r hl hr
  obtain ⟨p', q', hp', hq', hpq', hd1, hd2, hd3, hd4, hd5⟩ :=
    mergeDown_spec ((l.length + r.length) / 2) l r hl hr
  rw [Nat.min_eq_left (by omega)] at hpq
  rw [Nat.min_eq_left (by omega)] at hpq'
  have hup : ∀ u ∈ l.take p ++ r.take q,
      ∀ v ∈ l.drop p ++ r.drop q, u.1 ≤ v.1 := by
    intro u hu v hv
    exact hu5 u (hu3.mem_iff.mpr hu) v hv
  have hdown : ∀ u ∈ l.drop (l.length - p') ++ r.drop (r.length - q'),
      ∀ v ∈ l.take (l.length - p') ++ r.take (r.length - q'),
        v.1 ≤ u.1 := by
    intro u hu v hv
    exact hd5 u (hd3.mem_iff.mpr hu) v hv
  obtain ⟨hpp, hqq⟩ := merge_partition l r hn (by omega) hp hq hpq hp'
    hq' hpq' hup hdown
  have hlp : l.length - p' = p := by omega
  have hrq : r.length - q' = q := by omega
  have hlenu : (mergeUp ((l.length + r.length + 1) / 2) l r).1.length
      = p + q := by
    rw [hu3.length_eq, List.length_append, List.length_take,
      List.length_take]
    omega
  have hlend : (mergeDown ((l.length + r.length) / 2) l r).1.length
      = p' + q' := by
    rw [hd3.length_eq, List.length_append, List.length_drop,
      List.length_drop, hlp, hrq]
    omega
  have hdperm : (mergeDown ((l.length + r.length) / 2) l r).1.Perm
      (l.drop p ++ r.drop q) := by
    have := hd3
    rwa [hlp, hrq] at this
  have hperm : (bimerge l r).Perm (l ++ r) := by
    have hstep : ((l.take p ++ r.take q) ++ (l.drop p ++ r.drop q)).Perm
        ((l.take p ++ l.drop p) ++ (r.take q ++ r.drop q)) := by
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _
        (List.perm_append_comm_assoc (r.take q) (l.drop p) (r.drop q))
    have hb : (bimerge l r).Perm
        ((l.take p ++ r.take q) ++ (l.drop p ++ r.drop q)) := by
      show ((mergeUp ((l.length + r.length + 1) / 2) l r).1
        ++ (mergeDown ((l.length + r.length) / 2) l r).1).Perm _
      exact hu3.append hdperm
    refine hb.trans (hstep.trans ?_)
    rw [List.take_append_drop, List.take_append_drop]
  refine ⟨⟨?_, ?_⟩, hperm, ?_, ?_⟩
  · rw [hu1, hd1, List.length_drop, List.length_take, hlp]
    omega
  · rw [hu2, hd2, List.length_drop, List.length_take, hrq]
    omega
  · show SortedByKey ((mergeUp ((l.length + r.length + 1) / 2) l r).1
      ++ (mergeDown ((l.length + r.length) / 2) l r).1)
    refine (sortedByKey_append _ _).mpr ⟨hu4, hd4, ?_⟩
    intro x hx y hy
    exact hu5 x hx y (hdperm.mem_iff.mp hy)
  · rw [hperm.length_eq, List.length_append]

/-! ## The four facts a caller wants -/

/-- The forward half and the backward half of the merge meet exactly.
Neither half runs past the other, so both pointer tests of WAT 8632 to
8641 fail and the `call 107` of WAT 8656 is dead. -/
theorem bimerge_exhausts {l r : List (UInt32 × UInt32)}
    (hl : SortedByKey l) (hr : SortedByKey r)
    (hn : NodupKeys (l ++ r)) : BimergeExhausts l r :=
  (bimerge_facts l r hl hr hn).1

/-- The merge only reorders the entries of the two runs. -/
theorem bimerge_perm {l r : List (UInt32 × UInt32)}
    (hl : SortedByKey l) (hr : SortedByKey r)
    (hn : NodupKeys (l ++ r)) : (bimerge l r).Perm (l ++ r) :=
  (bimerge_facts l r hl hr hn).2.1

/-- The merge of two runs that are in key order is in key order. -/
theorem bimerge_sorted {l r : List (UInt32 × UInt32)}
    (hl : SortedByKey l) (hr : SortedByKey r)
    (hn : NodupKeys (l ++ r)) : SortedByKey (bimerge l r) :=
  (bimerge_facts l r hl hr hn).2.2.1

/-- The merge writes one entry for each entry of the two runs. -/
theorem bimerge_length {l r : List (UInt32 × UInt32)}
    (hl : SortedByKey l) (hr : SortedByKey r)
    (hn : NodupKeys (l ++ r)) :
    (bimerge l r).length = l.length + r.length :=
  (bimerge_facts l r hl hr hn).2.2.2

/-! ## Word and address bridges

Every lemma of this section is a copy of a private lemma of
`Project.RustHashMap.Func21Region` or of
`Project.RustHashMap.Func21Network9`, which this module cannot name.
-/

/-- `.const 4294967288` is minus eight. -/
private theorem addNegEight (x : UInt32) : x + 4294967288 = x - 8 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967288 : UInt32).toNat = 4294967288 from rfl,
    show (8 : UInt32).toNat = 8 from rfl] at *
  omega

/-- The address of entry `n + 1` is eight above the address of entry
`n`. -/
private theorem addr_succ (v : UInt32) (n : Nat) :
    v + UInt32.ofNat (8 * n) + 8 = v + UInt32.ofNat (8 * (n + 1)) := by
  have h8 : (8 : UInt32) = UInt32.ofNat 8 := rfl
  rw [show 8 * (n + 1) = 8 * n + 8 from by omega, UInt32.ofNat_add, h8,
    UInt32.add_assoc]

/-- Stepping the cursor back by one entry. -/
private theorem addr_back (v : UInt32) (n : Nat) :
    v + UInt32.ofNat (8 * (n + 1)) + 4294967288
      = v + UInt32.ofNat (8 * n) := by
  rw [← addr_succ, addNegEight, UInt32.add_sub_cancel]

/-- `i32.add` puts the second operand first. -/
private theorem addr_next (v : UInt32) (n : Nat) :
    (8 : UInt32) + (v + UInt32.ofNat (8 * n))
      = v + UInt32.ofNat (8 * (n + 1)) := by
  rw [UInt32.add_comm (8 : UInt32), addr_succ]

/-- `i32.shl` by three, after the Wasm mask. -/
private theorem shl_three (x : UInt32) : x <<< ((3 : UInt32) % 32)
    = x <<< 3 := rfl

/-- `i32.shl` of zero and of one by three. -/
private theorem shl_zero_three : (0 : UInt32) <<< (3 : UInt32) = 0 :=
  by decide

private theorem shl_one_three : (1 : UInt32) <<< (3 : UInt32) = 8 :=
  by decide

/-- A flag that the compiled code made with `i32.lt_u` or `i32.ge_u`
selects the arm that the test names. -/
private theorem select_flag {β : Type _} (P : Prop) [Decidable P]
    (x y : β) :
    (if (if P then (1 : UInt32) else 0) ≠ 0 then x else y) =
      if P then x else y := by
  by_cases h : P <;> simp [h]

/-- Move an owned double word between two names of one address. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

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
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 4 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 5 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 6 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 7 (by omega)

/-- The three address facts that `twp_load32_addr` asks for. -/
private theorem addr_facts (addr : UInt32)
    (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧
      (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- The cell of entry `i` of a buffer that does not wrap. -/
private theorem cell_facts64 (v : UInt32) (i n : Nat) (hin : i < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * i) + 0).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + (0 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * i) + 0 + 1).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 1 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 2).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 2 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 3).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 3 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 4).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 4 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 5).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 5 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 6).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 6 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 7).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 7 := by
  have hbase : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  exact offset_facts64 (v + UInt32.ofNat (8 * i)) 0 0 rfl (by omega)

/-- The key cell of entry `i` of a buffer that does not wrap. -/
private theorem cell_facts32 (v : UInt32) (i n : Nat) (hin : i < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * i) + 1).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + 1 ∧
      (v + UInt32.ofNat (8 * i) + 2).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + 2 ∧
      (v + UInt32.ofNat (8 * i) + 3).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + 3 := by
  have hbase : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  exact addr_facts (v + UInt32.ofNat (8 * i)) (by omega)

/-- Setting the one entry between two runs. -/
private theorem set_middle {β : Type} (pre : List β) (a q : β)
    (post : List β) :
    (pre ++ a :: post).set pre.length q = pre ++ q :: post := by
  induction pre with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `i32.shl` by three is a multiplication by eight. -/
private theorem shift_three (x : UInt32)
    (hbound : 8 * x.toNat < UInt32.size) :
    x <<< (3 : UInt32) = UInt32.ofNat (8 * x.toNat) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h2 : (2 : Nat) ^ 3 = 8 := by norm_num
  have hlt : x.toNat * 8 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft,
    show (3 : UInt32).toNat % 32 = 3 by decide, Nat.shiftLeft_eq, h2,
    Nat.mod_eq_of_lt hlt, UInt32.toNat_ofNat_of_lt' hbound]
  omega

/-- `i32.and` with one is the last bit. -/
private theorem and_one_toNat (x : UInt32) :
    (x &&& 1).toNat = x.toNat % 2 := by
  rw [UInt32.toNat_and, show (1 : UInt32).toNat = 1 from rfl,
    Nat.and_one_is_mod]

/-- Two buffer offsets compare the way their indexes do. -/
private theorem offset_lt (v : UInt32) (i j : Nat)
    (hi : v.toNat + i < UInt32.size) (hj : v.toNat + j < UInt32.size) :
    (v + UInt32.ofNat i < v + UInt32.ofNat j) ↔ i < j := by
  rw [UInt32.lt_iff_toNat_lt, Slices.byteOffset_toNat v i hi,
    Slices.byteOffset_toNat v j hj]
  omega

/-- Stepping a cursor forward by one entry. -/
private theorem back_forth (v : UInt32) :
    (8 : UInt32) + (v + 4294967288) = v := by
  rw [addNegEight, UInt32.add_comm, UInt32.sub_add_cancel]

/-! ## Reading and writing one entry -/

set_option maxHeartbeats 2000000 in
/-- `i64.load` of entry `k`, from the address of the entry. -/
private theorem twp_read_pair [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < ps.length) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord ps[k]) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := cell_facts64 v k n (by omega) hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hk $$ Hbuf
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord ps[k]) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %ps[k] Hcell
  isimp only [List.set_getElem_self hk] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i32.load` of the key of entry `k`, from the address of the
entry. -/
private theorem twp_read_key [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < ps.length) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i32 ps[k].1 :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load32 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := cell_facts32 v k n (by omega) hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v ps hk $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr
    ps[k].1 hfacts.1 hfacts.2.1 hfacts.2.2 with Hcell
  ihave Hbuf := Hclose $$ %ps[k].1 Hcell
  isimp only [show (ps[k].1, ps[k].2) = ps[k] from rfl,
    List.set_getElem_self hk] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.store` of a whole entry into slot `k`. -/
private theorem twp_write_pair [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)}
    {q : UInt32 × UInt32} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < ps.length) (hlen : ps.length = n)
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
  have hfacts := cell_facts64 v k n (by omega) hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hk $$ Hbuf
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord ps[k]) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %q Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

/-- A flag that the compiled code made with `i32.lt_u`, as a word. -/
private theorem select_i32 (P : Prop) [Decidable P] (x y : UInt32) :
    Value.i32 (if P then x else y)
      = if (if P then (1 : UInt32) else 0) ≠ 0 then Value.i32 x
          else Value.i32 y := by
  by_cases h : P <;> simp [h]

/-- A flag that the compiled code made with `i32.ge_u`, as a word. -/
private theorem select_i32' (P : Prop) [Decidable P] (x y : UInt32) :
    Value.i32 (if P then y else x)
      = if (if P then (0 : UInt32) else 1) ≠ 0 then Value.i32 x
          else Value.i32 y := by
  by_cases h : P <;> simp [h]

/-- `i32.shl` of a `ge_u` flag by three. -/
private theorem shl_flag (P : Prop) [Decidable P] :
    (if P then (0 : UInt32) else 1) <<< ((3 : UInt32) % 32)
      = if P then 0 else 8 := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; decide
  · rw [if_neg h, if_neg h]; decide

/-- `i32.shl` of a `lt_u` flag by three. -/
private theorem shl_flag' (P : Prop) [Decidable P] :
    (if P then (1 : UInt32) else 0) <<< ((3 : UInt32) % 32)
      = if P then 8 else 0 := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; decide
  · rw [if_neg h, if_neg h]; decide

/-- A one element list of a choice is the choice of two one element
lists. -/
private theorem singleton_if {β : Type} (P : Prop) [Decidable P]
    (x y : β) : [if P then x else y] = if P then [x] else [y] := by
  by_cases h : P <;> simp [h]

/-- `.const 4294967295` counts the turn register down. -/
private theorem index_dec (k : Nat) (hk : 1 ≤ k)
    (hb : k < UInt32.size) :
    (4294967295 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k - 1) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h1 : (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' hb
  have h2 : (UInt32.ofNat (k - 1)).toNat = k - 1 :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, h1, h2,
    show (4294967295 : UInt32).toNat = 4294967295 from rfl]
  omega

/-- A small count is not the word zero. -/
private theorem ofNat_ne_zero (k : Nat) (hk : 1 ≤ k)
    (hb : k < UInt32.size) : UInt32.ofNat k ≠ 0 := by
  intro hc
  have h := congrArg UInt32.toNat hc
  rw [UInt32.toNat_ofNat_of_lt' hb,
    show (0 : UInt32).toNat = 0 from rfl] at h
  omega

/-! ## The two fragments as instruction lists

A proof that steps through a loop body needs the list, because the
`Func21Defs` name unfolds to a private extraction that no tactic can
reduce.  Both shape lemmas are `rfl`.
-/

/-- One turn of the merge loop, WAT 8525 to 8595. -/
@[reducible] private def mergeBody : Program :=
  [.localGet 9, .localGet 13, .localGet 6, .localGet 13, .load32 0,
    .localTee 11, .localGet 6, .load32 0, .localTee 15, .ltU,
    .localTee 14, .select, .load64 0, .store64 0,
    .localGet 10, .localGet 7, .localGet 8, .localGet 8, .load32 0,
    .localTee 3, .localGet 7, .load32 0, .localTee 2, .ltU,
    .localTee 4, .select, .load64 0, .store64 0,
    .localGet 10, .const 4294967288, .add, .localSet 10,
    .localGet 9, .const 8, .add, .localSet 9,
    .localGet 7, .const 4294967288, .const 0, .localGet 4, .select,
    .add, .localSet 7,
    .localGet 8, .const 4294967288, .const 0, .localGet 3, .localGet 2,
    .geU, .select, .add, .localSet 8,
    .localGet 6, .localGet 11, .localGet 15, .geU, .const 3, .shl,
    .add, .localSet 6,
    .localGet 13, .localGet 14, .const 3, .shl, .add, .localSet 13,
    .localGet 16, .const 4294967295, .add, .localTee 16, .br_if 0]

private theorem mergeBody_shape : qsMerge = mergeBody := rfl

/-- The odd middle, WAT 8602 to 8630. -/
@[reducible] private def oddBody : Program :=
  [.localGet 1, .const 1, .and, .eqz, .br_if 0,
    .localGet 9, .localGet 6, .localGet 13, .localGet 6, .localGet 7,
    .ltU, .localTee 10, .select, .load64 0, .store64 0,
    .localGet 13, .localGet 6, .localGet 7, .geU, .const 3, .shl,
    .add, .localSet 13,
    .localGet 6, .localGet 10, .const 3, .shl, .add, .localSet 6]

private theorem oddBody_shape : qsMergeOdd = oddBody := rfl

set_option maxHeartbeats 2000000 in
/-- The `select` of two entry addresses that feeds the `i64.load` of the
entry the test picks. -/
private theorem twp_pick_pair [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr1 addr2 : UInt32} {ps : List (UInt32 × UInt32)}
    {k1 k2 n : Nat} {P : Prop} [Decidable P]
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk1 : k1 < ps.length) (hk2 : k2 < ps.length)
    (hlen : ps.length = n) (hroom : v.toNat + 8 * n < UInt32.size)
    (h1 : addr1 = v + UInt32.ofNat (8 * k1))
    (h2 : addr2 = v + UInt32.ofNat (8 * k2)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (if P then ps[k1] else ps[k2]))
                :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 (if P then 1 else 0) :: .i32 addr2 :: .i32 addr1 ::
              values⟩,
          .select :: .load64 0 :: code, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  iapply Wasm.SmallStep.twp_select
    (selected := if P then Value.i32 addr1 else Value.i32 addr2)
    (select_flag _ _ _).symm
  by_cases h : P
  · isimp only [if_pos h] at Hcont
    isimp only [if_pos h]
    iapply twp_read_pair hk1 hlen hroom h1
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo
  · isimp only [if_neg h] at Hcont
    isimp only [if_neg h]
    iapply twp_read_pair hk2 hlen hroom h2
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo

/-! ## One step of the model -/

/-- One step of a merge that has both heads. -/
private theorem mergeTake_one_cons
    (lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool)
    (a b : UInt32 × UInt32) (xs ys : List (UInt32 × UInt32)) :
    mergeTake lt 1 (a :: xs) (b :: ys) =
      (if lt b a then [b] else [a],
        if lt b a then a :: xs else xs,
        if lt b a then ys else b :: ys) := by
  by_cases h : lt b a <;> simp [mergeTake, h]

/-- The turn after `t` turns, when the left run is empty. -/
private theorem mergeTake_succ_right
    (lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool) (t : Nat)
    (l r : List (UInt32 × UInt32)) (y : UInt32 × UInt32)
    (ys : List (UInt32 × UInt32))
    (h1 : (mergeTake lt t l r).2.1 = [])
    (h2 : (mergeTake lt t l r).2.2 = y :: ys) :
    mergeTake lt (t + 1) l r =
      ((mergeTake lt t l r).1 ++ [y], [], ys) := by
  have h := mergeTake_add lt t 1 l r
  rw [h1, h2] at h
  exact h

/-- The turn after `t` turns, when both runs still have a head. -/
private theorem mergeTake_succ_cons
    (lt : (UInt32 × UInt32) → (UInt32 × UInt32) → Bool) (t : Nat)
    (l r : List (UInt32 × UInt32)) (a b : UInt32 × UInt32)
    (xs ys : List (UInt32 × UInt32))
    (h1 : (mergeTake lt t l r).2.1 = a :: xs)
    (h2 : (mergeTake lt t l r).2.2 = b :: ys) :
    mergeTake lt (t + 1) l r =
      ((mergeTake lt t l r).1 ++ (if lt b a then [b] else [a]),
        if lt b a then a :: xs else xs,
        if lt b a then ys else b :: ys) := by
  have h := mergeTake_add lt t 1 l r
  rw [h1, h2, mergeTake_one_cons] at h
  exact h

/-- The model forward test is the compiled forward test. -/
private theorem keyLt_if {β : Type _} (a b : UInt32 × UInt32)
    (u v : β) : (if keyLt b a then u else v)
      = if b.1 < a.1 then u else v := by
  by_cases h : b.1 < a.1
  · rw [if_pos h, if_pos (show keyLt b a = true by
      simp only [keyLt, decide_eq_true_eq]; exact h)]
  · rw [if_neg h, if_neg (show ¬ (keyLt b a = true) by
      simp only [keyLt, decide_eq_true_eq]; exact h)]

/-- The model backward test, written with `i32.lt_u`. -/
private theorem keyGt_if {β : Type _} (x y : UInt32 × UInt32)
    (u v : β) : (if keyGt y x then u else v)
      = if x.1 < y.1 then u else v := by
  by_cases h : x.1 < y.1
  · rw [if_pos h, if_pos (show keyGt y x = true by
      simp only [keyGt, decide_eq_true_eq]; exact h)]
  · rw [if_neg h, if_neg (show ¬ (keyGt y x = true) by
      simp only [keyGt, decide_eq_true_eq]; exact h)]

/-- Two distinct keys give the same arm under either strict test.  The
compiled backward step keeps the right entry on a tie and the model
keeps the left one, and `NodupKeys` rules a tie out. -/
private theorem flip_if {β : Type _} (x y : UInt32) (hne : x ≠ y)
    (u v : β) : (if y < x then u else v) = (if x < y then v else u) := by
  by_cases h : x < y
  · rw [if_pos h, if_neg (UInt32.not_lt.mpr (UInt32.le_of_lt h))]
  · have h2 : y.toNat ≤ x.toNat :=
      UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h)
    have h4 : x.toNat ≠ y.toNat := fun hc => hne (UInt32.toNat_inj.mp hc)
    rw [if_pos (UInt32.lt_iff_toNat_lt.mpr (by omega)), if_neg h]

/-- `i32.ge_u` is the negation of `i32.lt_u`. -/
private theorem ge_if {β : Type _} (a b : UInt32) (u v : β) :
    (if b ≥ a then u else v) = (if b < a then v else u) := by
  by_cases h : b < a
  · rw [if_pos h, if_neg (UInt32.not_le.mpr h)]
  · rw [if_neg h, if_pos (UInt32.not_lt.mp h)]

/-- The head of a suffix is the entry at that index. -/
private theorem getElem_of_drop (l : List (UInt32 × UInt32)) {k : Nat}
    {a : UInt32 × UInt32} {xs : List (UInt32 × UInt32)}
    (h : l.drop k = a :: xs) : ∃ hk : k < l.length, l[k] = a := by
  have hk : k < l.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hc)] at h
    exact List.cons_ne_nil a xs h.symm
  refine ⟨hk, ?_⟩
  have h2 := List.drop_eq_getElem_cons hk
  rw [h] at h2
  exact (List.cons.inj h2).1.symm

/-- The rests of the backward half, before the reverse. -/
private theorem mergeTakeGt_spec (n : Nat)
    (l r : List (UInt32 × UInt32)) (hl : SortedByKey l)
    (hr : SortedByKey r) :
    ∃ a b : Nat, a ≤ l.length ∧ b ≤ r.length ∧
      a + b = min n (l.length + r.length) ∧
      (mergeTake keyGt n l.reverse r.reverse).2.1 = l.reverse.drop a ∧
      (mergeTake keyGt n l.reverse r.reverse).2.2 = r.reverse.drop b := by
  have hlr : l.reverse.Pairwise (fun a b => b.1 ≤ a.1) :=
    List.pairwise_reverse.mpr hl
  have hrr : r.reverse.Pairwise (fun a b => b.1 ≤ a.1) :=
    List.pairwise_reverse.mpr hr
  obtain ⟨a, b, ha, hb, hab, h1, h2, _, _, _⟩ :=
    mergeTake_spec (R := fun a b => b.1 ≤ a.1) (lt := keyGt)
      (fun _ _ _ hab hbc => UInt32.le_trans hbc hab)
      (fun x y h => UInt32.le_of_lt (by
        simpa only [keyGt, decide_eq_true_eq] using h))
      (fun x y h => by
        have h' : ¬ (x.1 < y.1) := by
          simpa only [keyGt, decide_eq_false_iff_not] using h
        exact UInt32.not_lt.mp h')
      n l.reverse r.reverse hlr hrr
  simp only [List.length_reverse] at ha hb hab
  exact ⟨a, b, ha, hb, hab, h1, h2⟩

/-- The entry of the buffer that a backward cursor points at. -/
private theorem getElem_reverse_drop (l : List (UInt32 × UInt32))
    {c : Nat} {x : UInt32 × UInt32} {xs : List (UInt32 × UInt32)}
    (h : l.reverse.drop c = x :: xs) :
    ∃ hk : l.length - c - 1 < l.length, l[l.length - c - 1] = x := by
  obtain ⟨hc, hget⟩ := getElem_of_drop l.reverse h
  rw [List.length_reverse] at hc
  have hk : l.length - c - 1 < l.length := by omega
  refine ⟨hk, ?_⟩
  rw [← hget, List.getElem_reverse]
  congr 1
  omega

/-! ## The state of the merge loop

The merge loop keeps seven cursors.  Local 6 and local 13 walk the two
runs from the front and feed the forward half.  Local 7 and local 8 walk
them from the back and feed the backward half.  Local 9 and local 10 are
the two output cursors in the frame, and local 16 counts the turns down.
Every one of the seven is a function of the turn number and of what is
left of the two runs, so `mergeLoc` names them once.

The two backward cursors point one entry below the run base when the run
is empty from the back, which is why they are written with the word
`4294967288` and never with a subtraction on `Nat`.
-/

/-- The locals of the merge loop.  `lu` and `ru` are what is left of the
two runs from the front, and `dl` and `dr` are what is left of them from
the back, each written back to front. -/
@[reducible] private def mergeLoc (buf len fp : UInt32) (m : Nat)
    (nt : NetScratch) (r11 : UInt32) (r12 : UInt64)
    (r15 r16 r17 r18 : UInt32) (t : Nat)
    (lu ru dl dr : List (UInt32 × UInt32)) : Locals :=
  rLoc buf len fp nt
    (buf + UInt32.ofNat (8 * (m - lu.length)))
    (buf + UInt32.ofNat (8 * dl.length) + 4294967288)
    (buf + UInt32.ofNat (8 * (m + dr.length)) + 4294967288)
    (fp + UInt32.ofNat (8 * t))
    (fp + UInt32.ofNat (8 * (len.toNat - t)) + 4294967288)
    r11 r12
    (buf + UInt32.ofNat (8 * (len.toNat - ru.length)))
    r15 r16 r17 r18 []

/-- The registers that one turn of the merge loop overwrites. -/
@[reducible] private def mergeNext (nt : NetScratch)
    (k2 k3 k4 k14 : UInt32) : NetScratch :=
  { nt with r2 := k2, r3 := k3, r4 := k4, r14 := k14 }

/-- The index of the merge loop family: the turn number, what is left of
the two runs on each side, and the four registers that one turn writes
and the next turn reads back. -/
private structure MergeIx where
  t : Nat
  lu : List (UInt32 × UInt32)
  ru : List (UInt32 × UInt32)
  dl : List (UInt32 × UInt32)
  dr : List (UInt32 × UInt32)
  nt : NetScratch
  r11 : UInt32
  r15 : UInt32

/-- Where the merge loop leaves the machine: at WAT 8597, with the
forward half and the backward half both `m` entries long and the gap
between them `len - 2 * m` entries wide. -/
private def mergeExit [WasmSmallStepGS hlc Universal.State]
    (buf len fp : UInt32) (m : Nat) (L Rt : List (UInt32 × UInt32))
    (Rest : HeapIProp) (r12 : UInt64) (r17 r18 : UInt32) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ nt' : NetScratch, ∀ y11 : UInt32, ∀ y15 : UInt32,
    ∀ upAcc : List (UInt32 × UInt32),
    ∀ dAcc : List (UInt32 × UInt32),
    ∀ mid : List (UInt32 × UInt32),
    ∀ lu : List (UInt32 × UInt32),
    ∀ ru : List (UInt32 × UInt32),
    ∀ dl : List (UInt32 × UInt32),
    ∀ dr : List (UInt32 × UInt32),
    ⌜mergeTake keyLt m L Rt = (upAcc, lu, ru) ∧
      mergeTake keyGt m L.reverse Rt.reverse = (dAcc, dl, dr) ∧
      mid.length = len.toNat - 2 * m⌝ -∗
    (Table.PairSlice 0 buf (L ++ Rt) ∗
      Table.PairSlice 0 fp (upAcc ++ mid ++ dAcc.reverse) ∗ Rest -∗
      WP (.running ⟨mergeLoc buf len fp m nt' y11 r12 y15 0 r17 r18 m
            lu ru dl dr,
          qsAfterMerge, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Phi }]))

/-- The invariant of the merge loop at turn `i.t`.  The buffer is
unchanged, the frame holds the forward half, a gap and the backward
half, and the four rests of `i` are the rests of the model. -/
private def mergeInv [WasmSmallStepGS hlc Universal.State]
    (buf len fp : UInt32) (m : Nat) (L Rt : List (UInt32 × UInt32))
    (Rest exit : HeapIProp) (i : MergeIx) : HeapIProp :=
  iprop(∃ upAcc : List (UInt32 × UInt32),
    ∃ dAcc : List (UInt32 × UInt32),
    ∃ mid : List (UInt32 × UInt32),
    ⌜mergeTake keyLt i.t L Rt = (upAcc, i.lu, i.ru) ∧
      mergeTake keyGt i.t L.reverse Rt.reverse = (dAcc, i.dl, i.dr) ∧
      i.t < m ∧ mid.length = len.toNat - 2 * i.t⌝ ∗
    Table.PairSlice 0 buf (L ++ Rt) ∗
    Table.PairSlice 0 fp (upAcc ++ mid ++ dAcc.reverse) ∗ Rest ∗ exit)

/-! ## The merge loop, WAT 8524 to 8595 -/

set_option maxHeartbeats 2000000 in
/-- The merge loop, WAT 8524 to 8595.  One turn takes one entry off the
two fronts and writes it up from the frame base, and one entry off the
two backs and writes it down from the frame end.  The loop makes `m`
turns and leaves at WAT 8597. -/
private theorem twp_merge_loop [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {r11 r15 r17 r18 : UInt32} {r12 : UInt64}
    {L Rt scratch : List (UInt32 × UInt32)} {m : Nat}
    {Rest : HeapIProp} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hm : m = len.toNat / 2) (hlow : 18 ≤ len.toNat)
    (hhigh : len.toNat ≤ 32)
    (hL : L.length = m) (hRt : Rt.length = len.toNat - m)
    (hsL : Table.SortedByKey L) (hsRt : Table.SortedByKey Rt)
    (hn : NodupKeys (L ++ Rt))
    (hbuf : buf.toNat + 8 * len.toNat < UInt32.size)
    (hfp : fp.toNat + 8 * len.toNat < UInt32.size)
    (hscratch : scratch.length = len.toNat) :
    iprop(Table.PairSlice 0 buf (L ++ Rt) ∗
      Table.PairSlice 0 fp scratch ∗ Rest ∗
      mergeExit buf len fp m L Rt Rest r12 r17 r18 arity remainder
        controls calls s E Φ) ⊢
      WP (.running ⟨mergeLoc buf len fp m nt r11 r12 r15
            (UInt32.ofNat m) r17 r18 0 L Rt L.reverse Rt.reverse,
          .loop 0 0 qsMerge :: qsAfterMerge, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hm9 : 9 ≤ m := by omega
  have hmhalf : 2 * m ≤ len.toNat := by omega
  iintro ⟨Hbuf, Hfr, HRest, Hexit⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := MergeIx)
    (measure := fun i => m - i.t)
    (locals := fun i => mergeLoc buf len fp m i.nt i.r11 r12 i.r15
      (UInt32.ofNat (m - i.t)) r17 r18 i.t i.lu i.ru i.dl i.dr)
    (I := fun i => mergeInv buf len fp m L Rt Rest
      (mergeExit buf len fp m L Rt Rest r12 r17 r18 arity remainder
        controls calls s E Φ) i)
    (initial := ⟨0, L, Rt, L.reverse, Rt.reverse, nt, r11, r15⟩)
    (initialLocals := mergeLoc buf len fp m nt r11 r12 r15
      (UInt32.ofNat m) r17 r18 0 L Rt L.reverse Rt.reverse)
    rfl rfl
  · intro i
    obtain ⟨t, lu, ru, dl, dr, nti, y11, y15⟩ := i
    iintro Hrec Hinv
    isimp only [mergeInv] at Hinv
    icases Hinv with
      ⟨%upAcc, %dAcc, %mid, %hpure, Hbuf, Hfr, HRest, Hexit⟩
    obtain ⟨hupe, hdne, htm, hmidlen⟩ := hpure
    -- what the model leaves of the two runs after `t` turns
    obtain ⟨a, b, ha, hb, hab, hu1, hu2, hu3, _, _⟩ :=
      mergeUp_spec t L Rt hsL hsRt
    obtain ⟨c, d, hc, hd, hcd, hv1, hv2⟩ :=
      mergeTakeGt_spec t L Rt hsL hsRt
    have hlen2 : L.length + Rt.length = len.toNat := by omega
    have habt : a + b = t := by
      rw [hlen2, Nat.min_eq_left (by omega)] at hab; exact hab
    have hcdt : c + d = t := by
      rw [hlen2, Nat.min_eq_left (by omega)] at hcd; exact hcd
    have hlu : lu = L.drop a := by
      have h : (mergeTake keyLt t L Rt).2.1 = L.drop a := hu1
      rw [hupe] at h; exact h
    have hru : ru = Rt.drop b := by
      have h : (mergeTake keyLt t L Rt).2.2 = Rt.drop b := hu2
      rw [hupe] at h; exact h
    have hdl : dl = L.reverse.drop c := by rw [← hv1, hdne]
    have hdr : dr = Rt.reverse.drop d := by rw [← hv2, hdne]
    have hupacc : upAcc.length = t := by
      have h : (mergeTake keyLt t L Rt).1.Perm (L.take a ++ Rt.take b) :=
        hu3
      rw [hupe] at h
      rw [h.length_eq, List.length_append, List.length_take,
        List.length_take]
      omega
    have hlulen : lu.length = m - a := by
      rw [hlu, List.length_drop, hL]
    have hrulen : ru.length = len.toNat - m - b := by
      rw [hru, List.length_drop, hRt]
    have hdllen : dl.length = m - c := by
      rw [hdl, List.length_drop, List.length_reverse, hL]
    have hdrlen : dr.length = len.toNat - m - d := by
      rw [hdr, List.length_drop, List.length_reverse, hRt]
    -- the four entries that this turn reads
    have hlune : lu ≠ [] := by
      intro hcn
      have h0 : lu.length = 0 := by rw [hcn]; rfl
      omega
    have hrune : ru ≠ [] := by
      intro hcn
      have h0 : ru.length = 0 := by rw [hcn]; rfl
      omega
    have hdlne : dl ≠ [] := by
      intro hcn
      have h0 : dl.length = 0 := by rw [hcn]; rfl
      omega
    have hdrne : dr ≠ [] := by
      intro hcn
      have h0 : dr.length = 0 := by rw [hcn]; rfl
      omega
    obtain ⟨A, lu1, hAc⟩ := List.exists_cons_of_ne_nil hlune
    obtain ⟨B, ru1, hBc⟩ := List.exists_cons_of_ne_nil hrune
    obtain ⟨X, dl1, hXc⟩ := List.exists_cons_of_ne_nil hdlne
    obtain ⟨Y, dr1, hYc⟩ := List.exists_cons_of_ne_nil hdrne
    have hPlen : (L ++ Rt).length = len.toNat := by
      rw [List.length_append]; omega
    have hiA : a < (L ++ Rt).length := by omega
    have hiB : m + b < (L ++ Rt).length := by omega
    have hiX : m - c - 1 < (L ++ Rt).length := by omega
    have hiY : len.toNat - d - 1 < (L ++ Rt).length := by omega
    have hAe : (L ++ Rt)[a] = A := by
      obtain ⟨_, h⟩ := getElem_of_drop L
        (show L.drop a = A :: lu1 by rw [← hlu, hAc])
      rw [List.getElem_append_left (show a < L.length by omega)]
      exact h
    have hBe : (L ++ Rt)[m + b] = B := by
      obtain ⟨_, h⟩ := getElem_of_drop Rt
        (show Rt.drop b = B :: ru1 by rw [← hru, hBc])
      rw [List.getElem_append_right (show L.length ≤ m + b by omega)]
      simp only [show m + b - L.length = b from by omega]
      exact h
    have hXe : (L ++ Rt)[m - c - 1] = X := by
      obtain ⟨_, h⟩ := getElem_reverse_drop L
        (show L.reverse.drop c = X :: dl1 by rw [← hdl, hXc])
      rw [List.getElem_append_left (show m - c - 1 < L.length by omega)]
      simp only [show m - c - 1 = L.length - c - 1 from by omega]
      exact h
    have hYe : (L ++ Rt)[len.toNat - d - 1] = Y := by
      obtain ⟨_, h⟩ := getElem_reverse_drop Rt
        (show Rt.reverse.drop d = Y :: dr1 by rw [← hdr, hYc])
      rw [List.getElem_append_right
        (show L.length ≤ len.toNat - d - 1 by omega)]
      simp only [show len.toNat - d - 1 - L.length = Rt.length - d - 1
        from by omega]
      exact h
    have hXmem : X ∈ L := by
      rw [show X = L[m - c - 1]'(by omega) from by
        rw [← hXe, List.getElem_append_left (by omega)]]
      exact List.getElem_mem _
    have hYmem : Y ∈ Rt := by
      rw [show Y = Rt[Rt.length - d - 1]'(by omega) from by
        rw [← hYe, List.getElem_append_right (by omega)]
        simp only [show len.toNat - d - 1 - L.length = Rt.length - d - 1
          from by omega]]
      exact List.getElem_mem _
    have hXY : X.1 ≠ Y.1 := key_ne L Rt hn hXmem hYmem
    -- the seven cursors, written as indexes into the buffer
    have h6 : buf + UInt32.ofNat (8 * (m - lu.length))
        = buf + UInt32.ofNat (8 * a) := by
      rw [hlulen, show m - (m - a) = a from by omega]
    have h13 : buf + UInt32.ofNat (8 * (len.toNat - ru.length))
        = buf + UInt32.ofNat (8 * (m + b)) := by
      rw [hrulen,
        show len.toNat - (len.toNat - m - b) = m + b from by omega]
    have h7 : buf + UInt32.ofNat (8 * dl.length) + 4294967288
        = buf + UInt32.ofNat (8 * (m - c - 1)) := by
      rw [hdllen, show m - c = (m - c - 1) + 1 from by omega]
      exact addr_back buf (m - c - 1)
    have h8 : buf + UInt32.ofNat (8 * (m + dr.length)) + 4294967288
        = buf + UInt32.ofNat (8 * (len.toNat - d - 1)) := by
      rw [hdrlen,
        show m + (len.toNat - m - d) = (len.toNat - d - 1) + 1 from by
          omega]
      exact addr_back buf (len.toNat - d - 1)
    have h10 : fp + UInt32.ofNat (8 * (len.toNat - t)) + 4294967288
        = fp + UInt32.ofNat (8 * (len.toNat - t - 1)) := by
      rw [show len.toNat - t = (len.toNat - t - 1) + 1 from by omega]
      exact addr_back fp (len.toNat - t - 1)
    -- the gap between the two halves holds at least two entries
    have hmidne : mid ≠ [] := by
      intro hcn
      have h0 : mid.length = 0 := by rw [hcn]; rfl
      omega
    obtain ⟨M0, midr, hM0⟩ := List.exists_cons_of_ne_nil hmidne
    have hmidrlen : midr.length = len.toNat - 2 * t - 1 := by
      have h0 : mid.length = midr.length + 1 := by rw [hM0]; rfl
      omega
    have hmidrne : midr ≠ [] := by
      intro hcn
      have h0 : midr.length = 0 := by rw [hcn]; rfl
      omega
    obtain ⟨mid1, Mlast, hMl⟩ :
        ∃ mid1 Mlast, midr = mid1 ++ [Mlast] := by
      rcases List.eq_nil_or_concat midr with hnil | ⟨l', e, he⟩
      · exact absurd hnil hmidrne
      · exact ⟨l', e, by rw [he, List.concat_eq_append]⟩
    have hmid1len : mid1.length = len.toNat - 2 * (t + 1) := by
      have h0 : midr.length = mid1.length + 1 := by
        rw [hMl, List.length_append]; rfl
      omega
    have hdacc : dAcc.length = t := by
      have h : (mergeTake keyGt t L.reverse Rt.reverse).1.length
          = min t (L.reverse.length + Rt.reverse.length) :=
        mergeTake_taken_length keyGt t L.reverse Rt.reverse
      rw [hdne] at h
      simp only [List.length_reverse] at h
      rw [h, hlen2, Nat.min_eq_left (by omega)]
    have hfrlen : (upAcc ++ mid ++ dAcc.reverse).length = len.toNat := by
      rw [List.length_append, List.length_append, List.length_reverse,
        hupacc, hdacc, hmidlen]
      omega
    -- WAT 8525 to 8538: one entry off the two fronts
    simp only [Wasm.SmallStep.loopBodyExpr, mergeBody_shape, mergeBody,
      mergeLoc, rLoc, qsLocals]
    isimp only [h6, h7, h8, h10, h13]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet
      twp_localGet]
    iapply twp_read_key (ps := L ++ Rt) (k := m + b) (n := len.toNat)
      hiB hPlen hbuf rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hBe]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    iapply twp_read_key (ps := L ++ Rt) (k := a) (n := len.toNat)
      hiA hPlen hbuf rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hAe]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_ltU
      (result := if B.1 < A.1 then 1 else 0) rfl
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_pick_pair (ps := L ++ Rt) (k1 := m + b) (k2 := a)
      (n := len.toNat) (P := B.1 < A.1) hiB hiA hPlen hbuf rfl rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hAe, hBe]
    -- WAT 8538: the forward entry goes to the frame base side
    have hfa : (upAcc ++ (M0 :: (mid1 ++ [Mlast]))) ++ dAcc.reverse
        = upAcc ++ M0 :: ((mid1 ++ [Mlast]) ++ dAcc.reverse) := by
      simp only [List.append_assoc, List.cons_append]
    have hset1 : ∀ q : UInt32 × UInt32,
        (upAcc ++ M0 :: ((mid1 ++ [Mlast]) ++ dAcc.reverse)).set t q
          = (upAcc ++ q :: mid1) ++ Mlast :: dAcc.reverse := by
      intro q
      have hs := set_middle upAcc M0 q (mid1 ++ [Mlast] ++ dAcc.reverse)
      rw [hupacc] at hs
      rw [hs]
      simp
    have hfrlen2 : ∀ q1 : UInt32 × UInt32,
        ((upAcc ++ q1 :: mid1) ++ Mlast :: dAcc.reverse).length
          = len.toNat := by
      intro q1
      simp only [List.length_append, List.length_cons,
        List.length_reverse, hupacc, hdacc, hmid1len]
      omega
    have hset2 : ∀ q1 q2 : UInt32 × UInt32,
        ((upAcc ++ q1 :: mid1) ++ Mlast :: dAcc.reverse).set
            (len.toNat - t - 1) q2
          = (upAcc ++ [q1]) ++ mid1 ++ (dAcc ++ [q2]).reverse := by
      intro q1 q2
      have hs := set_middle (upAcc ++ q1 :: mid1) Mlast q2 dAcc.reverse
      rw [show (upAcc ++ q1 :: mid1).length = len.toNat - t - 1 from by
        simp only [List.length_append, List.length_cons, hupacc,
          hmid1len]
        omega] at hs
      rw [hs]
      simp
    isimp only [hM0, hMl, hfa] at Hfr
    iapply twp_write_pair (ps :=
      upAcc ++ M0 :: ((mid1 ++ [Mlast]) ++ dAcc.reverse)) (k := t)
      (n := len.toNat) (by rw [← hfa, ← hMl, ← hM0]; omega)
      (by rw [← hfa, ← hMl, ← hM0]; exact hfrlen) hfp rfl
    isplitl_exact Hfr
    iintro Hfr
    isimp only [hset1] at Hfr
    -- WAT 8539 to 8552: one entry off the two backs
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet
      twp_localGet]
    iapply twp_read_key (ps := L ++ Rt) (k := len.toNat - d - 1)
      (n := len.toNat) hiY hPlen hbuf rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hYe]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    iapply twp_read_key (ps := L ++ Rt) (k := m - c - 1)
      (n := len.toNat) hiX hPlen hbuf rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hXe]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_ltU
      (result := if Y.1 < X.1 then 1 else 0) rfl
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_pick_pair (ps := L ++ Rt) (k1 := m - c - 1)
      (k2 := len.toNat - d - 1) (n := len.toNat) (P := Y.1 < X.1)
      hiX hiY hPlen hbuf rfl rfl
    isplitl_exact Hbuf
    iintro Hbuf
    isimp only [hXe, hYe]
    -- WAT 8552: the backward entry goes to the frame end side
    iapply twp_write_pair
      (ps := (upAcc ++ (if B.1 < A.1 then B else A) :: mid1)
        ++ Mlast :: dAcc.reverse)
      (k := len.toNat - t - 1) (n := len.toNat)
      (by rw [hfrlen2]; omega) (by rw [hfrlen2]) hfp rfl
    isplitl_exact Hfr
    iintro Hfr
    isimp only [hset2] at Hfr
    -- WAT 8553 to 8594: the seven cursors step
    wasm_twp_pures [twp_localGet twp_const twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
    iapply Wasm.SmallStep.twp_select
      (selected := Value.i32 (if Y.1 < X.1 then 4294967288 else 0))
      (select_i32 _ _ _)
    wasm_twp_pures [twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet
      twp_localGet]
    iapply Wasm.SmallStep.twp_geU
      (result := if Y.1 < X.1 then 0 else 1) (ge_if X.1 Y.1 1 0).symm
    iapply Wasm.SmallStep.twp_select
      (selected := Value.i32 (if Y.1 < X.1 then 0 else 4294967288))
      (select_i32' _ _ _)
    wasm_twp_pures [twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    iapply Wasm.SmallStep.twp_geU
      (result := if B.1 < A.1 then 0 else 1) (ge_if A.1 B.1 1 0).symm
    wasm_twp_pures [twp_const twp_shl]
    isimp only [shl_flag]
    wasm_twp_pures [twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    isimp only [shl_flag']
    wasm_twp_pures [twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [index_dec (m - t) (by omega) (by omega)]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    -- the model after one more turn
    have hstepU := mergeTake_succ_cons keyLt t L Rt A B lu1 ru1
      (by rw [hupe]; exact hAc) (by rw [hupe]; exact hBc)
    have hstepD := mergeTake_succ_cons keyGt t L.reverse Rt.reverse X Y
      dl1 dr1 (by rw [hdne]; exact hXc) (by rw [hdne]; exact hYc)
    have hlu1len : lu1.length = m - a - 1 := by
      have h0 : lu.length = lu1.length + 1 := by rw [hAc]; rfl
      omega
    have hru1len : ru1.length = len.toNat - m - b - 1 := by
      have h0 : ru.length = ru1.length + 1 := by rw [hBc]; rfl
      omega
    have hdl1len : dl1.length = m - c - 1 := by
      have h0 : dl.length = dl1.length + 1 := by rw [hXc]; rfl
      omega
    have hdr1len : dr1.length = len.toNat - m - d - 1 := by
      have h0 : dr.length = dr1.length + 1 := by rw [hYc]; rfl
      omega
    -- the seven cursors of the next turn
    have e6 : (if B.1 < A.1 then (0 : UInt32) else 8)
          + (buf + UInt32.ofNat (8 * a))
        = buf + UInt32.ofNat
            (8 * (m - (mergeTake keyLt (t + 1) L Rt).2.1.length)) := by
      rw [hstepU]
      simp only [keyLt_if]
      by_cases hp : B.1 < A.1
      · rw [if_pos hp, if_pos hp, List.length_cons, hlu1len,
          show m - (m - a - 1 + 1) = a from by omega]
        exact UInt32.zero_add _
      · rw [if_neg hp, if_neg hp, hlu1len,
          show m - (m - a - 1) = a + 1 from by omega]
        exact addr_next buf a
    have e13 : (if B.1 < A.1 then (8 : UInt32) else 0)
          + (buf + UInt32.ofNat (8 * (m + b)))
        = buf + UInt32.ofNat
            (8 * (len.toNat
              - (mergeTake keyLt (t + 1) L Rt).2.2.length)) := by
      rw [hstepU]
      simp only [keyLt_if]
      by_cases hp : B.1 < A.1
      · rw [if_pos hp, if_pos hp, hru1len,
          show len.toNat - (len.toNat - m - b - 1) = m + b + 1 from by
            omega]
        exact addr_next buf (m + b)
      · rw [if_neg hp, if_neg hp, List.length_cons, hru1len,
          show len.toNat - (len.toNat - m - b - 1 + 1) = m + b from by
            omega]
        exact UInt32.zero_add _
    have e7 : (if Y.1 < X.1 then (4294967288 : UInt32) else 0)
          + (buf + UInt32.ofNat (8 * (m - c - 1)))
        = buf + UInt32.ofNat
            (8 * (mergeTake keyGt (t + 1) L.reverse Rt.reverse).2.1.length)
          + 4294967288 := by
      rw [hstepD]
      simp only [keyGt_if, ← flip_if X.1 Y.1 hXY dl1 (X :: dl1)]
      by_cases hq : Y.1 < X.1
      · rw [if_pos hq, if_pos hq, hdl1len]
        exact UInt32.add_comm _ _
      · rw [if_neg hq, if_neg hq, List.length_cons, hdl1len,
          show m - c - 1 + 1 = m - c from by omega,
          show m - c = (m - c - 1) + 1 from by omega,
          addr_back buf (m - c - 1)]
        exact UInt32.zero_add _
    have e8 : (if Y.1 < X.1 then (0 : UInt32) else 4294967288)
          + (buf + UInt32.ofNat (8 * (len.toNat - d - 1)))
        = buf + UInt32.ofNat
            (8 * (m + (mergeTake keyGt (t + 1) L.reverse
              Rt.reverse).2.2.length)) + 4294967288 := by
      rw [hstepD]
      simp only [keyGt_if, ← flip_if X.1 Y.1 hXY (Y :: dr1) dr1]
      by_cases hq : Y.1 < X.1
      · rw [if_pos hq, if_pos hq, List.length_cons, hdr1len,
          show m + (len.toNat - m - d - 1 + 1) = (len.toNat - d - 1) + 1
            from by omega, addr_back buf (len.toNat - d - 1)]
        exact UInt32.zero_add _
      · rw [if_neg hq, if_neg hq, hdr1len,
          show m + (len.toNat - m - d - 1) = len.toNat - d - 1 from by
            omega]
        exact UInt32.add_comm _ _
    have e9 : (8 : UInt32) + (fp + UInt32.ofNat (8 * t))
        = fp + UInt32.ofNat (8 * (t + 1)) := addr_next fp t
    have e10 : (4294967288 : UInt32)
          + (fp + UInt32.ofNat (8 * (len.toNat - t - 1)))
        = fp + UInt32.ofNat (8 * (len.toNat - (t + 1))) + 4294967288 :=
      UInt32.add_comm _ _
    have hfrm : upAcc ++ [if B.1 < A.1 then B else A] ++ mid1
          ++ (dAcc ++ [if Y.1 < X.1 then X else Y]).reverse
        = (mergeTake keyLt (t + 1) L Rt).1 ++ mid1
          ++ (mergeTake keyGt (t + 1) L.reverse Rt.reverse).1.reverse := by
      rw [hstepU, hstepD]
      simp only [hupe, hdne, keyLt_if, keyGt_if, singleton_if,
        flip_if X.1 Y.1 hXY [X] [Y]]
    isimp only [e6, e7, e8, e9, e10, e13]
    isimp only [hfrm] at Hfr
    by_cases hlast : t + 1 = m
    · -- WAT 8595: the last turn falls through to the middle
      isimp only [show UInt32.ofNat (m - t - 1) = (0 : UInt32) from by
        rw [show m - t - 1 = 0 from by omega]; rfl]
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      rw [hlast]
      isimp only [mergeExit] at Hexit
      ihave Hgo := Hexit
        $$ %(mergeNext nti X.1 Y.1 (if Y.1 < X.1 then 1 else 0)
            (if B.1 < A.1 then 1 else 0))
        %B.1 %A.1
        %(mergeTake keyLt m L Rt).1
        %(mergeTake keyGt m L.reverse Rt.reverse).1
        %mid1
        %(mergeTake keyLt m L Rt).2.1
        %(mergeTake keyLt m L Rt).2.2
        %(mergeTake keyGt m L.reverse Rt.reverse).2.1
        %(mergeTake keyGt m L.reverse Rt.reverse).2.2
        %(⟨rfl, rfl, by omega⟩ :
          mergeTake keyLt m L Rt
              = ((mergeTake keyLt m L Rt).1,
                (mergeTake keyLt m L Rt).2.1,
                (mergeTake keyLt m L Rt).2.2) ∧
            mergeTake keyGt m L.reverse Rt.reverse
              = ((mergeTake keyGt m L.reverse Rt.reverse).1,
                (mergeTake keyGt m L.reverse Rt.reverse).2.1,
                (mergeTake keyGt m L.reverse Rt.reverse).2.2) ∧
            mid1.length = len.toNat - 2 * m)
      iapply Hgo
      isplitl [Hbuf]
      · iexact Hbuf
      · isplitl [Hfr]
        · iexact Hfr
        · iexact HRest
    · -- WAT 8595: one more turn
      iapply Wasm.SmallStep.twp_brIf
        (ofNat_ne_zero (m - t - 1) (by omega) (by omega)) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hback := Hrec
        $$ %(⟨t + 1, (mergeTake keyLt (t + 1) L Rt).2.1,
            (mergeTake keyLt (t + 1) L Rt).2.2,
            (mergeTake keyGt (t + 1) L.reverse Rt.reverse).2.1,
            (mergeTake keyGt (t + 1) L.reverse Rt.reverse).2.2,
            mergeNext nti X.1 Y.1 (if Y.1 < X.1 then 1 else 0)
              (if B.1 < A.1 then 1 else 0),
            B.1, A.1⟩ : MergeIx)
        %(show m - (t + 1) < m - t by omega)
      iapply Hback
      isimp only [mergeInv]
      iexists (mergeTake keyLt (t + 1) L Rt).1
      iexists (mergeTake keyGt (t + 1) L.reverse Rt.reverse).1
      iexists mid1
      isplitl_pureexact (⟨rfl, rfl, by omega, by omega⟩ :
        mergeTake keyLt (t + 1) L Rt
            = ((mergeTake keyLt (t + 1) L Rt).1,
              (mergeTake keyLt (t + 1) L Rt).2.1,
              (mergeTake keyLt (t + 1) L Rt).2.2) ∧
          mergeTake keyGt (t + 1) L.reverse Rt.reverse
            = ((mergeTake keyGt (t + 1) L.reverse Rt.reverse).1,
              (mergeTake keyGt (t + 1) L.reverse Rt.reverse).2.1,
              (mergeTake keyGt (t + 1) L.reverse Rt.reverse).2.2) ∧
          t + 1 < m ∧ mid1.length = len.toNat - 2 * (t + 1))
      · isplitl [Hbuf]
        · iexact Hbuf
        · isplitl [Hfr]
          · iexact Hfr
          · isplitl [HRest]
            · iexact HRest
            · iexact Hexit
  · isimp only [mergeInv]
    iexists []
    iexists []
    iexists scratch
    isplitl_pureexact (show mergeTake keyLt 0 L Rt = ([], L, Rt) ∧
        mergeTake keyGt 0 L.reverse Rt.reverse
          = ([], L.reverse, Rt.reverse) ∧
        0 < m ∧ scratch.length = len.toNat - 2 * 0 from
      ⟨rfl, rfl, by omega, by omega⟩)
    · isplitl [Hbuf]
      · iexact Hbuf
      · isplitl [Hfr]
        · isimp only [List.nil_append, List.reverse_nil,
            List.append_nil]
          iexact Hfr
        · isplitl [HRest]
          · iexact HRest
          · iexact Hexit

/-! ## The odd middle, the dead checks and the copy back -/

set_option maxHeartbeats 2000000 in
/-- WAT 8597 to 8652.  An odd length moves the one entry that the loop
left, both pointer checks fail because the two halves meet, and the
frame goes back to the buffer. -/
private theorem twp_merge_tail [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {r11 r15 r17 r18 : UInt32} {r12 : UInt64}
    {L Rt upAcc dAcc mid lu ru dl dr : List (UInt32 × UInt32)}
    {m : Nat} {Rest : HeapIProp} {after : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hm : m = len.toNat / 2) (hlow : 18 ≤ len.toNat)
    (hhigh : len.toNat ≤ 32)
    (hL : L.length = m) (hRt : Rt.length = len.toNat - m)
    (hsL : Table.SortedByKey L) (hsRt : Table.SortedByKey Rt)
    (hn : NodupKeys (L ++ Rt))
    (hbuf : buf.toNat + 8 * len.toNat < UInt32.size)
    (hfp : fp.toNat + 8 * len.toNat < UInt32.size)
    (hUp : mergeTake keyLt m L Rt = (upAcc, lu, ru))
    (hDn : mergeTake keyGt m L.reverse Rt.reverse = (dAcc, dl, dr))
    (hmid : mid.length = len.toNat - 2 * m)
    (hcont : ∀ (nt' : NetScratch) (y6 y7 y8 y9 y10 y11 : UInt32)
        (y12 : UInt64) (y13 y15 y16 y17 y18 : UInt32),
      iprop(Table.PairSlice 0 buf (bimerge L Rt) ∗
        Table.PairSlice 0 fp (bimerge L Rt) ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt' y6 y7 y8 y9 y10 y11 y12 y13
            y15 y16 y17 y18 [], after, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 buf (L ++ Rt) ∗
      Table.PairSlice 0 fp (upAcc ++ mid ++ dAcc.reverse) ∗ Rest) ⊢
      WP (.running ⟨mergeLoc buf len fp m nt r11 r12 r15 0 r17 r18 m
            lu ru dl dr,
          qsAfterMerge, arity, remainder, regBlocks after controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hm9 : 9 ≤ m := by omega
  have hsum : L.length + Rt.length = len.toNat := by omega
  obtain ⟨a, b, ha, hb, hab, hu1, hu2, _, _, _⟩ :=
    mergeUp_spec m L Rt hsL hsRt
  obtain ⟨c, d, hc, hd, hcd, hv1, hv2⟩ :=
    mergeTakeGt_spec m L Rt hsL hsRt
  have habm : a + b = m := by
    rw [hsum, Nat.min_eq_left (by omega)] at hab; exact hab
  have hcdm : c + d = m := by
    rw [hsum, Nat.min_eq_left (by omega)] at hcd; exact hcd
  have hlu : lu = L.drop a := by
    have h : (mergeTake keyLt m L Rt).2.1 = L.drop a := hu1
    rw [hUp] at h; exact h
  have hru : ru = Rt.drop b := by
    have h : (mergeTake keyLt m L Rt).2.2 = Rt.drop b := hu2
    rw [hUp] at h; exact h
  have hdl : dl = L.reverse.drop c := by rw [← hv1, hDn]
  have hdr : dr = Rt.reverse.drop d := by rw [← hv2, hDn]
  have hlulen : lu.length = m - a := by rw [hlu, List.length_drop, hL]
  have hrulen : ru.length = len.toNat - m - b := by
    rw [hru, List.length_drop, hRt]
  have hdllen : dl.length = m - c := by
    rw [hdl, List.length_drop, List.length_reverse, hL]
  have hdrlen : dr.length = len.toNat - m - d := by
    rw [hdr, List.length_drop, List.length_reverse, hRt]
  have hex := bimerge_exhausts hsL hsRt hn
  simp only [BimergeExhausts, hsum, mergeDown, List.length_reverse]
    at hex
  simp only [← hm, hDn, hL, hRt, hdllen, hdrlen] at hex
  rw [qsAfterMerge_split, qsMergeMiddle_split, qsMergeAdvance_shape,
    qsPointerCheck_shape, qsCopy_shape, oddBody_shape]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  simp only [mergeLoc, rLoc, qsLocals]
  iintro ⟨Hbuf, Hfr, HRest⟩
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [back_forth]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_block twp_localGet twp_const twp_and]
  by_cases hodd : len.toNat % 2 = 1
  · -- WAT 8606: an odd length writes one more entry forward
    have hlenodd : len.toNat = 2 * m + 1 := by omega
    have hhalf : (len.toNat + 1) / 2 = m + 1 := by omega
    have hmid1 : mid.length = 1 := by omega
    have hPlen : (L ++ Rt).length = len.toNat := by
      rw [List.length_append]; omega
    have hiA : a < (L ++ Rt).length := by omega
    have hiB : m + b < (L ++ Rt).length := by omega
    have hupacc : upAcc.length = m := by
      have h := mergeTake_taken_length keyLt m L Rt
      rw [hUp] at h
      rw [h, hsum, Nat.min_eq_left (by omega)]
    have hdacc : dAcc.length = m := by
      have h := mergeTake_taken_length keyGt m L.reverse Rt.reverse
      rw [hDn] at h
      simp only [List.length_reverse] at h
      rw [h, hsum, Nat.min_eq_left (by omega)]
    obtain ⟨M0, hM0⟩ : ∃ M0 : UInt32 × UInt32, mid = [M0] := by
      cases mid with
      | nil => exact absurd hmid1 (by simp)
      | cons x xs =>
        cases xs with
        | nil => exact ⟨x, rfl⟩
        | cons y ys =>
          exact absurd hmid1 (by simp only [List.length_cons]; omega)
    have hrune : ru ≠ [] := by
      intro hcn
      have h0 : ru.length = 0 := by rw [hcn]; rfl
      omega
    obtain ⟨B, ru1, hBc⟩ := List.exists_cons_of_ne_nil hrune
    have hBe : (L ++ Rt)[m + b] = B := by
      obtain ⟨_, h⟩ := getElem_of_drop Rt
        (show Rt.drop b = B :: ru1 by rw [← hru, hBc])
      rw [List.getElem_append_right (show L.length ≤ m + b by omega)]
      simp only [show m + b - L.length = b from by omega]
      exact h
    simp only [hhalf] at hex
    have hexU : (mergeTake keyLt (m + 1) L Rt).2.1.length + (m - c) = m :=
      hex.1
    -- the model takes the middle entry from the side the code picks
    obtain ⟨hpick, hacP1, hacP2⟩ :
        (mergeTake keyLt (m + 1) L Rt).1
              = upAcc ++ [if a < m - c then (L ++ Rt)[a]'hiA
                  else (L ++ Rt)[m + b]'hiB] ∧
            (a < m - c → a + c + 1 = m) ∧
          (¬ a < m - c → a + c = m) := by
      by_cases hlune : lu = []
      · have hlu0 : lu.length = 0 := by rw [hlune]; rfl
        have hstep := mergeTake_succ_right keyLt m L Rt B ru1
          (by rw [hUp]; exact hlune) (by rw [hUp]; exact hBc)
        rw [hUp] at hstep
        have hc0 : c = 0 := by
          rw [hstep] at hexU
          simp only [List.length_nil, Nat.zero_add] at hexU
          omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hstep, if_neg (show ¬ a < m - c from by omega), hBe]
        · intro hp
          omega
        · intro _
          omega
      · obtain ⟨A, lu1, hAc⟩ := List.exists_cons_of_ne_nil hlune
        have hlu1len : lu1.length = m - a - 1 := by
          have h0 : lu.length = lu1.length + 1 := by rw [hAc]; rfl
          omega
        have halt : a < m := by
          have h0 : lu.length = lu1.length + 1 := by rw [hAc]; rfl
          omega
        have hAe : (L ++ Rt)[a] = A := by
          obtain ⟨_, h⟩ := getElem_of_drop L
            (show L.drop a = A :: lu1 by rw [← hlu, hAc])
          rw [List.getElem_append_left (show a < L.length by omega)]
          exact h
        have hstep := mergeTake_succ_cons keyLt m L Rt A B lu1 ru1
          (by rw [hUp]; exact hAc) (by rw [hUp]; exact hBc)
        rw [hUp] at hstep
        rw [hstep] at hexU
        by_cases hBA : B.1 < A.1
        · simp only [keyLt_if, if_pos hBA, List.length_cons,
            hlu1len] at hexU
          refine ⟨?_, ?_, ?_⟩
          · rw [hstep]
            simp only [keyLt_if, if_pos hBA,
              if_neg (show ¬ a < m - c from by omega), hBe]
          · intro hp
            omega
          · intro _
            omega
        · simp only [keyLt_if, if_neg hBA, hlu1len] at hexU
          refine ⟨?_, ?_, ?_⟩
          · rw [hstep]
            simp only [keyLt_if, if_neg hBA,
              if_pos (show a < m - c from by omega), hAe]
          · intro _
            omega
          · intro hp
            omega
    -- the cursors that the middle step leaves
    have e13 : (if a < m - c then (0 : UInt32) else 8)
          + (buf + UInt32.ofNat (8 * (m + b)))
        = buf + UInt32.ofNat (8 * (len.toNat - d)) := by
      by_cases hp : a < m - c
      · have h1 := hacP1 hp
        rw [if_pos hp, show len.toNat - d = m + b from by omega]
        exact UInt32.zero_add _
      · have h1 := hacP2 hp
        rw [if_neg hp, show len.toNat - d = m + b + 1 from by omega]
        exact addr_next buf (m + b)
    have e6 : (if a < m - c then (8 : UInt32) else 0)
          + (buf + UInt32.ofNat (8 * a))
        = buf + UInt32.ofNat (8 * (m - c)) := by
      by_cases hp : a < m - c
      · have h1 := hacP1 hp
        rw [if_pos hp, show m - c = a + 1 from by omega]
        exact addr_next buf a
      · have h1 := hacP2 hp
        rw [if_neg hp, show m - c = a from by omega]
        exact UInt32.zero_add _
    have h6 : buf + UInt32.ofNat (8 * (m - lu.length))
        = buf + UInt32.ofNat (8 * a) := by
      rw [hlulen, show m - (m - a) = a from by omega]
    have h7 : buf + UInt32.ofNat (8 * dl.length)
        = buf + UInt32.ofNat (8 * (m - c)) := by rw [hdllen]
    have h13 : buf + UInt32.ofNat (8 * (len.toNat - ru.length))
        = buf + UInt32.ofNat (8 * (m + b)) := by
      rw [hrulen,
        show len.toNat - (len.toNat - m - b) = m + b from by omega]
    have h8 : buf + UInt32.ofNat (8 * (m + dr.length))
        = buf + UInt32.ofNat (8 * (len.toNat - d)) := by
      rw [hdrlen,
        show m + (len.toNat - m - d) = len.toNat - d from by omega]
    have hltp : (buf + UInt32.ofNat (8 * a)
        < buf + UInt32.ofNat (8 * (m - c))) ↔ a < m - c :=
      (offset_lt buf (8 * a) (8 * (m - c)) (by omega) (by omega)).trans
        (by omega)
    have hbim : bimerge L Rt
        = upAcc ++ (if a < m - c then (L ++ Rt)[a]'hiA
            else (L ++ Rt)[m + b]'hiB) :: dAcc.reverse := by
      simp only [bimerge, hsum, hhalf, ← hm, mergeDown, hDn,
        show mergeUp (m + 1) L Rt = mergeTake keyLt (m + 1) L Rt from
          rfl,
        hpick]
      simp
    have hbimlen : (bimerge L Rt).length = len.toNat := by
      rw [bimerge_length hsL hsRt hn]; omega
    -- WAT 8606: the parity test gives one, so the middle step runs
    iapply Wasm.SmallStep.twp_eqz (result := 0)
      (by
        rw [if_neg (show (len &&& 1) ≠ (0 : UInt32) from by
          intro hcn
          have h0 : (len &&& 1).toNat = 0 := by rw [hcn]; rfl
          rw [and_one_toNat] at h0
          omega)])
    iapply Wasm.SmallStep.twp_brIfZero
    -- WAT 8607 to 8617: the middle entry goes to the frame
    isimp only [h6, h7, h8, h13]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
      twp_localGet]
    iapply Wasm.SmallStep.twp_ltU (result := if a < m - c then 1 else 0)
      (by simp only [hltp])
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_pick_pair (ps := L ++ Rt) (k1 := a) (k2 := m + b)
      (n := len.toNat) (P := a < m - c) hiA hiB hPlen hbuf rfl rfl
    isplitl_exact Hbuf
    iintro Hbuf
    have hfa : upAcc ++ ([M0] ++ dAcc.reverse)
        = upAcc ++ M0 :: dAcc.reverse := by
      simp only [List.cons_append, List.nil_append]
    have hfrlen : (upAcc ++ M0 :: dAcc.reverse).length = len.toNat := by
      simp only [List.length_append, List.length_cons,
        List.length_reverse, hupacc, hdacc]
      omega
    have hset : ∀ q : UInt32 × UInt32,
        (upAcc ++ M0 :: dAcc.reverse).set m q
          = upAcc ++ q :: dAcc.reverse := by
      intro q
      have hs := set_middle upAcc M0 q dAcc.reverse
      rw [hupacc] at hs
      exact hs
    isimp only [hM0, hfa] at Hfr
    iapply twp_write_pair (ps := upAcc ++ M0 :: dAcc.reverse) (k := m)
      (n := len.toNat) (by rw [hfrlen]; omega) hfrlen hfp rfl
    isplitl_exact Hfr
    iintro Hfr
    isimp only [hset, ← hbim] at Hfr
    -- WAT 8618 to 8630: the two cursors step over the middle entry
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    iapply Wasm.SmallStep.twp_geU (result := if a < m - c then 0 else 1)
      (by
        simp only [← hltp]
        exact (ge_if (buf + UInt32.ofNat (8 * (m - c)))
          (buf + UInt32.ofNat (8 * a)) 1 0).symm)
    wasm_twp_pures [twp_const twp_shl]
    isimp only [shl_flag]
    wasm_twp_pures [twp_add]
    isimp only [e13]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    isimp only [shl_flag']
    wasm_twp_pures [twp_add]
    isimp only [e6]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    -- WAT 8632 to 8641: both pointer checks fail
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply Wasm.SmallStep.twp_ne (result := 0)
      (by rw [if_neg (show ¬ (buf + UInt32.ofNat (8 * (m - c))
        ≠ buf + UInt32.ofNat (8 * (m - c))) from fun hcn => hcn rfl)])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    isimp only [back_forth]
    iapply Wasm.SmallStep.twp_ne (result := 0)
      (by rw [if_neg (show ¬ (buf + UInt32.ofNat (8 * (len.toNat - d))
        ≠ buf + UInt32.ofNat (8 * (len.toNat - d)))
        from fun hcn => hcn rfl)])
    iapply Wasm.SmallStep.twp_brIfZero
    -- WAT 8642 to 8647: the length is not zero
    wasm_twp_pures [twp_localGet twp_const twp_shl]
    isimp only [shl_three, shift_three len (by omega)]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_eqz (result := 0)
      (by rw [if_neg (ofNat_ne_zero (8 * len.toNat) (by omega)
        (by omega))])
    iapply Wasm.SmallStep.twp_brIfZero
    -- WAT 8648 to 8651: the frame goes back to the buffer
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    ihave Hbuf := (Table.PairSlice_forget 0 buf (L ++ Rt)).mp $$ Hbuf
    ihave Hfr := (Table.PairSlice_forget 0 fp (bimerge L Rt)).mp $$ Hfr
    iapply Wasm.SmallStep.twp_memoryCopy32_slices
      (Table.pairBytes (L ++ Rt)) (Table.pairBytes (bimerge L Rt))
      (by
        rw [Table.pairBytes_length, List.length_append,
          UInt32.toNat_ofNat_of_lt'
            (show 8 * len.toNat < UInt32.size by omega)]
        omega)
      (by
        rw [Table.pairBytes_length, hbimlen,
          UInt32.toNat_ofNat_of_lt'
            (show 8 * len.toNat < UInt32.size by omega)])
      (by
        rw [UInt32.toNat_ofNat_of_lt'
          (show 8 * len.toNat < UInt32.size by omega)]
        omega)
      $$ Hfr Hbuf
    iintro Hfr Hbuf
    ihave Hfr := (Table.PairSlice_forget 0 fp (bimerge L Rt)).mpr
      $$ Hfr
    ihave Hbuf := (Table.PairSlice_forget 0 buf (bimerge L Rt)).mpr
      $$ Hbuf
    -- WAT 8652: leave the body
    iapply Wasm.SmallStep.twp_br rfl
    simp only [qsFrame, List.take_zero, List.nil_append]
    iapply hcont
    isplitl [Hbuf]
    · iexact Hbuf
    · isplitl [Hfr]
      · iexact Hfr
      · iexact HRest
  · -- WAT 8606: an even length skips the middle entry
    have heven : len.toNat = 2 * m := by omega
    have hhalf : (len.toNat + 1) / 2 = m := by omega
    simp only [hhalf, show mergeUp m L Rt = (upAcc, lu, ru) from hUp,
      hlulen, hrulen] at hex
    have hmid0 : mid = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    have hac : a + c = m := by omega
    have hbd : b + d = len.toNat - m := by omega
    iapply Wasm.SmallStep.twp_eqz (result := 1)
      (by
        rw [if_pos (show (len &&& 1) = (0 : UInt32) from by
          apply UInt32.toNat_inj.mp
          rw [and_one_toNat, show (0 : UInt32).toNat = 0 from rfl]
          omega)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hbim : bimerge L Rt = upAcc ++ dAcc.reverse := by
      simp only [bimerge, hsum, hhalf, ← hm, mergeDown,
        show mergeUp m L Rt = (upAcc, lu, ru) from hUp, hDn]
    have hbimlen : (bimerge L Rt).length = len.toNat := by
      rw [bimerge_length hsL hsRt hn]; omega
    have h67 : buf + UInt32.ofNat (8 * (m - lu.length))
        = buf + UInt32.ofNat (8 * dl.length) := by
      rw [hlulen, hdllen, show m - (m - a) = m - c from by omega]
    have h138 : buf + UInt32.ofNat (8 * (len.toNat - ru.length))
        = buf + UInt32.ofNat (8 * (m + dr.length)) := by
      rw [hrulen, hdrlen,
        show len.toNat - (len.toNat - m - b) = m + (len.toNat - m - d)
          from by omega]
    -- WAT 8632 to 8641: both pointer checks fail
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply Wasm.SmallStep.twp_ne (result := 0)
      (by rw [if_neg (show ¬ (buf + UInt32.ofNat (8 * (m - lu.length))
        ≠ buf + UInt32.ofNat (8 * dl.length)) from fun hc => hc h67)])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    isimp only [back_forth]
    iapply Wasm.SmallStep.twp_ne (result := 0)
      (by rw [if_neg (show
        ¬ (buf + UInt32.ofNat (8 * (len.toNat - ru.length))
          ≠ buf + UInt32.ofNat (8 * (m + dr.length)))
        from fun hc => hc h138)])
    iapply Wasm.SmallStep.twp_brIfZero
    -- WAT 8642 to 8647: the length is not zero
    wasm_twp_pures [twp_localGet twp_const twp_shl]
    isimp only [shl_three, shift_three len (by omega)]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_eqz (result := 0)
      (by rw [if_neg (ofNat_ne_zero (8 * len.toNat) (by omega)
        (by omega))])
    iapply Wasm.SmallStep.twp_brIfZero
    -- WAT 8648 to 8651: the frame goes back to the buffer
    isimp only [hmid0, List.append_nil, List.nil_append, ← hbim] at Hfr
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    ihave Hbuf := (Table.PairSlice_forget 0 buf (L ++ Rt)).mp $$ Hbuf
    ihave Hfr := (Table.PairSlice_forget 0 fp (bimerge L Rt)).mp $$ Hfr
    iapply Wasm.SmallStep.twp_memoryCopy32_slices
      (Table.pairBytes (L ++ Rt)) (Table.pairBytes (bimerge L Rt))
      (by
        rw [Table.pairBytes_length, List.length_append,
          UInt32.toNat_ofNat_of_lt'
            (show 8 * len.toNat < UInt32.size by omega)]
        omega)
      (by
        rw [Table.pairBytes_length, hbimlen,
          UInt32.toNat_ofNat_of_lt'
            (show 8 * len.toNat < UInt32.size by omega)])
      (by
        rw [UInt32.toNat_ofNat_of_lt'
          (show 8 * len.toNat < UInt32.size by omega)]
        omega)
      $$ Hfr Hbuf
    iintro Hfr Hbuf
    ihave Hfr := (Table.PairSlice_forget 0 fp (bimerge L Rt)).mpr
      $$ Hfr
    ihave Hbuf := (Table.PairSlice_forget 0 buf (bimerge L Rt)).mpr
      $$ Hbuf
    -- WAT 8652: leave the body
    iapply Wasm.SmallStep.twp_br rfl
    simp only [qsFrame, List.take_zero, List.nil_append]
    iapply hcont
    isplitl [Hbuf]
    · iexact Hbuf
    · isplitl [Hfr]
      · iexact Hfr
      · iexact HRest

/-! ## The merge, WAT 8503 to 8652 -/

/-- An offset of zero entries. -/
private theorem addr_zero (v : UInt32) :
    v + UInt32.ofNat (8 * 0) = v := by
  rw [show (8 * 0 : Nat) = 0 from rfl,
    show (UInt32.ofNat 0 : UInt32) = 0 from rfl]
  exact UInt32.add_zero v

/-- The setup of WAT 8511 builds an address from the other side. -/
private theorem addr_rot (v w : UInt32) :
    (4294967288 : UInt32) + w + v = v + w + 4294967288 := by
  rw [UInt32.add_comm (4294967288 : UInt32) w,
    UInt32.add_comm (w + 4294967288) v, ← UInt32.add_assoc]

/-- The locals that WAT 8503 to 8523 leave are the locals of turn zero
of the merge loop. -/
private theorem mergeLoc_start (buf len fp : UInt32) (nt : NetScratch)
    (r11 : UInt32) (r12 : UInt64) (r15 r17 r18 : UInt32) (m : Nat)
    (L Rt : List (UInt32 × UInt32)) (hL : L.length = m)
    (hRt : Rt.length = len.toNat - m) (hmlen : m ≤ len.toNat) :
    rLoc buf len fp nt buf
        (4294967288 + (buf + UInt32.ofNat (8 * m)))
        (4294967288 + UInt32.ofNat (8 * len.toNat) + buf) fp
        (4294967288 + UInt32.ofNat (8 * len.toNat) + fp) r11 r12
        (buf + UInt32.ofNat (8 * m)) r15 (UInt32.ofNat m) r17 r18 []
      = mergeLoc buf len fp m nt r11 r12 r15 (UInt32.ofNat m) r17 r18 0
          L Rt L.reverse Rt.reverse := by
  simp only [mergeLoc, hL, hRt, List.length_reverse, Nat.sub_self,
    Nat.sub_zero, addr_zero, addr_rot,
    show m + (len.toNat - m) = len.toNat from by omega,
    show len.toNat - (len.toNat - m) = m from by omega,
    UInt32.add_comm (4294967288 : UInt32) (buf + UInt32.ofNat (8 * m))]

set_option maxHeartbeats 2000000 in
/-- The merge loop, with the locals as WAT 8523 leaves them. -/
private theorem twp_merge_loop_entry
    [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {r11 r15 r17 r18 : UInt32} {r12 : UInt64}
    {L Rt scratch : List (UInt32 × UInt32)} {m : Nat}
    {Rest : HeapIProp} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hm : m = len.toNat / 2) (hlow : 18 ≤ len.toNat)
    (hhigh : len.toNat ≤ 32)
    (hL : L.length = m) (hRt : Rt.length = len.toNat - m)
    (hsL : Table.SortedByKey L) (hsRt : Table.SortedByKey Rt)
    (hn : NodupKeys (L ++ Rt))
    (hbuf : buf.toNat + 8 * len.toNat < UInt32.size)
    (hfp : fp.toNat + 8 * len.toNat < UInt32.size)
    (hscratch : scratch.length = len.toNat) :
    iprop(Table.PairSlice 0 buf (L ++ Rt) ∗
      Table.PairSlice 0 fp scratch ∗ Rest ∗
      mergeExit buf len fp m L Rt Rest r12 r17 r18 arity remainder
        controls calls s E Φ) ⊢
      WP (.running ⟨rLoc buf len fp nt buf
            (4294967288 + (buf + UInt32.ofNat (8 * m)))
            (4294967288 + UInt32.ofNat (8 * len.toNat) + buf) fp
            (4294967288 + UInt32.ofNat (8 * len.toNat) + fp) r11 r12
            (buf + UInt32.ofNat (8 * m)) r15 (UInt32.ofNat m) r17 r18 [],
          .loop 0 0 qsMerge :: qsAfterMerge, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  rw [mergeLoc_start buf len fp nt r11 r12 r15 r17 r18 m L Rt hL hRt
    (by omega)]
  exact twp_merge_loop hm hlow hhigh hL hRt hsL hsRt hn hbuf hfp hscratch

set_option maxHeartbeats 2000000 in
/-- The merge of the two sorted regions, WAT 8503 to 8652.  The setup of
WAT 8503 to 8523 points local 6 and local 13 at the two fronts, local 7
and local 8 at the two backs, and local 9 and local 10 at the two ends
of the frame.  The loop and the odd middle then write `bimerge L Rt`
into the frame, and WAT 8648 copies the frame back over the buffer. -/
theorem twp_merge [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {y9 y10 y11 y15 : UInt32} {y12 : UInt64}
    {L Rt : List (UInt32 × UInt32)} {frame : List UInt8}
    {Rest : HeapIProp} {after : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlow : 18 ≤ len.toNat) (hhigh : len.toNat ≤ 32)
    (hL : L.length = len.toNat / 2)
    (hRt : Rt.length = len.toNat - len.toNat / 2)
    (hsL : Table.SortedByKey L) (hsRt : Table.SortedByKey Rt)
    (hn : NodupKeys (L ++ Rt))
    (hbuf : buf.toNat + 8 * len.toNat < UInt32.size)
    (hfp : fp.toNat + 256 < UInt32.size) (hframe : frame.length = 256)
    (hcont : ∀ (frame' : List UInt8) (nt' : NetScratch)
        (z6 z7 z8 z9 z10 z11 : UInt32) (z12 : UInt64)
        (z13 z15 z16 z17 z18 : UInt32),
      frame'.length = 256 →
      iprop(Table.PairSlice 0 buf (bimerge L Rt) ∗
        Slices.ByteSlice 0 fp frame' ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt' z6 z7 z8 z9 z10 z11 z12 z13
            z15 z16 z17 z18 [], after, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 buf (L ++ Rt) ∗
      Slices.ByteSlice 0 fp frame ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt 0
            (UInt32.ofNat (len.toNat - len.toNat / 2))
            (buf + UInt32.ofNat (8 * (len.toNat / 2))) y9 y10 y11 y12
            (buf + UInt32.ofNat (8 * (len.toNat / 2))) y15
            (UInt32.ofNat (len.toNat / 2)) 0
            (UInt32.ofNat (len.toNat - len.toNat / 2)) [],
          qsAfterRegion, arity, remainder, regBlocks after controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  set m := len.toNat / 2 with hmdef
  have hmlen : m ≤ len.toNat := by omega
  have hfplen : fp.toNat + 8 * len.toNat < UInt32.size := by omega
  have hpb : (Table.pairBytes (bimerge L Rt)).length = 8 * len.toNat := by
    rw [Table.pairBytes_length, bimerge_length hsL hsRt hn]
    omega
  obtain ⟨fpre, fpost, hfe, hfpre⟩ :
      ∃ fpre fpost : List UInt8, frame = fpre ++ fpost ∧
        fpre.length = 8 * len.toNat := by
    refine ⟨frame.take (8 * len.toNat), frame.drop (8 * len.toNat),
      (List.take_append_drop _ _).symm, ?_⟩
    rw [List.length_take, hframe]
    omega
  have hfpost : (Table.pairBytes (bimerge L Rt) ++ fpost).length = 256 := by
    have h0 : (fpre ++ fpost).length = 256 := by rw [← hfe]; exact hframe
    rw [List.length_append] at h0
    rw [List.length_append, hpb]
    omega
  subst hfe
  rw [qsAfterRegion_split, qsMergeSetup_shape]
  simp only [List.cons_append, List.nil_append]
  simp only [rLoc, qsLocals]
  iintro ⟨Hbuf, Hframe, HRest⟩
  icases (Slices.ByteSlice_append 0 fp fpre fpost).mp $$ Hframe with
    ⟨Hpre, Hpost⟩
  isimp only [hfpre] at Hpost
  icases Table.PairSlice_of_ByteSlice 0 fp fpre len.toNat hfpre $$ Hpre
    with ⟨%scratch, %hscratch, Hfr⟩
  -- WAT 8503 to 8523: the six cursors
  wasm_twp_pures [twp_localGet twp_const twp_add]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  isimp only [shl_three, shift_three len (by omega)]
  wasm_twp_pures [twp_const twp_add]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_add]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  -- WAT 8524 to 8652: the loop, the odd middle and the copy back
  iapply twp_merge_loop_entry (m := m) (L := L) (Rt := Rt)
    (scratch := scratch)
    (Rest := iprop(Slices.ByteSlice 0 (fp + UInt32.ofNat (8 * len.toNat))
      fpost ∗ Rest))
    hmdef hlow hhigh hL hRt hsL hsRt hn hbuf hfplen hscratch
  isplitl [Hbuf]
  · iexact Hbuf
  · isplitl [Hfr]
    · iexact Hfr
    · isplitl [Hpost HRest]
      · isplitl [Hpost]
        · iexact Hpost
        · iexact HRest
      · isimp only [mergeExit]
        iintro %nt2 %y11b %y15b %upAcc %dAcc %mid %lu %ru %dl %dr
          %hfacts ⟨Hbuf, Hfr, Hpost, HRest⟩
        have hcont2 : ∀ (nt3 : NetScratch)
            (z6 z7 z8 z9 z10 z11 : UInt32) (z12 : UInt64)
            (z13 z15 z16 z17 z18 : UInt32),
            iprop(Table.PairSlice 0 buf (bimerge L Rt) ∗
              Table.PairSlice 0 fp (bimerge L Rt) ∗
              (Slices.ByteSlice 0
                  (fp + UInt32.ofNat (8 * len.toNat)) fpost ∗ Rest)) ⊢
              WP (.running ⟨rLoc buf len fp nt3 z6 z7 z8 z9 z10 z11 z12
                    z13 z15 z16 z17 z18 [], after, arity, remainder,
                  controls, calls⟩ : Expr Universal.State) @ s; E
                [{ Φ }] := by
          intro nt3 z6 z7 z8 z9 z10 z11 z12 z13 z15 z16 z17 z18
          iintro ⟨Hb, Hf, Hp, HR⟩
          ihave Hf := (Table.PairSlice_forget 0 fp (bimerge L Rt)).mp
            $$ Hf
          isimp only [show fp + UInt32.ofNat (8 * len.toNat)
              = fp + UInt32.ofNat
                (Table.pairBytes (bimerge L Rt)).length from by
              rw [hpb]] at Hp
          iapply (hcont (Table.pairBytes (bimerge L Rt) ++ fpost) nt3
            z6 z7 z8 z9 z10 z11 z12 z13 z15 z16 z17 z18 hfpost)
          isplitl [Hb]
          · iexact Hb
          · isplitl [Hf Hp]
            · iapply (Slices.ByteSlice_append 0 fp
                (Table.pairBytes (bimerge L Rt)) fpost).mpr
              isplitl [Hf]
              · iexact Hf
              · iexact Hp
            · iexact HR
        iapply twp_merge_tail hmdef hlow hhigh hL hRt hsL hsRt hn hbuf
          hfplen hfacts.1 hfacts.2.1 hfacts.2.2 hcont2
        isplitl [Hbuf]
        · iexact Hbuf
        · isplitl [Hfr]
          · iexact Hfr
          · isplitl [Hpost]
            · iexact Hpost
            · iexact HRest

/-! ## The whole small sort, WAT 6193 to 8652 -/

set_option maxHeartbeats 2000000 in
/-- The small sort of absolute `func 24`, WAT 6193 to 8652.  A length
below 18 makes one region, which the sorting network and the insertion
sort of `Func21Region` put in key order.  A length of 18 to 32 makes two
regions and then merges them.  Both routes leave a sorted permutation of
the input in the buffer, and the frame keeps its 256 bytes. -/
theorem twp_small_sort [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {r6 r7 r8 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32} {r12 : UInt64}
    {pairs : List (UInt32 × UInt32)} {frame : List UInt8}
    {Rest : HeapIProp} {after : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hpairs : pairs.length = len.toNat) (hlen : len.toNat ≤ 32)
    (hn : NodupKeys pairs)
    (hbuf : buf.toNat + 8 * len.toNat < UInt32.size)
    (hfp : fp.toNat + 256 < UInt32.size) (hframe : frame.length = 256)
    (hcont : ∀ (out : List (UInt32 × UInt32)) (frame' : List UInt8)
        (nt' : NetScratch) (y6 y7 y8 y9 y10 y11 : UInt32)
        (y12 : UInt64) (y13 y15 y16 y17 y18 : UInt32),
      out.Perm pairs → Table.SortedByKey out → frame'.length = 256 →
      iprop(Table.PairSlice 0 buf out ∗ Slices.ByteSlice 0 fp frame' ∗
        Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt' y6 y7 y8 y9 y10 y11 y12 y13
            y15 y16 y17 y18 [], after, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 buf pairs ∗ Slices.ByteSlice 0 fp frame ∗
      Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 r8 r9 r10 r11 r12 r13 r15
            r16 r17 r18 [], qsAfter4, arity, remainder,
          regBlocks after controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  by_cases hsmall : len.toNat < 18
  · -- WAT 6193 to 8501: one region, and WAT 8503 never runs
    have hstep : ∀ (out : List (UInt32 × UInt32)) (nt' : NetScratch)
        (y6 y7 y8 y9 y10 y11 : UInt32) (y12 : UInt64)
        (y13 y15 y16 y17 y18 : UInt32),
        out.Perm pairs → Table.SortedByKey out →
        iprop(Table.PairSlice 0 buf out ∗
          (Slices.ByteSlice 0 fp frame ∗ Rest)) ⊢
        WP (.running ⟨rLoc buf len fp nt' y6 y7 y8 y9 y10 y11 y12 y13
              y15 y16 y17 y18 [], after, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
      intro out nt' y6 y7 y8 y9 y10 y11 y12 y13 y15 y16 y17 y18
        hperm hsorted
      iintro ⟨Hout, Hf, HR⟩
      iapply (hcont out frame nt' y6 y7 y8 y9 y10 y11 y12 y13 y15 y16
        y17 y18 hperm hsorted hframe)
      isplitl [Hout]
      · iexact Hout
      · isplitl [Hf]
        · iexact Hf
        · iexact HR
    iintro ⟨Hbuf, Hframe, HRest⟩
    iapply twp_region_loop_single
      (Rest := iprop(Slices.ByteSlice 0 fp frame ∗ Rest))
      hpairs hsmall hbuf hstep
    isplitl [Hbuf]
    · iexact Hbuf
    · isplitl [Hframe]
      · iexact Hframe
      · iexact HRest
  · -- WAT 6193 to 8652: two regions and the merge
    have hstep : ∀ (L Rt : List (UInt32 × UInt32)) (nt' : NetScratch)
        (y9 y10 y11 : UInt32) (y12 : UInt64) (y15 : UInt32),
        L.length = len.toNat / 2 →
        Rt.length = len.toNat - len.toNat / 2 →
        Table.SortedByKey L → Table.SortedByKey Rt →
        (L ++ Rt).Perm pairs →
        iprop(Table.PairSlice 0 buf (L ++ Rt) ∗
          (Slices.ByteSlice 0 fp frame ∗ Rest)) ⊢
        WP (.running ⟨rLoc buf len fp nt' 0
              (UInt32.ofNat (len.toNat - len.toNat / 2))
              (buf + UInt32.ofNat (8 * (len.toNat / 2))) y9 y10 y11 y12
              (buf + UInt32.ofNat (8 * (len.toNat / 2))) y15
              (UInt32.ofNat (len.toNat / 2)) 0
              (UInt32.ofNat (len.toNat - len.toNat / 2)) [],
            qsAfterRegion, arity, remainder, regBlocks after controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
      intro L Rt nt' y9 y10 y11 y12 y15 hL hRt hsL hsRt hperm
      have hnn : NodupKeys (L ++ Rt) := nodupKeys_of_perm hperm hn
      have hmerge : ∀ (frame' : List UInt8) (nt3 : NetScratch)
          (z6 z7 z8 z9 z10 z11 : UInt32) (z12 : UInt64)
          (z13 z15 z16 z17 z18 : UInt32),
          frame'.length = 256 →
          iprop(Table.PairSlice 0 buf (bimerge L Rt) ∗
            Slices.ByteSlice 0 fp frame' ∗ Rest) ⊢
          WP (.running ⟨rLoc buf len fp nt3 z6 z7 z8 z9 z10 z11 z12 z13
                z15 z16 z17 z18 [], after, arity, remainder, controls,
              calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
        intro frame' nt3 z6 z7 z8 z9 z10 z11 z12 z13 z15 z16 z17 z18
          hframe'
        iintro ⟨Hout, Hf, HR⟩
        iapply (hcont (bimerge L Rt) frame' nt3 z6 z7 z8 z9 z10 z11 z12
          z13 z15 z16 z17 z18
          ((bimerge_perm hsL hsRt hnn).trans hperm)
          (bimerge_sorted hsL hsRt hnn) hframe')
        isplitl [Hout]
        · iexact Hout
        · isplitl [Hf]
          · iexact Hf
          · iexact HR
      iintro ⟨Hbuf, Hframe, HRest⟩
      iapply twp_merge (by omega) hlen hL hRt hsL hsRt hnn hbuf hfp
        hframe hmerge
      isplitl [Hbuf]
      · iexact Hbuf
      · isplitl [Hframe]
        · iexact Hframe
        · iexact HRest
    iintro ⟨Hbuf, Hframe, HRest⟩
    iapply twp_region_loop_double
      (Rest := iprop(Slices.ByteSlice 0 fp frame ∗ Rest))
      hpairs (by omega) hlen hbuf hstep
    isplitl [Hbuf]
    · iexact Hbuf
    · isplitl [Hframe]
      · iexact Hframe
      · iexact HRest

end Project.RustHashMap.Func21Merge
