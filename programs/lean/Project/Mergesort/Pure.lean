import Mathlib.Data.List.Sort

/-!
# Pure merge-sort facts

This file contains the implementation-independent mathematics used by the
Wasm proof.  The definitions are polymorphic over a linear order so the loop
invariants are reusable for other integer widths.
-/

namespace Project.Mergesort.Pure

/- `UInt64` exposes its computational unsigned `LE`/`LT` operations but does
not come with a bundled `LinearOrder`.  The generated merge, recursive sort,
and their pure specifications must all use exactly this one shared instance. -/
instance uint64LinearOrder : LinearOrder UInt64 where
  le := @LE.le UInt64 instLEUInt64
  lt := @LT.lt UInt64 instLTUInt64
  le_refl := by intro a; rw [UInt64.le_iff_toNat_le]
  le_trans := by
    intro a b c hab hbc
    rw [UInt64.le_iff_toNat_le] at hab hbc ⊢
    omega
  le_antisymm := by
    intro a b hab hba
    apply UInt64.toNat.inj
    rw [UInt64.le_iff_toNat_le] at hab hba
    omega
  lt_iff_le_not_ge := by
    intro a b
    rw [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt64.le_iff_toNat_le]
    omega
  le_total := by
    intro a b
    rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le]
    omega
  toDecidableLE := UInt64.decLe
  toDecidableEq := instDecidableEqUInt64
  toDecidableLT := UInt64.decLt

/-! ## Text stream format -/

/-- The exact byte encoding used by the unchanged Rust entry point: decimal
`u64` values separated by one ASCII space, with no trailing delimiter. -/
def encodeValues (values : List UInt64) : List UInt8 :=
  (String.intercalate " " (values.map toString)).toUTF8.toList

@[simp] theorem encodeValues_nil : encodeValues [] = [] := by
  simp [encodeValues]

/-- A list is sorted in nondecreasing order. -/
def Sorted [LE α] (values : List α) : Prop :=
  values.Pairwise (· ≤ ·)

/-- A declarative trace of a stable merge. -/
inductive MergeRel [LE α] : List α → List α → List α → Prop where
  | leftNil (right) : MergeRel [] right right
  | rightNil (left) : MergeRel left [] left
  | takeLeft {x y xs ys output}
      (hxy : x ≤ y) (tail : MergeRel xs (y :: ys) output) :
      MergeRel (x :: xs) (y :: ys) (x :: output)
  | takeRight {x y xs ys output}
      (hxy : ¬x ≤ y) (tail : MergeRel (x :: xs) ys output) :
      MergeRel (x :: xs) (y :: ys) (y :: output)

theorem perm_of_mergeRel [LE α] {left right output : List α}
    (hmerge : MergeRel left right output) :
    List.Perm (left ++ right) output := by
  induction hmerge with
  | leftNil => simp
  | rightNil => simp
  | takeLeft _ _ ih =>
      simp only [List.cons_append]
      exact List.Perm.cons _ ih
  | takeRight _ _ ih =>
      exact (List.Perm.cons _ List.perm_middle).trans
        ((List.Perm.swap _ _ _).symm.trans (List.Perm.cons _ ih))

theorem sorted_of_mergeRel [LinearOrder α] {left right output : List α}
    (hmerge : MergeRel left right output)
    (hleft : Sorted left) (hright : Sorted right) :
    Sorted output := by
  induction hmerge with
  | leftNil => exact hright
  | rightNil => exact hleft
  | @takeLeft x y xs ys output hxy tail ih =>
      have hxs : Sorted xs := List.Pairwise.tail hleft
      have hyr : Sorted (y :: ys) := hright
      simp only [Sorted, List.pairwise_cons] at hleft hright ⊢
      constructor
      · intro z hz
        have hz' : z ∈ xs ++ y :: ys :=
          (perm_of_mergeRel tail).mem_iff.mpr hz
        simp only [List.mem_append, List.mem_cons] at hz'
        rcases hz' with hxs' | rfl | hys
        · exact hleft.1 z hxs'
        · exact hxy
        · exact hxy.trans (hright.1 z hys)
      · exact ih hxs hyr
  | @takeRight x y xs ys output hxy tail ih =>
      have hxl : Sorted (x :: xs) := hleft
      have hys : Sorted ys := List.Pairwise.tail hright
      simp only [Sorted, List.pairwise_cons] at hleft hright ⊢
      constructor
      · intro z hz
        have hz' : z ∈ x :: xs ++ ys :=
          (perm_of_mergeRel tail).mem_iff.mpr hz
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hz'
        rcases hz' with rfl | hxs | hys'
        · exact le_of_not_ge hxy
        · exact (le_of_not_ge hxy).trans (hleft.1 z hxs)
        · exact hright.1 z hys'
      · exact ih hxl hys

/-- Sortedness and multiset preservation, the public mathematical result. -/
def SortedPermutation [LE α] (input output : List α) : Prop :=
  Sorted output ∧ List.Perm input output

/-- Compose the two recursive results and the final stable merge. -/
theorem sortedPermutation_of_split_merge [LinearOrder α]
    (input left right output : List α) (mid : Nat)
    (hleft : SortedPermutation (input.take mid) left)
    (hright : SortedPermutation (input.drop mid) right)
    (hmerge : MergeRel left right output) :
    SortedPermutation input output := by
  constructor
  · exact sorted_of_mergeRel hmerge hleft.1 hright.1
  · rw [← List.take_append_drop mid input]
    exact (hleft.2.append hright.2).trans (perm_of_mergeRel hmerge)

theorem sortedPermutation_of_mergeRel [LinearOrder α]
    {left right output : List α}
    (hmerge : MergeRel left right output)
    (hleft : Sorted left) (hright : Sorted right) :
    SortedPermutation (left ++ right) output :=
  ⟨sorted_of_mergeRel hmerge hleft hright, perm_of_mergeRel hmerge⟩

/-- Continuation form of a partially completed merge. -/
def MergeProgress [LE α]
    (originalLeft originalRight emitted remainingLeft remainingRight :
      List α) : Prop :=
  ∀ tail, MergeRel remainingLeft remainingRight tail →
    MergeRel originalLeft originalRight (emitted ++ tail)

@[simp] theorem mergeProgress_start [LE α] (left right : List α) :
    MergeProgress left right [] left right := by
  intro tail htail
  simpa using htail

theorem MergeProgress.takeLeft [LE α]
    {originalLeft originalRight emitted xs ys : List α} {x y : α}
    (hprogress :
      MergeProgress originalLeft originalRight emitted (x :: xs) (y :: ys))
    (hxy : x ≤ y) :
    MergeProgress originalLeft originalRight (emitted ++ [x]) xs (y :: ys) := by
  intro tail htail
  have hnext : MergeRel (x :: xs) (y :: ys) (x :: tail) :=
    .takeLeft hxy htail
  simpa [List.append_assoc] using hprogress (x :: tail) hnext

theorem MergeProgress.takeRight [LE α]
    {originalLeft originalRight emitted xs ys : List α} {x y : α}
    (hprogress :
      MergeProgress originalLeft originalRight emitted (x :: xs) (y :: ys))
    (hxy : ¬x ≤ y) :
    MergeProgress originalLeft originalRight (emitted ++ [y]) (x :: xs) ys := by
  intro tail htail
  have hnext : MergeRel (x :: xs) (y :: ys) (y :: tail) :=
    .takeRight hxy htail
  simpa [List.append_assoc] using hprogress (y :: tail) hnext

theorem MergeProgress.finishLeft [LE α]
    {originalLeft originalRight emitted remaining : List α}
    (hprogress :
      MergeProgress originalLeft originalRight emitted remaining []) :
    MergeRel originalLeft originalRight (emitted ++ remaining) :=
  hprogress remaining (.rightNil remaining)

theorem MergeProgress.finishRight [LE α]
    {originalLeft originalRight emitted remaining : List α}
    (hprogress :
      MergeProgress originalLeft originalRight emitted [] remaining) :
    MergeRel originalLeft originalRight (emitted ++ remaining) :=
  hprogress remaining (.leftNil remaining)

section ListInvariants

variable {α : Type} [LinearOrder α]

/-- Half-open list segment `[start, stop)`. -/
def segment (values : List α) (start stop : Nat) : List α :=
  (values.drop start).take (stop - start)

theorem segment_cons {values : List α} {index stop : Nat} {value : α}
    (hindex : index < stop) (hstop : stop ≤ values.length)
    (hlookup : values[index]? = some value) :
    segment values index stop =
      value :: segment values (index + 1) stop := by
  induction values generalizing index stop with
  | nil => simp at hlookup
  | cons head values ih =>
      cases index with
      | zero =>
        cases stop with
        | zero => omega
        | succ stop =>
          simp at hlookup
          subst head
          simp [segment]
      | succ index =>
        cases stop with
        | zero => omega
        | succ stop =>
          simp [segment]
          apply ih
          · omega
          · simp at hstop
            omega
          · simpa using hlookup

omit [LinearOrder α] in
theorem take_set_succ {values : List α} {index : Nat} {value : α}
    (hindex : index < values.length) :
    (values.set index value).take (index + 1) =
      values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons head values ih =>
      cases index with
      | zero => simp
      | succ index =>
        simp at hindex
        simp [ih hindex, Nat.add_assoc]

theorem take_set_of_le {values : List α} {index count : Nat} {value : α}
    (hcount : count ≤ index) :
    (values.set index value).take count = values.take count := by
  induction values generalizing index count with
  | nil => simp
  | cons head values ih =>
      cases count with
      | zero => simp
      | succ count =>
        cases index with
        | zero => omega
        | succ index =>
          simp
          exact ih (by omega)

omit [LinearOrder α] in
theorem drop_set_succ {values : List α} {index : Nat} {value : α} :
    (values.set index value).drop (index + 1) =
      values.drop (index + 1) := by
  induction values generalizing index with
  | nil => simp
  | cons head values ih =>
      cases index with
      | zero => simp
      | succ index =>
        simpa [Nat.add_assoc] using ih (index := index)

theorem segment_eq_take_drop {values : List α} {start stop : Nat}
    (hstart : start ≤ stop) :
    segment values start stop = (values.take stop).drop start := by
  induction values generalizing start stop with
  | nil => simp [segment]
  | cons head values ih =>
      cases start with
      | zero => simp [segment]
      | succ start =>
        cases stop with
        | zero => omega
        | succ stop =>
          simp [segment]
          exact ih (by omega)

theorem mergeRel_right_nil_eq {left output : List α}
    (h : MergeRel left [] output) : output = left := by
  cases h <;> simp_all

theorem mergeRel_left_nil_eq {right output : List α}
    (h : MergeRel [] right output) : output = right := by
  cases h <;> simp_all

theorem MergeProgress.takeRemainingLeft
    {originalLeft originalRight emitted xs : List α} {x : α}
    (hprogress :
      MergeProgress originalLeft originalRight emitted (x :: xs) []) :
    MergeProgress originalLeft originalRight (emitted ++ [x]) xs [] := by
  intro tail htail
  have htailEq : tail = xs := mergeRel_right_nil_eq htail
  subst tail
  have hnext : MergeRel (x :: xs) [] (x :: xs) := .rightNil _
  simpa [List.append_assoc] using hprogress (x :: xs) hnext

theorem MergeProgress.takeRemainingRight
    {originalLeft originalRight emitted ys : List α} {y : α}
    (hprogress :
      MergeProgress originalLeft originalRight emitted [] (y :: ys)) :
    MergeProgress originalLeft originalRight (emitted ++ [y]) [] ys := by
  intro tail htail
  have htailEq : tail = ys := mergeRel_left_nil_eq htail
  subst tail
  have hnext : MergeRel [] (y :: ys) (y :: ys) := .leftNil _
  simpa [List.append_assoc] using hprogress (y :: ys) hnext

/-- Invariant for the loop that merges two source runs into scratch. -/
def MergeLoopInvariant
    (input temporaryValues : List α) (left mid right i j k : Nat)
    (emitted : List α) : Prop :=
  left ≤ i ∧ i ≤ mid ∧ mid ≤ j ∧ j ≤ right ∧
  right ≤ input.length ∧
  temporaryValues.length = input.length ∧
  k = left + emitted.length ∧
  emitted.length = (i - left) + (j - mid) ∧
  temporaryValues.take k = temporaryValues.take left ++ emitted ∧
  MergeProgress
    (segment input left mid) (segment input mid right) emitted
    (segment input i mid) (segment input j right)

theorem mergeLoopInvariant_start
    {input temporaryValues : List α} {left mid right : Nat}
    (hbounds : left ≤ mid ∧ mid ≤ right ∧ right ≤ input.length)
    (hlength : temporaryValues.length = input.length) :
    MergeLoopInvariant input temporaryValues left mid right
      left mid left [] := by
  rcases hbounds with ⟨hlm, hmr, hrlen⟩
  simp [MergeLoopInvariant, hlength, hlm, hmr, hrlen,
    mergeProgress_start]

theorem MergeLoopInvariant.k_lt
    {input temporaryValues : List α} {left mid right i j k : Nat}
    {emitted : List α}
    (h : MergeLoopInvariant input temporaryValues left mid right i j k emitted)
    (hi : i < mid) (hj : j < right) :
    k < input.length := by
  unfold MergeLoopInvariant at h
  omega

theorem MergeLoopInvariant.takeLeft
    {input temporaryValues : List α} {left mid right i j k : Nat}
    {emitted : List α} {x y : α}
    (h : MergeLoopInvariant input temporaryValues left mid right i j k emitted)
    (hi : i < mid) (hj : j < right)
    (hx : input[i]? = some x) (hy : input[j]? = some y)
    (hxy : x ≤ y) :
    MergeLoopInvariant input (temporaryValues.set k x)
      left mid right (i + 1) j (k + 1) (emitted ++ [x]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hli, him, hmj, hjr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by rw [hlength]; omega
  have hlk : left ≤ k := by omega
  have hleftSegment :
      segment input i mid = x :: segment input (i + 1) mid :=
    segment_cons hi (by omega) hx
  have hrightSegment :
      segment input j right = y :: segment input (j + 1) right :=
    segment_cons hj hrlen hy
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨by omega, by omega, hmj, hjr, hrlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, take_set_of_le hlk, htake]
    simp [List.append_assoc]
  · rw [hrightSegment]
    exact hprogress.takeLeft hxy

theorem MergeLoopInvariant.takeRight
    {input temporaryValues : List α} {left mid right i j k : Nat}
    {emitted : List α} {x y : α}
    (h : MergeLoopInvariant input temporaryValues left mid right i j k emitted)
    (hi : i < mid) (hj : j < right)
    (hx : input[i]? = some x) (hy : input[j]? = some y)
    (hxy : ¬x ≤ y) :
    MergeLoopInvariant input (temporaryValues.set k y)
      left mid right i (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hli, him, hmj, hjr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by rw [hlength]; omega
  have hlk : left ≤ k := by omega
  have hrightSegment :
      segment input j right = y :: segment input (j + 1) right :=
    segment_cons hj hrlen hy
  have hleftSegment :
      segment input i mid = x :: segment input (i + 1) mid :=
    segment_cons hi (by omega) hx
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨hli, him, by omega, by omega, hrlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, take_set_of_le hlk, htake]
    simp [List.append_assoc]
  · rw [hleftSegment]
    exact hprogress.takeRight hxy

theorem MergeLoopInvariant.takeRemainingLeft
    {input temporaryValues : List α} {left mid right i k : Nat}
    {emitted : List α} {x : α}
    (h : MergeLoopInvariant input temporaryValues left mid right i right k emitted)
    (hi : i < mid) (hx : input[i]? = some x) :
    MergeLoopInvariant input (temporaryValues.set k x)
      left mid right (i + 1) right (k + 1) (emitted ++ [x]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hli, him, hmr, hrr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by rw [hlength]; omega
  have hlk : left ≤ k := by omega
  have hleftSegment :
      segment input i mid = x :: segment input (i + 1) mid :=
    segment_cons hi (by omega) hx
  have hrightSegment : segment input right right = [] := by simp [segment]
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨by omega, by omega, hmr, hrr, hrlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, take_set_of_le hlk, htake]
    simp [List.append_assoc]
  · rw [hrightSegment]
    exact hprogress.takeRemainingLeft

theorem MergeLoopInvariant.takeRemainingRight
    {input temporaryValues : List α} {left mid right j k : Nat}
    {emitted : List α} {y : α}
    (h : MergeLoopInvariant input temporaryValues left mid right mid j k emitted)
    (hj : j < right) (hy : input[j]? = some y) :
    MergeLoopInvariant input (temporaryValues.set k y)
      left mid right mid (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hlm, hmm, hmj, hjr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by rw [hlength]; omega
  have hlk : left ≤ k := by omega
  have hrightSegment :
      segment input j right = y :: segment input (j + 1) right :=
    segment_cons hj hrlen hy
  have hleftSegment : segment input mid mid = [] := by simp [segment]
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨hlm, hmm, by omega, by omega, hrlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, take_set_of_le hlk, htake]
    simp [List.append_assoc]
  · rw [hleftSegment]
    exact hprogress.takeRemainingRight

theorem MergeLoopInvariant.finished
    {input temporaryValues : List α} {left mid right k : Nat}
    {emitted : List α}
    (h : MergeLoopInvariant input temporaryValues left mid right
      mid right k emitted) :
    k = right ∧
    temporaryValues.take right = temporaryValues.take left ++ emitted ∧
    MergeRel (segment input left mid) (segment input mid right) emitted := by
  unfold MergeLoopInvariant at h
  rcases h with
    ⟨hlm, _, hmr, _, _, _, hk, hemitted, htake, hprogress⟩
  have hkright : k = right := by omega
  rw [hkright] at htake
  refine ⟨hkright, htake, ?_⟩
  have hleft : segment input mid mid = [] := by simp [segment]
  have hright : segment input right right = [] := by simp [segment]
  rw [hleft, hright] at hprogress
  simpa using hprogress [] (.leftNil [])

/-- Minimal invariant for the standalone recursive scratch-to-source copy. -/
def CopyBackInvariant (current scratch : List α) (index : Nat) : Prop :=
  current.length = scratch.length ∧
  index ≤ current.length ∧
  current.take index = scratch.take index

omit [LinearOrder α] in
theorem CopyBackInvariant.step
    {current scratch : List α} {index : Nat}
    (h : CopyBackInvariant current scratch index)
    (hindex : index < current.length)
    (hsindex : index < scratch.length) :
    CopyBackInvariant (current.set index scratch[index]) scratch (index + 1) := by
  rcases h with ⟨hlength, hle, htake⟩
  refine ⟨by simp [hlength], by simp; omega, ?_⟩
  rw [take_set_succ hindex, htake]
  exact List.take_append_getElem hsindex

omit [LinearOrder α] in
theorem CopyBackInvariant.finished
    {current scratch : List α}
    (h : CopyBackInvariant current scratch current.length) :
    current = scratch := by
  rcases h with ⟨hlength, _, htake⟩
  rw [List.take_length, hlength, List.take_length] at htake
  exact htake

theorem sorted_of_length_le_one {values : List α}
    (hlength : values.length ≤ 1) :
    Sorted values := by
  unfold Sorted
  cases values with
  | nil => simp
  | cons head tail =>
    cases tail with
    | nil => simp
    | cons next rest => simp at hlength

/-- Declarative recursive merge-sort execution.  The split constructor is
deliberately parameterized by the split point: the generated Wasm proof will
instantiate it with `input.length / 2`, while the mathematical argument only
needs the standard `take`/`drop` decomposition. -/
inductive SortRel : List α → List α → Prop where
  | small {input : List α} (hlength : input.length ≤ 1) :
      SortRel input input
  | split {input left right output : List α} (mid : Nat)
      (leftSort : SortRel (input.take mid) left)
      (rightSort : SortRel (input.drop mid) right)
      (merged : MergeRel left right output) :
      SortRel input output

/-- Every declarative recursive merge-sort execution produces a sorted
permutation of its input. -/
theorem sortedPermutation_of_sortRel {input output : List α}
    (hsort : SortRel input output) :
    SortedPermutation input output := by
  induction hsort with
  | small hlength =>
      exact ⟨sorted_of_length_le_one hlength, List.Perm.refl _⟩
  | split mid leftSort rightSort merged leftIH rightIH =>
      exact sortedPermutation_of_split_merge _ _ _ _ mid
        leftIH rightIH merged

theorem SortRel.perm {input output : List α}
    (hsort : SortRel input output) :
    List.Perm input output :=
  (sortedPermutation_of_sortRel hsort).2

theorem SortRel.length_eq {input output : List α}
    (hsort : SortRel input output) :
    output.length = input.length :=
  hsort.perm.length_eq.symm

end ListInvariants

end Project.Mergesort.Pure
