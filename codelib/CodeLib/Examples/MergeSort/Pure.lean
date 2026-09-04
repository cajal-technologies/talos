import CodeLib.Examples.MergeSort
import CodeLib.List
import CodeLib.UInt32

/-!
# Pure mathematics used by the MiniWasm merge-sort proof

This file contains no Iris assertions or machine states.  `MergeRel` is a
declarative trace of the choices made by `mergeBody`; keeping it relational
makes the loop invariant readable and avoids exposing a second executable
merge implementation.
-/

namespace Wasm.Examples.MergeSort

theorem segment_cons {values : List UInt32} {index stop : Nat} {value : UInt32}
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
          · simp at hstop; omega
          · simpa using hlookup

theorem take_set_succ {values : List UInt32} {index : Nat} {value : UInt32}
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

theorem take_set_of_le {values : List UInt32} {index count : Nat} {value : UInt32}
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
          simp; exact ih (by omega)

theorem set_eq_self_of_getElem?_eq
    {values : List UInt32} {index : Nat} {value : UInt32}
    (hlookup : values[index]? = some value) :
    values.set index value = values := by
  induction values generalizing index with
  | nil => simp at hlookup
  | cons head tail ih =>
    cases index with
    | zero =>
      simp at hlookup
      subst head
      simp
    | succ index =>
      simp at hlookup
      simp [ih hlookup]

theorem drop_set_succ {values : List UInt32} {index : Nat} {value : UInt32} :
    (values.set index value).drop (index + 1) =
      values.drop (index + 1) := by
  induction values generalizing index with
  | nil => simp
  | cons head values ih =>
      cases index with
      | zero => simp
      | succ index =>
        simpa [Nat.add_assoc] using ih (index := index)

theorem perm_of_mergeRel {left right output}
    (hmerge : MergeRel left right output) :
    List.Perm (left ++ right) output := by
  induction hmerge with
  | leftNil | rightNil | takeLeft => simp_all
  | takeRight _ _ ih =>
      exact List.perm_middle.trans (List.Perm.cons _ ih)

theorem sorted_of_mergeRel {left right output}
    (hmerge : MergeRel left right output)
    (hleft : Sorted left) (hright : Sorted right) :
    Sorted output := by
  induction hmerge with
  | leftNil => exact hright
  | rightNil => exact hleft
  | @takeLeft x y xs ys output hxy tail ih =>
      have hyr : Sorted (y :: ys) := hright
      simp only [Sorted, List.pairwise_cons] at hleft hright ⊢
      refine ⟨?_, ih hleft.2 hyr⟩
      intro z hz
      have hz' : z ∈ xs ++ y :: ys :=
        (perm_of_mergeRel tail).mem_iff.mpr hz
      simp only [List.mem_append, List.mem_cons] at hz'
      rcases hz' with hxs | rfl | hys
      · exact hleft.1 z hxs
      · exact UInt32.le_of_lt hxy
      · exact UInt32.le_trans (UInt32.le_of_lt hxy) (hright.1 z hys)
  | @takeRight x y xs ys output hxy tail ih =>
      have hxl : Sorted (x :: xs) := hleft
      simp only [Sorted, List.pairwise_cons] at hleft hright ⊢
      refine ⟨?_, ih hxl hright.2⟩
      intro z hz
      have hz' : z ∈ x :: xs ++ ys :=
        (perm_of_mergeRel tail).mem_iff.mpr hz
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hz'
      rcases hz' with rfl | hxs | hys
      · exact UInt32.le_of_not_lt hxy
      · exact UInt32.le_trans (UInt32.le_of_not_lt hxy) (hleft.1 z hxs)
      · exact hright.1 z hys

theorem sortedPermutation_of_mergeRel {left right output}
    (hmerge : MergeRel left right output)
    (hleft : Sorted left) (hright : Sorted right) :
    SortedPermutation (left ++ right) output :=
  ⟨sorted_of_mergeRel hmerge hleft hright, perm_of_mergeRel hmerge⟩

/-- Continuation form of a partially completed merge.

`emitted` has already been emitted. Any valid merge of the two remainders can
be appended to it to obtain a valid merge of the original inputs.
-/
def MergeProgress
    (originalLeft originalRight emitted remainingLeft remainingRight :
      List UInt32) : Prop :=
  ∀ tail, MergeRel remainingLeft remainingRight tail →
    MergeRel originalLeft originalRight (emitted ++ tail)

@[simp]
theorem mergeProgress_start (left right : List UInt32) :
    MergeProgress left right [] left right := by simp [MergeProgress]

theorem MergeProgress.takeLeft
    {originalLeft originalRight emitted xs ys : List UInt32} {x y : UInt32}
    (hprogress :
      MergeProgress originalLeft originalRight emitted (x :: xs) (y :: ys))
    (hxy : x < y) :
    MergeProgress originalLeft originalRight (emitted ++ [x]) xs (y :: ys) := by
  intro tail htail
  simpa [List.append_assoc] using hprogress (x :: tail) (.takeLeft hxy htail)

theorem MergeProgress.takeRight
    {originalLeft originalRight emitted xs ys : List UInt32} {x y : UInt32}
    (hprogress :
      MergeProgress originalLeft originalRight emitted (x :: xs) (y :: ys))
    (hxy : ¬x < y) :
    MergeProgress originalLeft originalRight (emitted ++ [y]) (x :: xs) ys := by
  intro tail htail
  simpa [List.append_assoc] using hprogress (y :: tail) (.takeRight hxy htail)

theorem MergeProgress.finishLeft
    {originalLeft originalRight emitted remaining : List UInt32}
    (hprogress :
      MergeProgress originalLeft originalRight emitted remaining []) :
    MergeRel originalLeft originalRight (emitted ++ remaining) :=
  hprogress remaining (.rightNil remaining)

theorem MergeProgress.finishRight
    {originalLeft originalRight emitted remaining : List UInt32}
    (hprogress :
      MergeProgress originalLeft originalRight emitted [] remaining) :
    MergeRel originalLeft originalRight (emitted ++ remaining) :=
  hprogress remaining (.leftNil remaining)

theorem mergeRel_right_nil_eq {left output : List UInt32}
    (h : MergeRel left [] output) : output = left := by
  cases h <;> simp_all

theorem mergeRel_left_nil_eq {right output : List UInt32}
    (h : MergeRel [] right output) : output = right := by
  cases h <;> simp_all

theorem MergeProgress.takeRemainingLeft
    {originalLeft originalRight emitted xs : List UInt32} {x : UInt32}
    (hprogress :
      MergeProgress originalLeft originalRight emitted (x :: xs) []) :
    MergeProgress originalLeft originalRight (emitted ++ [x]) xs [] := by
  intro tail htail
  cases mergeRel_right_nil_eq htail
  simpa [List.append_assoc] using
    hprogress (x :: xs) (.rightNil (x :: xs))

theorem MergeProgress.takeRemainingRight
    {originalLeft originalRight emitted ys : List UInt32} {y : UInt32}
    (hprogress :
      MergeProgress originalLeft originalRight emitted [] (y :: ys)) :
    MergeProgress originalLeft originalRight (emitted ++ [y]) [] ys := by
  intro tail htail
  cases mergeRel_left_nil_eq htail
  simpa [List.append_assoc] using
    hprogress (y :: ys) (.leftNil (y :: ys))

/-- Pure invariant of the first merge loop. `emitted` is exactly the temporary
array prefix written since `left`; the source array is still unchanged. -/
def MergeLoopInvariant
    (input temporaryValues : List UInt32) (left mid right i j k : Nat)
    (emitted : List UInt32) : Prop :=
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
    {input temporaryValues : List UInt32} {left mid right : Nat}
    (hbounds : left ≤ mid ∧ mid ≤ right ∧ right ≤ input.length)
    (hlength : temporaryValues.length = input.length) :
    MergeLoopInvariant input temporaryValues left mid right
      left mid left [] := by
  rcases hbounds with ⟨hlm, hmr, hrlen⟩
  simp [MergeLoopInvariant, hlength, hlm, hmr, hrlen,
    mergeProgress_start]

theorem MergeLoopInvariant.k_lt
    {input temporaryValues : List UInt32} {left mid right i j k : Nat}
    {emitted : List UInt32}
    (h : MergeLoopInvariant input temporaryValues left mid right i j k emitted)
    (hi : i < mid) (hj : j < right) :
    k < input.length := by
  unfold MergeLoopInvariant at h
  omega

theorem MergeLoopInvariant.takeLeft
    {input temporaryValues : List UInt32} {left mid right i j k : Nat}
    {emitted : List UInt32} {x y : UInt32}
    (h : MergeLoopInvariant input temporaryValues left mid right i j k emitted)
    (hi : i < mid) (hj : j < right)
    (hx : input[i]? = some x) (hy : input[j]? = some y)
    (hxy : x < y) :
    MergeLoopInvariant input (temporaryValues.set k x)
      left mid right (i + 1) j (k + 1) (emitted ++ [x]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hli, him, hmj, hjr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by omega
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
  · rw [hrightSegment]; exact hprogress.takeLeft hxy

theorem MergeLoopInvariant.takeRight
    {input temporaryValues : List UInt32} {left mid right i j k : Nat}
    {emitted : List UInt32} {x y : UInt32}
    (h : MergeLoopInvariant input temporaryValues left mid right i j k emitted)
    (hi : i < mid) (hj : j < right)
    (hx : input[i]? = some x) (hy : input[j]? = some y)
    (hxy : ¬x < y) :
    MergeLoopInvariant input (temporaryValues.set k y)
      left mid right i (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hli, him, hmj, hjr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by omega
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
  · rw [hleftSegment]; exact hprogress.takeRight hxy

theorem MergeLoopInvariant.takeRemainingLeft
    {input temporaryValues : List UInt32} {left mid right i k : Nat}
    {emitted : List UInt32} {x : UInt32}
    (h :
      MergeLoopInvariant input temporaryValues left mid right i right k emitted)
    (hi : i < mid) (hx : input[i]? = some x) :
    MergeLoopInvariant input (temporaryValues.set k x)
      left mid right (i + 1) right (k + 1) (emitted ++ [x]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hli, him, hmr, hrr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by omega
  have hlk : left ≤ k := by omega
  have hleftSegment :
      segment input i mid = x :: segment input (i + 1) mid :=
    segment_cons hi (by omega) hx
  have hrightSegment : segment input right right = [] := by
    simp [segment]
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨by omega, by omega, hmr, hrr, hrlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, take_set_of_le hlk, htake]
    simp [List.append_assoc]
  · rw [hrightSegment]; exact hprogress.takeRemainingLeft

theorem MergeLoopInvariant.takeRemainingRight
    {input temporaryValues : List UInt32} {left mid right j k : Nat}
    {emitted : List UInt32} {y : UInt32}
    (h :
      MergeLoopInvariant input temporaryValues left mid right mid j k emitted)
    (hj : j < right) (hy : input[j]? = some y) :
    MergeLoopInvariant input (temporaryValues.set k y)
      left mid right mid (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hlm, hmm, hmj, hjr, hrlen, hlength, hk, hemitted,
      htake, hprogress⟩
  have hklen : k < temporaryValues.length := by omega
  have hlk : left ≤ k := by omega
  have hrightSegment :
      segment input j right = y :: segment input (j + 1) right :=
    segment_cons hj hrlen hy
  have hleftSegment : segment input mid mid = [] := by
    simp [segment]
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨hlm, hmm, by omega, by omega, hrlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, take_set_of_le hlk, htake]
    simp [List.append_assoc]
  · rw [hleftSegment]; exact hprogress.takeRemainingRight

theorem MergeLoopInvariant.finished
    {input temporaryValues : List UInt32} {left mid right k : Nat}
    {emitted : List UInt32}
    (h :
      MergeLoopInvariant input temporaryValues left mid right
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

/-- Pure invariant while the completed merge is copied back to the source. -/
def CopyLoopInvariant
    (input current : List UInt32) (left right k : Nat)
    (copied : List UInt32) : Prop :=
  left ≤ k ∧ k ≤ right ∧ right ≤ input.length ∧
  current.length = input.length ∧
  copied.length = k - left ∧
  current.take k = input.take left ++ copied ∧
  current.drop k = input.drop k

theorem copyLoopInvariant_start {input : List UInt32} {left right : Nat}
    (hleft : left ≤ right) (hright : right ≤ input.length) :
    CopyLoopInvariant input input left right left [] := by simp [CopyLoopInvariant, hleft, hright]

theorem CopyLoopInvariant.k_lt_length
    {input current copied : List UInt32} {left right k : Nat}
    (h : CopyLoopInvariant input current left right k copied)
    (hk : k < right) : k < current.length := by
  unfold CopyLoopInvariant at h
  omega

theorem CopyLoopInvariant.step
    {input current copied : List UInt32} {left right k : Nat} {value : UInt32}
    (h : CopyLoopInvariant input current left right k copied)
    (hk : k < right) :
    CopyLoopInvariant input (current.set k value) left right (k + 1)
      (copied ++ [value]) := by
  unfold CopyLoopInvariant at h ⊢
  rcases h with
    ⟨hlk, hkr, hrlen, hlength, hcopied, htake, hdrop⟩
  have hklen : k < current.length := by omega
  refine ⟨by omega, by omega, hrlen, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · rw [take_set_succ hklen, htake]
    simp [List.append_assoc]
  · rw [drop_set_succ]
    have hdrop' := congrArg (List.drop 1) hdrop
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hdrop'

theorem CopyLoopInvariant.finish
    {input output copied : List UInt32} {left mid right : Nat}
    (h : CopyLoopInvariant input output left right right copied)
    (hlm : left ≤ mid) (hmr : mid ≤ right)
    (hmerge :
      MergeRel (segment input left mid) (segment input mid right) copied) :
    MergeRange input output left mid right := by
  unfold CopyLoopInvariant at h
  rcases h with
    ⟨hlr, _, hrlen, hlength, hcopied, htake, hdrop⟩
  refine ⟨hlm, hmr, hrlen, hlength, ?_, hdrop, ?_⟩
  · have hleftlen : left ≤ input.length := by omega
    have houtleft : output.take left = (output.take right).take left := by
      simp [List.take_take, Nat.min_eq_left hlr]
    rw [houtleft, htake]
    rw [List.take_append, List.length_take_of_le hleftlen]
    rw [List.take_take]
    simp
  · simp only [segment]
    rw [← List.drop_take (i := left) (j := right) (l := output), htake]
    have hleftlen : (input.take left).length = left := List.length_take_of_le (by omega)
    rw [List.drop_append_of_le_length (by omega)]
    simp; exact hmerge

theorem getElem?_of_take_eq_append
    {values pref merged : List UInt32} {left right k : Nat}
    (hright : right ≤ values.length)
    (hpref : pref = values.take left)
    (htake : values.take right = pref ++ merged)
    (hkleft : left ≤ k) (hkright : k < right) :
    values[k]? = merged[k - left]? := by
  subst pref
  have hlookup := congrArg (fun xs : List UInt32 => xs[k]?) htake
  have hleftlen : (values.take left).length = left := List.length_take_of_le (by omega)
  simpa [List.getElem?_take, hkright, List.getElem?_append,
    hleftlen, show ¬k < left by omega] using hlookup

theorem MergeRange.perm {input output : List UInt32} {left mid right : Nat}
    (h : MergeRange input output left mid right) :
    List.Perm input output := by
  rcases h with ⟨hlm, hmr, _, hlength, hprefix, hsuffix, hmerge⟩
  rw [← List.take_extract_drop (values := input) (Nat.le_trans hlm hmr),
    ← List.take_extract_drop (values := output) (Nat.le_trans hlm hmr)]
  rw [hprefix, hsuffix]
  apply List.Perm.append_right
  apply List.Perm.append_left
  rw [← List.extract_append hlm hmr]; exact perm_of_mergeRel hmerge

theorem MergeRange.segment_before
    {input output : List UInt32} {left mid right start stop : Nat}
    (h : MergeRange input output left mid right)
    (hstop : stop ≤ left) :
    segment output start stop = segment input start stop :=
  List.extract_eq_of_take_eq hstop h.2.2.2.2.1

theorem MergeRange.segment_after
    {input output : List UInt32} {left mid right start stop : Nat}
    (h : MergeRange input output left mid right)
    (hstart : right ≤ start) :
    segment output start stop = segment input start stop :=
  List.extract_eq_of_drop_eq hstart h.2.2.2.2.2.1

/-- Every consecutive block of `width` values is sorted.  Blocks are numbered
from zero; the final block may be shorter than `width`. -/
def SortedRuns (values : List UInt32) (width : Nat) : Prop :=
  ∀ block, block * width < values.length →
    Sorted (segment values (block * width)
      (min ((block + 1) * width) values.length))

/-- Mathematical invariant of one left-to-right bottom-up merge pass.

Blocks before `pass` have already been combined into sorted runs of size
`2 * width`; blocks at and after `2 * pass` are still sorted runs of size
`width`.  The permutation conjunct records global element preservation. -/
def MergePassInvariant
    (original current : List UInt32) (width pass : Nat) : Prop :=
  0 < width ∧
  current.length = original.length ∧
  List.Perm original current ∧
  (∀ block, block < pass →
    Sorted (segment current (block * (2 * width))
      (min ((block + 1) * (2 * width)) current.length))) ∧
  (∀ block, 2 * pass ≤ block → block * width < current.length →
    Sorted (segment current (block * width)
      (min ((block + 1) * width) current.length)))

theorem mergePassInvariant_start
    {original current : List UInt32} {width : Nat}
    (hwidth : 0 < width) (hperm : List.Perm original current)
    (hruns : SortedRuns current width) :
    MergePassInvariant original current width 0 := by
  refine ⟨hwidth, hperm.length_eq.symm, hperm, ?_, ?_⟩
  · intro block hblock
    omega
  · intro block _ hblock
    exact hruns block hblock

theorem sortedRuns_one (values : List UInt32) :
    SortedRuns values 1 := by
  intro block _
  apply List.pairwise_of_length_le_one
  simp only [segment, List.length_take, List.length_drop]; omega

theorem MergePassInvariant.finished
    {original current : List UInt32} {width pass : Nat}
    (h : MergePassInvariant original current width pass)
    (hfinished : current.length ≤ pass * (2 * width)) :
    SortedRuns current (2 * width) := by
  intro block hblock
  have hblockPass : block < pass := by
    apply Nat.lt_of_not_ge
    intro hpass
    have hmul := Nat.mul_le_mul_right (2 * width) hpass
    omega
  exact h.2.2.2.1 block hblockPass

theorem sorted_of_sortedRuns_cover
    {values : List UInt32} {width : Nat}
    (hruns : SortedRuns values width)
    (hwidth : values.length ≤ width) :
    Sorted values := by
  cases values with
  | nil => simp [Sorted]
  | cons head tail =>
    have hrun := hruns 0 (by simp)
    have hmin :
        min width (tail.length + 1) = tail.length + 1 :=
      Nat.min_eq_right hwidth
    simpa [segment, hmin] using hrun

theorem MergePassInvariant.step
    {original current output : List UInt32} {width pass : Nat}
    (h : MergePassInvariant original current width pass)
    (hleft :
      pass * (2 * width) < current.length)
    (hmerge : MergeRange current output
      (pass * (2 * width))
      (min (pass * (2 * width) + width) current.length)
      (min (pass * (2 * width) + 2 * width) current.length)) :
    MergePassInvariant original output width (pass + 1) := by
  let left := pass * (2 * width)
  let mid := min (left + width) current.length
  let right := min (left + 2 * width) current.length
  have hleftIndex : (2 * pass) * width = left := by
    simp [left, Nat.mul_left_comm, Nat.mul_comm]
  have hmidIndex : (2 * pass + 1) * width = left + width := by
    rw [Nat.add_mul, hleftIndex]
    simp
  have hrightIndex : (2 * pass + 2) * width = left + 2 * width := by
    rw [Nat.add_mul, hleftIndex]
  have hmerge' : MergeRange current output left mid right := by
    simpa only [left, mid, right] using hmerge
  have houtputLength : output.length = current.length :=
    hmerge'.2.2.2.1
  have hleftSorted : Sorted (segment current left mid) := by
    have hrun := h.2.2.2.2 (2 * pass) (by omega) (by
      rw [hleftIndex]
      simpa only [left] using hleft)
    simpa only [hleftIndex, hmidIndex, mid] using hrun
  have hrightSorted : Sorted (segment current mid right) := by
    by_cases hrightStart :
        (2 * pass + 1) * width < current.length
    · have hrun :=
        h.2.2.2.2 (2 * pass + 1) (by omega) hrightStart
      have hmidEq : mid = left + width := by
        dsimp only [mid]
        rw [Nat.min_eq_left]
        simpa only [← hmidIndex] using Nat.le_of_lt hrightStart
      simpa only [hmidEq, hmidIndex, hrightIndex, right] using hrun
    · have hmidEnd : mid = current.length := by
        dsimp only [mid]
        rw [Nat.min_eq_right]; omega
      have hrightEnd : right = current.length := by
        dsimp only [right]
        rw [Nat.min_eq_right]; omega
      simp [hmidEnd, hrightEnd, segment, Sorted]
  have hmergedSorted : Sorted (segment output left right) :=
    sorted_of_mergeRel hmerge'.2.2.2.2.2.2
      hleftSorted hrightSorted
  refine ⟨h.1, ?_, h.2.2.1.trans hmerge'.perm, ?_, ?_⟩
  · exact houtputLength.trans h.2.1
  · intro block hblock
    by_cases hprior : block < pass
    · have hblockEnd : (block + 1) * (2 * width) ≤ left := by
        have hle : block + 1 ≤ pass := by omega
        have hmul := Nat.mul_le_mul_right (2 * width) hle
        simpa only [left] using hmul
      have hstopLeft :
          min ((block + 1) * (2 * width)) output.length ≤ left :=
        Nat.le_trans (Nat.min_le_left _ _) hblockEnd
      rw [hmerge'.segment_before hstopLeft]
      simpa only [houtputLength] using h.2.2.2.1 block hprior
    · have hblockEq : block = pass := by omega
      subst block
      have hpassEnd : (pass + 1) * (2 * width) =
          pass * (2 * width) + 2 * width := by
        rw [Nat.add_mul]
        simp
      simpa only [left, right, houtputLength, hpassEnd] using hmergedSorted
  · intro block hblock hblockStart
    have hrightStart : right ≤ block * width := by
      have hle : 2 * pass + 2 ≤ block := by omega
      have hmul := Nat.mul_le_mul_right width hle
      exact Nat.le_trans (Nat.min_le_left _ _) (by
        rw [← hrightIndex]; exact hmul)
    rw [houtputLength]
    rw [hmerge'.segment_after hrightStart]; exact h.2.2.2.2 block (by omega) (by
      simpa only [houtputLength] using hblockStart)

end Wasm.Examples.MergeSort
