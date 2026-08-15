import Project.Mergesort.SliceProof

/-!
# Generated merge and recursive-sort proof

The original Rust compiler emits `func125` for `merge::<u64>` and `func126`
for `mergesort::<u64>`.  This file develops their contracts independently of
the text/allocator wrapper.  The first layer below is the exact mathematical
loop invariant for `func125`'s three generated loops.
-/

namespace Project.Mergesort.CoreProof

open Project.Mergesort.Pure

/-- State shared by the generated main loop and its two remainder loops.
`i`, `j`, and `k` are precisely the three `u32` counters stored at frame
offsets 4, 8, and 12 by `func125`. -/
def MergeSlicesInvariant
    (left right scratch : List UInt64) (i j k : Nat)
    (emitted : List UInt64) : Prop :=
  i ≤ left.length ∧
  j ≤ right.length ∧
  scratch.length = left.length + right.length ∧
  k = emitted.length ∧
  emitted.length = i + j ∧
  scratch.take k = emitted ∧
  MergeProgress left right emitted (left.drop i) (right.drop j)

theorem mergeSlicesInvariant_start
    {left right scratch : List UInt64}
    (hlength : scratch.length = left.length + right.length) :
    MergeSlicesInvariant left right scratch 0 0 0 [] := by
  simp [MergeSlicesInvariant, hlength, mergeProgress_start]

private theorem drop_at_cons {values : List UInt64} {index : Nat}
    {value : UInt64} (hindex : index < values.length)
    (hvalue : values[index]? = some value) :
    values.drop index = value :: values.drop (index + 1) := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons head values ih =>
      cases index with
      | zero =>
          simp at hvalue
          subst head
          simp
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simp only [List.getElem?_cons_succ] at hvalue
          simpa [Nat.add_assoc] using ih hindex hvalue

theorem MergeSlicesInvariant.k_lt
    {left right scratch : List UInt64} {i j k : Nat}
    {emitted : List UInt64}
    (h : MergeSlicesInvariant left right scratch i j k emitted)
    (hi : i < left.length) :
    k < scratch.length := by
  unfold MergeSlicesInvariant at h
  omega

theorem MergeSlicesInvariant.takeLeft
    {left right scratch : List UInt64} {i j k : Nat}
    {emitted : List UInt64} {x y : UInt64}
    (h : MergeSlicesInvariant left right scratch i j k emitted)
    (hi : i < left.length) (hj : j < right.length)
    (hx : left[i]? = some x) (hy : right[j]? = some y)
    (hxy : x ≤ y) :
    MergeSlicesInvariant left (right) (scratch.set k x)
      (i + 1) j (k + 1) (emitted ++ [x]) := by
  unfold MergeSlicesInvariant at h ⊢
  rcases h with ⟨hileft, hjright, hlength, hk, hemitted,
    htake, hprogress⟩
  have hklen : k < scratch.length := by omega
  have hleftDrop := drop_at_cons hi hx
  have hrightDrop := drop_at_cons hj hy
  rw [hleftDrop, hrightDrop] at hprogress
  refine ⟨by omega, hjright, by simp [hlength], ?_, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, htake]
  · rw [hrightDrop]
    exact hprogress.takeLeft hxy

theorem MergeSlicesInvariant.takeRight
    {left right scratch : List UInt64} {i j k : Nat}
    {emitted : List UInt64} {x y : UInt64}
    (h : MergeSlicesInvariant left right scratch i j k emitted)
    (hi : i < left.length) (hj : j < right.length)
    (hx : left[i]? = some x) (hy : right[j]? = some y)
    (hxy : ¬x ≤ y) :
    MergeSlicesInvariant left right (scratch.set k y)
      i (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeSlicesInvariant at h ⊢
  rcases h with ⟨hileft, hjright, hlength, hk, hemitted,
    htake, hprogress⟩
  have hklen : k < scratch.length := by omega
  have hleftDrop := drop_at_cons hi hx
  have hrightDrop := drop_at_cons hj hy
  rw [hleftDrop, hrightDrop] at hprogress
  refine ⟨hileft, by omega, by simp [hlength], ?_, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, htake]
  · rw [hleftDrop]
    exact hprogress.takeRight hxy

theorem MergeSlicesInvariant.takeRemainingLeft
    {left right scratch : List UInt64} {i k : Nat}
    {emitted : List UInt64} {x : UInt64}
    (h : MergeSlicesInvariant left right scratch i right.length k emitted)
    (hi : i < left.length) (hx : left[i]? = some x) :
    MergeSlicesInvariant left right (scratch.set k x)
      (i + 1) right.length (k + 1) (emitted ++ [x]) := by
  unfold MergeSlicesInvariant at h ⊢
  rcases h with ⟨hileft, hjright, hlength, hk, hemitted,
    htake, hprogress⟩
  have hklen : k < scratch.length := by omega
  have hleftDrop := drop_at_cons hi hx
  have hrightDrop : right.drop right.length = [] := by simp
  rw [hleftDrop, hrightDrop] at hprogress
  refine ⟨by omega, by omega, by simp [hlength], ?_, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, htake]
  · rw [hrightDrop]
    exact hprogress.takeRemainingLeft

theorem MergeSlicesInvariant.takeRemainingRight
    {left right scratch : List UInt64} {j k : Nat}
    {emitted : List UInt64} {y : UInt64}
    (h : MergeSlicesInvariant left right scratch left.length j k emitted)
    (hj : j < right.length) (hy : right[j]? = some y) :
    MergeSlicesInvariant left right (scratch.set k y)
      left.length (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeSlicesInvariant at h ⊢
  rcases h with ⟨hileft, hjright, hlength, hk, hemitted,
    htake, hprogress⟩
  have hklen : k < scratch.length := by omega
  have hleftDrop : left.drop left.length = [] := by simp
  have hrightDrop := drop_at_cons hj hy
  rw [hleftDrop, hrightDrop] at hprogress
  refine ⟨by omega, by omega, by simp [hlength], ?_, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · rw [take_set_succ hklen, htake]
  · rw [hleftDrop]
    exact hprogress.takeRemainingRight

theorem MergeSlicesInvariant.finished
    {left right scratch : List UInt64} {k : Nat}
    {emitted : List UInt64}
    (h : MergeSlicesInvariant left right scratch
      left.length right.length k emitted) :
    scratch = emitted ∧ MergeRel left right emitted := by
  unfold MergeSlicesInvariant at h
  rcases h with ⟨_, _, hlength, hk, hemitted, htake, hprogress⟩
  have hscratch : k = scratch.length := by omega
  have hleftDrop : left.drop left.length = [] := by simp
  have hrightDrop : right.drop right.length = [] := by simp
  rw [hscratch, List.take_length] at htake
  rw [hleftDrop, hrightDrop] at hprogress
  refine ⟨htake, ?_⟩
  simpa using hprogress [] (.leftNil [])

theorem MergeSlicesInvariant.sortedPermutation
    {left right scratch : List UInt64} {k : Nat}
    {emitted : List UInt64}
    (h : MergeSlicesInvariant left right scratch
      left.length right.length k emitted)
    (hleft : Sorted left) (hright : Sorted right) :
    SortedPermutation (left ++ right) scratch := by
  rcases h.finished with ⟨rfl, hmerge⟩
  exact sortedPermutation_of_mergeRel hmerge hleft hright

/-- Function-level mathematical postcondition for generated `func125`. -/
def MergePost (left right output : List UInt64) : Prop :=
  MergeRel left right output

/-- Function-level mathematical postcondition for generated `func126`. -/
def SortPost (input output : List UInt64) : Prop :=
  SortedPermutation input output

end Project.Mergesort.CoreProof
