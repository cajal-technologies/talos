import Project.Mergesort.Spec
import Project.Mergesort.SliceProof

/-!
# Correctness proof for the original generated merge sort

The exact generated-function proof is assembled bottom-up.  Leaf slice
contracts live in `SliceProof`; the merge, recursive sort, and exported text
driver contracts are added here as their dependencies become available.
-/

namespace Project.Mergesort.Proof

open Project.Mergesort.Pure

/-- Mathematical consequence used at the boundary after the generated merge
loop has established its declarative stable-merge relation. -/
theorem merged_halves_are_sorted_permutation [LinearOrder α]
    {left right output : List α}
    (hleft : Sorted left) (hright : Sorted right)
    (hmerge : MergeRel left right output) :
    SortedPermutation (left ++ right) output :=
  sortedPermutation_of_mergeRel hmerge hleft hright

end Project.Mergesort.Proof
