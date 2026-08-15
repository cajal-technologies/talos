import Project.Mergesort.Spec
import Project.Mergesort.CoreProof
import Project.Mergesort.RangeProof
import Project.Mergesort.MemoryCopyProof
import Project.Mergesort.MemoryFillProof
import Project.Mergesort.CopySliceProof
import Project.Mergesort.SplitAtProof
import Project.Mergesort.VectorProof
import Project.Mergesort.VecFromElemProof
import Project.Mergesort.IteratorProof
import Project.Mergesort.OutputIteratorProof
import Project.Mergesort.FormatProof
import Project.Mergesort.ArgumentsProof
import Project.Mergesort.StringProof
import Project.Mergesort.MergeFunctionProof
import Project.Mergesort.SortFunctionProof
import Project.Mergesort.TextProof
import Project.Mergesort.ParseByteProof
import Project.Mergesort.ParseProof
import Project.Mergesort.WideMulProof
import Project.Mergesort.DriverProof
import Project.Mergesort.StdIOWrapperProof

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

/-- Once the generated recursive body has established `SortRel`, no Wasm or
memory details remain in the public mathematical correctness argument. -/
theorem sort_execution_is_correct {input output : List UInt64}
    (hsort : Pure.SortRel input output) :
    Spec.SortedPermutation input output :=
  Pure.sortedPermutation_of_sortRel hsort

end Project.Mergesort.Proof
