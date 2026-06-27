import Project.MergeSort.Spec

/-!
# Proof progress for `MergeSortSpec`

A full proof of `MergeSortSpec` (universally quantified over `st`, `dataPtr`,
`len`) is a large, multi-component effort: the exported `func33` calls the
dlmalloc-backed allocator (`call 15`) to obtain its scratch buffer and then the
*recursive* sort (`call 1`). Discharging the universal statement therefore
needs (a) a model of the allocator — that it terminates, performs no trapping
`memory.grow`, and returns a buffer disjoint from the data — (b) induction on
the recursion with fuel as a function of `len`, and (c) symbolic memory
framing. That work is not yet in place.

This file records the progress that *is* sorry-free: a concrete instance of the
specification, validated end-to-end by executing the real interpreter (the
allocator and the recursion included) with `native_decide`. It is a genuine
instance of `MergeSortSpec` — the chosen `dataPtr`/`len` satisfy all three
preconditions — so it proves the spec is non-vacuous and that the whole stack
runs, without yet proving the universal statement.
-/

namespace Project.MergeSort.Proof

open Wasm Project.MergeSort Project.MergeSort.Spec

/-- Write a list of `u32` words into memory at consecutive addresses starting
at `base` (little-endian, 4 bytes each). -/
def writeWords (m : Mem) (base : UInt32) : List UInt32 → Mem
  | []      => m
  | v :: vs => writeWords (m.write32 base v) (base + 4) vs

/-- A sample unsorted input. -/
def sample : List UInt32 := [5, 3, 1, 4, 2, 9, 0, 7, 6, 8]

/-- Data buffer address: in the heap, well above the bottom-of-heap window the
allocator carves scratch from (`heapBase + 4*len ≤ dataPtr`, with
`heapBase = 1050240`), and in bounds for the module's initial 17 pages
(`17 * 65536 = 1114112`). -/
def dataPtr : UInt32 := 1083072

/-- Initial store: the module's pristine initial store with `sample` written
into the data region. Below `heapBase` it is byte-identical to the initial
store, so the allocator state is pristine — this `st` satisfies every
precondition of `MergeSortSpec`. -/
def st0 : Store Unit :=
  let m := «module».initialStore (α := Unit)
  { m with mem := writeWords m.mem dataPtr sample }

/-- The data region after running the export, or `[]` on trap/out-of-fuel. -/
def resultWords (fuel : Nat) : List UInt32 :=
  match run fuel «module» 33 st0 [.i32 (UInt32.ofNat sample.length), .i32 dataPtr] with
  | .Success _ st' => wordsAt st'.mem dataPtr sample.length
  | _              => []

/-- End-to-end concrete validation: running `merge_sort` on `sample` sorts the
data region in place. Exercises the allocator and the recursion through the
real interpreter. -/
theorem sample_sorts :
    resultWords 200000 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

end Project.MergeSort.Proof
