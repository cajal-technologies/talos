import Project.MergeSort.Program
import Mathlib.Data.List.Sort

/-!
# Specification for `merge_sort`

The wasm export `merge_sort(data_ptr, len)` (func index 33) sorts the `len`
little-endian `u32` words stored at `data_ptr` into ascending order, **in
place**. Unlike the earlier scratch-passing version, the caller now supplies
only the data buffer: the equal-sized scratch space is allocated **inside** the
call (a `Vec`), so the Rust allocator — and, transitively, `memory.grow` — is
now part of the verified call graph.

The behavioural part of the spec is unchanged and still the standard
total-correctness statement of a sort:

* **sortedness** — after the call, the data region is `List.Pairwise (· ≤ ·)`
  (every earlier word is `≤` every later one, i.e. ascending order);
* **permutation** — after the call, the data region is a `Perm`utation of the
  data region before the call (so no element is invented or lost).

What changed is the *precondition* side. See the `MergeSortSpec` docstring for
the new obligations the internal allocation forces into the statement.

The proof is deferred: only the statement is given here (no `@[proves]`
theorem yet), matching the project convention of never committing `sorry`.
-/

namespace Project.MergeSort.Spec

open Wasm

/-- The `n` consecutive little-endian `u32` words stored in memory `m`
starting at byte address `base`. Element `i` lives at `base + 4 * i`. This is
the view of a `[u32]` slice that the wasm code reads and writes. -/
def wordsAt (m : Mem) (base : UInt32) (n : Nat) : List UInt32 :=
  (List.range n).map (fun i => m.read32 (base + 4 * UInt32.ofNat i))

/-! ## Memory layout constants (from `«module»`)

LLVM's wasm layout for this module places the shadow stack below `1048576`
(global 0, the stack pointer), the static data and the allocator's mutable
bookkeeping in `[…, 1050240)`, and the heap at and above `1050240` (global 2,
`__heap_base`). The data buffer must live in the heap, and the allocator hands
out the scratch buffer from the heap as well. -/

/-- `__heap_base` for `«module»` (init value of global 2). -/
def heapBase : Nat := 1050240

/-- The exported `merge_sort(data_ptr, len)` sorts the `len`-word region at
`data_ptr` ascending, in place, allocating its scratch buffer internally.

## Behaviour (postcondition)

The call terminates, returns no values, and leaves the data region a sorted
permutation of its original contents.

## Preconditions — and the new allocator obligations

The data buffer must be a valid heap region:

* `data_ptr + 4*len ≤ pages * 65536` (in bounds). That the buffer is *in the
  heap* (`heapBase ≤ data_ptr`) follows from the scratch margin below, so it is
  not stated as a separate hypothesis.

Because scratch is now allocated *inside* the call rather than supplied, the
statement also has to constrain the heap so that the allocation behaves. These
are the genuinely new pieces of what we must verify going forward, and they are
stated here as concrete (if conservative) hypotheses:

* **Pristine allocator state.** `st` agrees with the module's initial store on
  every byte below `heapBase`. That region holds the allocator's mutable
  control state, so this pins it to "fresh" — the first internal `malloc`
  initialises the heap from the bottom upward.
* **Scratch lands clear of the data (provisional margin).**
  `heapBase + 4*len ≤ data_ptr`, i.e. the data buffer sits above a free window
  at the bottom of the heap large enough for the scratch buffer. With a
  pristine allocator the scratch chunk is carved from that bottom window, so it
  ends up disjoint from the data. The *exact* margin is dlmalloc's chunk
  overhead; pinning it down precisely (and discharging the allocator's
  termination, the non-trapping of any `memory.grow` it performs, and the
  disjointness it guarantees) is the deferred allocator-verification work this
  signature change deliberately pulls in. -/
@[spec_of "rust-exported" "merge_sort::merge_sort"]
def MergeSortSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (dataPtr len : UInt32),
    let n   := len.toNat
    let dLo := dataPtr.toNat
    let dHi := dLo + 4 * n
    -- data buffer in bounds (its lower end is constrained by the scratch
    -- margin below, which already implies `heapBase ≤ dLo`)
    dHi ≤ st.mem.pages * 65536 →
    -- allocator control state is pristine (see docstring)
    (∀ i, i < heapBase → st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i) →
    -- scratch fits in the free window below the data buffer (provisional);
    -- this also places the data buffer in the heap (`heapBase ≤ dLo`)
    heapBase + 4 * n ≤ dLo →
    TerminatesWith env «module» 33 st [.i32 len, .i32 dataPtr]
      (fun st' rs =>
        -- no return values …
        rs = [] ∧
        -- … the data region is sorted ascending …
        (wordsAt st'.mem dataPtr n).Pairwise (· ≤ ·) ∧
        -- … and is a permutation of the original data region.
        (wordsAt st'.mem dataPtr n).Perm (wordsAt st.mem dataPtr n))

end Project.MergeSort.Spec
