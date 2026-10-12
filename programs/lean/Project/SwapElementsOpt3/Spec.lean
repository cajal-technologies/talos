import Project.SwapElementsOpt3.Program
import Project.SwapElementsOpt3.SmallStepEquivalence

/-!
# Specification and proof for `swap_elements_opt3`

The `opt-level = 3` build of byte-for-byte the same Rust source as
`swap_elements`:

```rust
pub fn swap_elements(arr: &mut [u64], i: usize, j: usize) {
    arr.swap(i, j);
}
```

## What the optimiser did

At `opt-level = 0` the export (`func4`) carves a 16-byte shadow-stack frame,
materialises the slice fat pointer through memory, and forwards through a
four-deep call chain (`func3`/`func0`/`func1`/`func2`), exchanging the two
elements via a **scratch slot** at `1048552`.

At `opt-level = 3` the whole thing collapses into the exported `func0`: it
bounds-checks `i, j < len` (both `panic` branches are unreachable under the
preconditions), computes the two element addresses, and performs the exchange
with two `i64.load`s and two `i64.store`s through an `i64` local. It never
reads or writes `global 0`, and it never touches the scratch slot.

Consequently this build needs *strictly fewer* preconditions than the opt0 one:
no shadow-stack pin on `global 0`, and no `1048576 ≤ ptr` (there is no scratch
frame for the array to alias). The two builds' final memories therefore are not
the same function — opt0 additionally writes the scratch slot at
`[1048552, 1048560)`, which this build never touches — while agreeing on the
array itself. Relating them is the subject of
`Project.SwapElementsOpt3.Equivalence`.
-/

namespace Project.SwapElementsOpt3.Spec

open Wasm

set_option maxRecDepth 1048576

structure Input where
  ptr : UInt32
  len : UInt32
  i   : UInt32
  j   : UInt32
  xs  : List UInt64

abbrev Output := List UInt64

def args (input : Input) : ExportCall Unit :=
  { initial   := SmallStepEquivalence.opt3InitialStore input.ptr input.xs
    arguments := [.i32 input.j, .i32 input.i, .i32 input.len, .i32 input.ptr] }

def result (input : Input) (output : Output) : ExportReturn Unit → Prop :=
  fun returned =>
    returned.values = [] ∧
    returned.final.mem.words64 input.ptr input.xs.length = output

abbrev Runs := RunsExportWith (HostEnv.empty : HostEnv Unit) «module»

/-- The optimized exported `swap_elements` swaps two elements of a `[u64]`
slice in place.

Pre-written array `xs` at byte offset `ptr`; indices `i`, `j` both in bounds,
with equal indices allowed. The result is the list with positions `i` and `j`
exchanged, read back over the whole slice with `Mem.words64`. No shadow
stack or global-0 pin is required, since this build never touches either. -/
@[spec_of "rust-exported" "swap_elements_opt3::swap_elements"]
def SwapElementsOpt3Spec : Prop :=
  ∀ input : Input,
    input.xs.length = input.len.toNat →
    input.i < input.len →
    input.j < input.len →
    input.ptr.toNat + 8 * input.xs.length < UInt32.size →
    input.ptr.toNat + 8 * input.xs.length ≤
        («module».initialStore : Store Unit).mem.pages * 65536 →
    ∃ output : Output,
      Runs "swap_elements" (args input) (result input output) ∧
      output =
        (input.xs.set input.i.toNat (input.xs.getD input.j.toNat 0)).set
          input.j.toNat (input.xs.getD input.i.toNat 0)

@[proves SwapElementsOpt3Spec]
theorem swap_elements_opt3_correct : SwapElementsOpt3Spec := by
  intro input hlen hi hj hroom hpages
  refine ⟨_, ?_, rfl⟩
  unfold Runs RunsExportWith
  refine ⟨SmallStepEquivalence.opt3ConfigFromStore
      (SmallStepEquivalence.opt3InitialStore input.ptr input.xs)
      input.ptr input.len input.i input.j, rfl, ?_⟩
  simpa [result, Mem.readWords64_eq_words64] using
    SmallStepEquivalence.opt3_initialStore_terminatesWith_array
      input.ptr input.len input.i input.j input.xs
      hlen hi hj hroom hpages

end Project.SwapElementsOpt3.Spec
