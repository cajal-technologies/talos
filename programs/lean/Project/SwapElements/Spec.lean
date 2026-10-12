import Project.SwapElements.SwapSepLogic

/-!
# Specification and proof for `swap_elements`

The Rust source is

```rust
pub fn swap_elements(arr: &mut [u64], i: usize, j: usize) {
    arr.swap(i, j);
}
```

exposed across the wasm ABI as

```rust
pub extern "C" fn swap_elements(
    array_ptr: *mut u64, data_length: usize, i: usize, j: usize,
)
```

so the export receives four `i32` values `(array_ptr, data_length, i, j)`,
reconstitutes the slice `[array_ptr, array_ptr + 8 * data_length)` of 8-byte
`u64` elements, and swaps the elements at indices `i` and `j`.

The element at logical index `k` lives at byte address `array_ptr + 8 * k`
(elements are `u64`, eight bytes wide), read/written with `Mem.read64` /
`Mem.write64`.

Wasm's calling convention pushes arguments left-to-right, so the entry's value
stack (top first) is `[j, i, data_length, array_ptr]`.

## Preconditions

* `xs.length = len.toNat` — `len` is the slice length in elements.
* `i < len`, `j < len` — both indices are in bounds.
* `ptr.toNat + 8 * xs.length < UInt32.size` — the array region does not wrap.
* `1048576 ≤ ptr.toNat` — the array is above the shadow-stack base, so callee
  scratch frames cannot alias it; `func4`/`func2` allocate frames below 1048576.
* `ptr.toNat + 8 * xs.length ≤ pages * 65536` — the region is in addressable
  memory; the module declares `pagesMin = 17` (≥ 1 MiB).

The initial store is `func4InitialStore ptr xs`, which is the module's default
initial store with `xs` pre-written at byte offset `ptr`.
-/

namespace Project.SwapElements.Spec

open Wasm
open Project.SwapElements.SwapSepLogic

structure Input where
  ptr : UInt32
  len : UInt32
  i   : UInt32
  j   : UInt32
  xs  : List UInt64

abbrev Output := List UInt64

def args (input : Input) : ExportCall Unit :=
  { initial   := func4InitialStore input.ptr input.xs
    arguments := [.i32 input.j, .i32 input.i, .i32 input.len, .i32 input.ptr] }

def result (input : Input) (output : Output) : ExportReturn Unit → Prop :=
  fun returned =>
    returned.values = [] ∧
    returned.final.mem.words64 input.ptr input.xs.length = output

abbrev Runs := RunsExportWith (HostEnv.empty : HostEnv Unit) «module»

/-- The exported `swap_elements` swaps two elements of a `[u64]` slice in place.

Contract: the array `xs` is written at byte offset `ptr` in the module's
initial memory, with `xs.length = len` and `i`, `j` both in bounds; equal
indices are allowed. The slice must not wrap the 32-bit address space and must
fit in the initial memory, and `ptr ≥ 1048576` because the generated frames
live below that address. The export returns no values, and the slice reads
back as `xs` with positions `i` and `j` exchanged. -/
@[spec_of "rust-exported" "swap_elements::swap_elements"]
def SwapElementsSpec : Prop :=
  ∀ input : Input,
    input.xs.length = input.len.toNat →
    input.i < input.len →
    input.j < input.len →
    input.ptr.toNat + 8 * input.xs.length < UInt32.size →
    1048576 ≤ input.ptr.toNat →
    input.ptr.toNat + 8 * input.xs.length ≤
        («module».initialStore : Store Unit).mem.pages * 65536 →
    ∃ output : Output,
      Runs "swap_elements" (args input) (result input output) ∧
      output =
        (input.xs.set input.i.toNat (input.xs.getD input.j.toNat 0)).set
          input.j.toNat (input.xs.getD input.i.toNat 0)

@[proves Project.SwapElements.Spec.SwapElementsSpec]
theorem swap_elements_correct : SwapElementsSpec := by
  intro input hlen hi hj hroom hbase hpages
  refine ⟨_, ?_, rfl⟩
  unfold Runs RunsExportWith
  refine ⟨func4ConfigFromStore (func4InitialStore input.ptr input.xs)
      input.ptr input.len input.i input.j, rfl, ?_⟩
  simpa [result, Mem.readWords64_eq_words64] using
    func4_initialStore_terminatesWith_array
      input.ptr input.len input.i input.j input.xs
      hlen hi hj hroom hbase hpages

end Project.SwapElements.Spec
