import Project.SwapElements.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `swap_elements`

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
stack (top first) is `[j, i, data_length, array_ptr]`, matching `localGet 0 =
array_ptr, … , localGet 3 = j`.

## Two preconditions beyond the informal contract

The `swap` is only well-defined once the shadow stack and address arithmetic
are pinned down; both facts hold for every store the module actually produces,
but neither is implied by the four informal preconditions, so they are stated
explicitly:

* **`st.globals.globals[0]? = some (.i32 1048576)`** — the shadow-stack pointer
  is at its module-initial value. `func4`/`func2` derive their scratch frames
  as `global 0 − 16` and `global 0 − 32`; without pinning `global 0` the callee
  frames could alias the array (or wrap), and the statement would be *false*.
* **`st.mem.pages ≤ 65536`** — the wasm32 architectural memory limit (the module
  itself declares `pagesMin = 17`). Together with the addressability bound this
  gives `ptr.toNat + 8*len.toNat ≤ 2^32`, so element addresses `ptr + 8*k` do
  not wrap `UInt32`; without it two distinct in-bounds indices could collide (or
  an element could alias the scratch slot) and, again, the statement would fail.

Both mirror the shadow-stack pin already used by e.g. `total_variation` and the
interpreter's own in-bounds model.
-/

namespace Project.SwapElements.Spec

open Wasm

/-- Byte address of the `k`-th `u64` element of an array based at `ptr`. -/
@[reducible] def elemAddr (ptr k : UInt32) : UInt32 := ptr + 8 * k

/-- The exported `swap_elements` swaps two elements of a `[u64]` slice in place.

Given indices `i, j` both in bounds (`< len`); an array region
`[ptr, ptr + 8 * len)` that is addressable (`ptr.toNat + 8 * len.toNat ≤
pages * 65536`), sits at or above the shadow-stack base (`1048576 ≤ ptr`, so the
callee scratch frames cannot alias it), and does not wrap (`pages ≤ 65536`, the
wasm32 limit); and the shadow-stack pointer at its initial value (`global 0 =
1048576`): the export terminates leaving no result and

* the element at index `i` now holds the previous element at index `j`;
* the element at index `j` now holds the previous element at index `i`;
* every other in-bounds element `k` (`k ≠ i`, `k ≠ j`) is unchanged.

See the module docstring for why the last two hypotheses are required — without
them the statement is not merely unprovable but false. -/
@[spec_of "rust-exported" "swap_elements::swap_elements"]
def SwapElementsSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr len i j : UInt32),
    i < len → j < len →
    ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ ptr.toNat →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i32 1048576) →
    TerminatesWith env «module» 4 st
      [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = []
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ k : UInt32, k < len → k ≠ i → k ≠ j →
            st'.mem.read64 (elemAddr ptr k) = st.mem.read64 (elemAddr ptr k))

end Project.SwapElements.Spec
