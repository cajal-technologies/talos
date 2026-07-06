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
-/

namespace Project.SwapElements.Spec

open Wasm

/-- Byte address of the `k`-th `u64` element of an array based at `ptr`. -/
@[reducible] def elemAddr (ptr k : UInt32) : UInt32 := ptr + 8 * k

/-- The exported `swap_elements` swaps two elements of a `[u64]` slice in place.

Informal spec. Given indices `i, j` both in bounds (`< len`) and an array region
`[ptr, ptr + 8 * len)` that sits at or above the shadow-stack base (global 0 is
initialised to `1048576`), so the callee's 16-byte scratch frame at
`[1048560, 1048576)` cannot alias the array, the export terminates leaving no
result and:

* the element at index `i` now holds the previous element at index `j`;
* the element at index `j` now holds the previous element at index `i`;
* every other element `k < len` (`k ≠ i`, `k ≠ j`) is unchanged.

The bound `8 * len.toNat ≤ ...` precondition keeps the array inside addressable
memory and rules out address wraparound of the element offsets.

No proof is attempted here: only the statement is registered. -/
@[spec_of "rust-exported" "swap_elements::swap_elements"]
def SwapElementsSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr len i j : UInt32),
    -- indices in bounds
    i < len → j < len →
    -- the array is addressable and its element offsets do not wrap UInt32
    ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536 →
    -- memory fits in 32-bit address space (standard wasm constraint: pages ≤ 65536)
    st.mem.pages * 65536 ≤ 4294967296 →
    -- the array does not collide with the callee's shadow-stack scratch frame
    1048576 ≤ ptr.toNat →
    -- shadow-stack pointer at the wasm shadow-stack base on entry
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
