import Project.SwapElementsOpt3.Program
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic

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

/-- Byte address of the `k`-th `u64` element of an array based at `ptr`. -/
@[reducible] def elemAddr (ptr k : UInt32) : UInt32 := ptr + 8 * k

/-- Address arithmetic the codegen emits: `(k <<< 3) + ptr = elemAddr ptr k`. -/
theorem elemAddr_of_shl (ptr k : UInt32) : k <<< (3 % 32 : UInt32) + ptr = elemAddr ptr k :=
  MemRegion.slot64_of_shl ptr k

/-- No address wraparound: for an element index whose byte offset stays below
`2^32`, the wasm address `ptr + 8*k` is the true integer `ptr.toNat + 8*k.toNat`. -/
theorem elemAddr_toNat (ptr k : UInt32) (h : ptr.toNat + 8 * k.toNat < 4294967296) :
    (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat :=
  MemRegion.slot64_base_toNat ptr k h

/-- `func0` (index 0, the export): bounds checks fused with the exchange. -/
theorem func0_swap (env : HostEnv Unit) (st : Store Unit) (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hbound : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages ≤ 65536) :
    TerminatesWith env «module» 0 st [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' vs => vs = []
        ∧ st'.mem =
            (st.mem.write64 (elemAddr ptr i) (st.mem.read64 (elemAddr ptr j))).write64
              (elemAddr ptr j) (st.mem.read64 (elemAddr ptr i))) := by
  have hbnd : st.mem.pages * 65536 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hli : i.toNat < len.toNat := hi
  have hlj : j.toNat < len.toNat := hj
  have hwi : ptr.toNat + 8 * i.toNat < 4294967296 := by omega
  have hwj : ptr.toNat + 8 * j.toNat < 4294967296 := by omega
  have gpi : ¬ (st.mem.pages * 65536 < (elemAddr ptr i).toNat + 8) := by
    rw [elemAddr_toNat ptr i hwi]; omega
  have gpj : ¬ (st.mem.pages * 65536 < (elemAddr ptr j).toNat + 8) := by
    rw [elemAddr_toNat ptr j hwj]; omega
  -- the two `panic` branches: `i, j < len` refutes each `geU` test
  have hgi : ¬ (i ≥ len) := by intro h; have : len.toNat ≤ i.toNat := h; omega
  have hgj : ¬ (j ≥ len) := by intro h; have : len.toNat ≤ j.toNat := h; omega
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  apply wp_block_cons
  apply wp_block_cons
  simp only [wp_simp, Locals.get, Locals.set?, Function.toLocals,
    Function.numParams, List.take, List.drop,
    List.length, List.map, ValueType.zero,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte,
    UInt32.reduceToNat, UInt32.add_zero, Mem.write64_pages,
    hgi, hgj, elemAddr_of_shl, gpi, gpj]
  exact ⟨trivial, trivial⟩

end Project.SwapElementsOpt3.Spec
