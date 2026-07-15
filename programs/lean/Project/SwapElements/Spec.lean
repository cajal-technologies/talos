import Project.SwapElements.Program
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic

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
stack (top first) is `[j, i, data_length, array_ptr]`, matching `localGet 0 =
array_ptr, … , localGet 3 = j`.

## Call graph (opt-level 0)

`func4` (the export) allocates a 16-byte shadow-stack frame, calls `func3` to
materialise the slice fat pointer `(ptr, len)` into that frame, reads it back,
and calls `func0`. `func0` forwards to `func1`, which bounds-checks `i, j < len`
(the two `panic` branches are unreachable under the precondition) and calls
`func2`, the leaf that performs the exchange through a scratch slot.

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

/-! ## Address arithmetic -/

/-- `x <<< 3 = 8 * x` on `UInt32`, matching the wasm `(const 3) shl`. -/
theorem shl3 (x : UInt32) : x <<< (3 % 32 : UInt32) = 8 * x := by bv_decide

/-- Address arithmetic the codegen emits: `(k <<< 3) + ptr = elemAddr ptr k`. -/
theorem elemAddr_of_shl (ptr k : UInt32) : k <<< (3 % 32 : UInt32) + ptr = elemAddr ptr k := by
  simp only [elemAddr]; bv_decide

/-- No address wraparound: for an element index whose byte offset stays below
`2^32`, the wasm address `ptr + 8*k` is the true integer `ptr.toNat + 8*k.toNat`. -/
theorem elemAddr_toNat (ptr k : UInt32) (h : ptr.toNat + 8 * k.toNat < 4294967296) :
    (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat := by
  simp only [elemAddr, UInt32.toNat_add, UInt32.toNat_mul, UInt32.reduceToNat]
  omega

/-- Two distinct in-bounds element addresses are 8-byte disjoint. -/
theorem elemAddr_disjoint (ptr k l : UInt32)
    (hk : ptr.toNat + 8 * k.toNat < 4294967296) (hl : ptr.toNat + 8 * l.toNat < 4294967296)
    (hkl : k ≠ l) :
    (elemAddr ptr k).toNat + 8 ≤ (elemAddr ptr l).toNat
      ∨ (elemAddr ptr l).toNat + 8 ≤ (elemAddr ptr k).toNat := by
  rw [elemAddr_toNat ptr k hk, elemAddr_toNat ptr l hl]
  have : k.toNat ≠ l.toNat := fun he => hkl (UInt32.toNat.inj he)
  omega

/-! ## `func2`: the exchange leaf -/

/-- `func2` (index 2) swaps the two `u64` values at `pi` and `pj` using a
scratch slot at `1048552` (= `global0 − 16 + 8` with `global0 = 1048560`).
Stated with an explicit final-memory equation so callers can frame reads. -/
theorem func2_swap (env : HostEnv Unit) (st : Store Unit) (pi pj : UInt32)
    (rest : List Value)
    (hg : st.globals.globals[0]? = some (.i32 1048560))
    (hpiN : 1048576 ≤ pi.toNat) (hpiHi : pi.toNat + 8 ≤ st.mem.pages * 65536)
    (hpjN : 1048576 ≤ pj.toNat) (hpjHi : pj.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 2 st (.i32 pj :: .i32 pi :: rest)
      (fun st' vs => vs = rest ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem =
            ((st.mem.write64 1048552 (st.mem.read64 pi)).write64 pi
              (st.mem.read64 pj)).write64 pj (st.mem.read64 pi)) := by
  have c52 : (1048552 : UInt32).toNat = 1048552 := by decide
  have gpi : ¬ (st.mem.pages * 65536 < pi.toNat + 8) := by omega
  have gpj : ¬ (st.mem.pages * 65536 < pj.toNat + 8) := by omega
  have gscr : ¬ (st.mem.pages * 65536 < 1048560) := by omega
  have e1 : (st.mem.write64 1048552 (st.mem.read64 pi)).read64 pj = st.mem.read64 pj :=
    Mem.read64_write64_disjoint _ _ _ _ (Or.inr (by omega))
  have e2 : ((st.mem.write64 1048552 (st.mem.read64 pi)).write64 pi
              (st.mem.read64 pj)).read64 1048552 = st.mem.read64 pi := by
    rw [Mem.read64_write64_disjoint _ _ _ _ (Or.inl (by omega)), Mem.read64_write64_same]
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [.i32], func2, [], none⟩) rfl
  unfold func2
  wp_run
  rw [hg]
  simp [gpi, gpj, gscr, e1, e2]

/-! ## `func1`: the bounds checks -/

/-- `func1` (index 1): bounds-checks `i, j < len` (both panic branches are
unreachable under the preconditions) and calls `func2` on `&arr[i]`, `&arr[j]`. -/
theorem func1_swap (env : HostEnv Unit) (st1 : Store Unit) (ptr len i j loc : UInt32)
    (rest : List Value)
    (hg : st1.globals.globals[0]? = some (.i32 1048560))
    (hi : i < len) (hj : j < len)
    (hptr : 1048576 ≤ ptr.toNat)
    (hbound : ptr.toNat + 8 * len.toNat ≤ st1.mem.pages * 65536)
    (hpages : st1.mem.pages ≤ 65536) :
    TerminatesWith env «module» 1 st1
      (.i32 loc :: .i32 j :: .i32 i :: .i32 len :: .i32 ptr :: rest)
      (fun st' vs => vs = rest ∧ st'.globals = st1.globals ∧ st'.mem.pages = st1.mem.pages
        ∧ st'.mem =
            ((st1.mem.write64 1048552 (st1.mem.read64 (elemAddr ptr i))).write64 (elemAddr ptr i)
              (st1.mem.read64 (elemAddr ptr j))).write64 (elemAddr ptr j)
              (st1.mem.read64 (elemAddr ptr i))) := by
  have hbnd : st1.mem.pages * 65536 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hwi : ptr.toNat + 8 * i.toNat < 4294967296 := by
    have hli : i.toNat < len.toNat := hi; omega
  have hwj : ptr.toNat + 8 * j.toNat < 4294967296 := by
    have hlj : j.toNat < len.toNat := hj; omega
  have hpiN : 1048576 ≤ (elemAddr ptr i).toNat := by rw [elemAddr_toNat ptr i hwi]; omega
  have hpjN : 1048576 ≤ (elemAddr ptr j).toNat := by rw [elemAddr_toNat ptr j hwj]; omega
  have hpiHi : (elemAddr ptr i).toNat + 8 ≤ st1.mem.pages * 65536 := by
    rw [elemAddr_toNat ptr i hwi]
    have hli : i.toNat < len.toNat := hi; omega
  have hpjHi : (elemAddr ptr j).toNat + 8 ≤ st1.mem.pages * 65536 := by
    rw [elemAddr_toNat ptr j hwj]
    have hlj : j.toNat < len.toNat := hj; omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32, .i32], [.i32], func1, [], none⟩) rfl
  unfold func1
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  simp only [wp_simp, Locals.get, Locals.set?, Function.toLocals,
    Function.numParams, List.take, List.drop, 
    List.length, List.map, ValueType.zero, 
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.append_nil,
    
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte,
    hi, hj, elemAddr_of_shl,
    show ((1 : UInt32) &&& 1) = 1 from rfl, show ((1 : UInt32) = 0) = False from by simp]
  apply wp_call_tw (func2_swap env st1 (elemAddr ptr i) (elemAddr ptr j) []
    hg hpiN hpiHi hpjN hpjHi)
  rintro st' vs ⟨rfl, hglob, hpg, hmem⟩
  wp_run
  exact ⟨trivial, hglob, hpg, hmem⟩

/-! ## `func0`: the forwarder -/

/-- `func0` (index 0): forwards `(ptr, len, i, j)` plus the panic-location
constant to `func1`. -/
theorem func0_swap (env : HostEnv Unit) (st0 : Store Unit) (ptr len i j : UInt32)
    (rest : List Value)
    (hg : st0.globals.globals[0]? = some (.i32 1048560))
    (hi : i < len) (hj : j < len)
    (hptr : 1048576 ≤ ptr.toNat)
    (hbound : ptr.toNat + 8 * len.toNat ≤ st0.mem.pages * 65536)
    (hpages : st0.mem.pages ≤ 65536) :
    TerminatesWith env «module» 0 st0
      (.i32 j :: .i32 i :: .i32 len :: .i32 ptr :: rest)
      (fun st' vs => vs = rest ∧ st'.globals = st0.globals ∧ st'.mem.pages = st0.mem.pages
        ∧ st'.mem =
            ((st0.mem.write64 1048552 (st0.mem.read64 (elemAddr ptr i))).write64 (elemAddr ptr i)
              (st0.mem.read64 (elemAddr ptr j))).write64 (elemAddr ptr j)
              (st0.mem.read64 (elemAddr ptr i))) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [], func0, [], none⟩) rfl
  unfold func0
  wp_run
  apply wp_call_tw (func1_swap env st0 ptr len i j 1048604 [] hg hi hj hptr hbound hpages)
  rintro st' vs ⟨rfl, hglob, hpg, hmem⟩
  wp_run
  exact ⟨by simp, hglob, hpg, hmem⟩

/-! ## `func3`: materialise the slice fat pointer -/

/-- `func3` (index 3): writes the slice fat pointer `(a, b)` to `[dest, dest+8)`
(`store32` of `b` at `dest+4`, then `a` at `dest`). -/
theorem func3_writes (env : HostEnv Unit) (st : Store Unit) (dest a b c : UInt32)
    (rest : List Value)
    (hdlt : dest.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 3 st (.i32 c :: .i32 b :: .i32 a :: .i32 dest :: rest)
      (fun st' vs => vs = rest ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem = (st.mem.write32 (dest + 4) b).write32 dest a) := by
  have g1 : ¬ (st.mem.pages * 65536 < dest.toNat + 4 + 4) := by omega
  have g2 : ¬ (st.mem.pages * 65536 < dest.toNat + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [], func3, [], none⟩) rfl
  unfold func3
  wp_run
  simp [g1, g2]

/-! ## `func4`: the export -/

/-- Byte addresses of the fat-pointer frame slots. -/
private theorem tn68 : (1048568 : UInt32).toNat = 1048568 := by decide
private theorem tn72 : (1048572 : UInt32).toNat = 1048572 := by decide
private theorem tn52 : (1048552 : UInt32).toNat = 1048552 := by decide

/-- A `read64` at any array address (≥ 1048576) ignores `func3`'s two
`store32`s into the fat-pointer frame at `[1048568, 1048576)`. -/
private theorem frame_read64 (m : Mem) (len ptr x : UInt32) (hx : 1048576 ≤ x.toNat) :
    ((m.write32 1048572 len).write32 1048568 ptr).read64 x = m.read64 x := by
  rw [Mem.read64_write32_disjoint _ _ _ _ (Or.inl (by rw [tn68]; omega)),
      Mem.read64_write32_disjoint _ _ _ _ (Or.inl (by rw [tn72]; omega))]

/-- `func4` (index 4, the export): frame setup → `func3` → read the fat pointer
back → `func0` → frame teardown. Total-correctness swap over the array. -/
theorem func4_swap (env : HostEnv Unit) (st : Store Unit) (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hptr : 1048576 ≤ ptr.toNat)
    (hbound : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages ≤ 65536)
    (hsp : st.globals.globals[0]? = some (.i32 1048576)) :
    TerminatesWith env «module» 4 st [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs => rs = []
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ k : UInt32, k < len → k ≠ i → k ≠ j →
            st'.mem.read64 (elemAddr ptr k) = st.mem.read64 (elemAddr ptr k)) := by
  have hbnd : st.mem.pages * 65536 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hwi : ptr.toNat + 8 * i.toNat < 4294967296 := by
    have h : i.toNat < len.toNat := hi; omega
  have hwj : ptr.toNat + 8 * j.toNat < 4294967296 := by
    have h : j.toNat < len.toNat := hj; omega
  have hpiN : 1048576 ≤ (elemAddr ptr i).toNat := by rw [elemAddr_toNat ptr i hwi]; omega
  have hpjN : 1048576 ≤ (elemAddr ptr j).toNat := by rw [elemAddr_toNat ptr j hwj]; omega
  obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hsp
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32], func4, [], none⟩) rfl
  unfold func4
  wp_run
  rw [hsp]
  simp only [wp_simp, 
    
    List.length, 
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.append_nil,
    List.length_cons, 
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ,
    UInt32.reduceSub, UInt32.reduceAdd, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte,
    ]
  apply wp_call_tw (func3_writes env _ 1048568 ptr len 1048652 []
    (by show (1048568 : UInt32).toNat + 8 ≤ st.mem.pages * 65536; rw [tn68]; omega))
  rintro sta vsa ⟨rfl, hga, hpa, hma⟩
  simp only [UInt32.reduceAdd] at hma
  have hpg_a : sta.mem.pages = st.mem.pages := by rw [hma]; simp
  have hglob0 : sta.globals.globals[0]? = some (.i32 1048560) := by
    rw [hga]; exact List.getElem?_set_self hlen
  have hrlen : sta.mem.read32 1048572 = len := by
    rw [hma, Mem.read32_write32_disjoint _ _ _ _ (by rw [tn68, tn72]; omega),
        Mem.read32_write32_same]
  have hrptr : sta.mem.read32 1048568 = ptr := by rw [hma, Mem.read32_write32_same]
  simp only [wp_simp, Locals.get, Locals.set?, 
    
    List.length, 
    
    
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ,
    UInt32.reduceToNat, UInt32.reduceAdd, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte,
    hrlen, hrptr,
    show ¬ (1048576 > sta.mem.pages * 65536) from by rw [hpg_a]; omega,
    show ¬ (1048572 > sta.mem.pages * 65536) from by rw [hpg_a]; omega]
  apply wp_call_tw (func0_swap env sta ptr len i j [] hglob0 hi hj hptr
    (by rw [hpg_a]; exact hbound) (by rw [hpg_a]; exact hpages))
  rintro stb vsb ⟨rfl, hgb, hpb, hmb⟩
  wp_run
  rw [hgb, hga, List.getElem?_set_self hlen]
  rw [hma] at hmb
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [hmb]
    by_cases hij : i = j
    · subst hij; rw [Mem.read64_write64_same, frame_read64 _ _ _ _ hpiN]
    · rw [Mem.read64_write64_disjoint _ _ _ _ (elemAddr_disjoint ptr i j hwi hwj hij),
          Mem.read64_write64_same, frame_read64 _ _ _ _ hpjN]
  · rw [hmb, Mem.read64_write64_same, frame_read64 _ _ _ _ hpiN]
  · intro k hk hki hkj
    have hwk : ptr.toNat + 8 * k.toNat < 4294967296 := by
      have h : k.toNat < len.toNat := hk; omega
    have hpkN : 1048576 ≤ (elemAddr ptr k).toNat := by rw [elemAddr_toNat ptr k hwk]; omega
    rw [hmb,
        Mem.read64_write64_disjoint _ _ _ _ (elemAddr_disjoint ptr k j hwk hwj hkj),
        Mem.read64_write64_disjoint _ _ _ _ (elemAddr_disjoint ptr k i hwk hwi hki),
        Mem.read64_write64_disjoint _ _ _ _ (Or.inr (by rw [tn52]; omega)),
        frame_read64 _ _ _ _ hpkN]

/-! ## The registered spec -/

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

@[proves Project.SwapElements.Spec.SwapElementsSpec]
theorem swap_elements_correct : SwapElementsSpec := by
  intro env st ptr len i j hi hj hbound hptr hpages hsp
  exact func4_swap env st ptr len i j hi hj hptr hbound hpages hsp

end Project.SwapElements.Spec
