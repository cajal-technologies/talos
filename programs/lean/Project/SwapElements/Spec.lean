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

set_option maxRecDepth 1048576
-- The straight-line `simp only [wp_simp, …]` calls reuse one shared lemma set
-- across functions; not every lemma fires in every call.
set_option linter.unusedSimpArgs false

/-- Byte address of the `k`-th `u64` element of an array based at `ptr`. -/
@[reducible] def elemAddr (ptr k : UInt32) : UInt32 := ptr + 8 * k

/-- The post-state of swapping the 8-byte words at `a` and `b`: `a` and `b` hold
each other's old values, every slot at/above `g0` disjoint from both is
unchanged, and globals are preserved. Shared by `func2`/`func1`/`func0` so their
specs don't restate it. -/
def SwappedAbove (st st' : Store Unit) (g0 a b : UInt32) : Prop :=
  st'.mem.read64 a = st.mem.read64 b
  ∧ st'.mem.read64 b = st.mem.read64 a
  ∧ (∀ k : UInt32, g0.toNat ≤ k.toNat →
      (k.toNat + 8 ≤ a.toNat ∨ a.toNat + 8 ≤ k.toNat) →
      (k.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ k.toNat) →
      st'.mem.read64 k = st.mem.read64 k)
  ∧ st'.globals = st.globals

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
    -- indices in bounds and distinct (`arr.swap i i` is a no-op handled elsewhere)
    i < len → j < len → i ≠ j →
    -- the array is addressable; `pages ≤ 65536` is the wasm32 4 GiB limit, which
    -- (with the addressability bound) rules out UInt32 wraparound of `ptr + 8*k`
    ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    -- the array does not collide with the callee's shadow-stack scratch frame
    1048576 ≤ ptr.toNat →
    -- global 0 is the shadow-stack pointer, at its initial value
    st.globals.globals[0]? = some (.i32 1048576) →
    TerminatesWith env «module» 4 st
      [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = []
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ k : UInt32, k < len → k ≠ i → k ≠ j →
            st'.mem.read64 (elemAddr ptr k) = st.mem.read64 (elemAddr ptr k))

/-! ## Bottom-up proof of `swap_elements`, reusing the `RustStd/Mem.lean` trunk

The export `func4` calls `func3` (spill the slice to its frame) then `func0`
(→ `func1` → `func2`). Under the in-bounds preconditions the `call 56` panic
paths in `func1` are dead. Each function gets a `TerminatesWith` lemma; the
call sites are crossed with `wp_call_tw`, and the memory reasoning is entirely
`Mem.read64_write64_same` / `Mem.read64_write64_disjoint`. -/

/-- `func2` — the swap primitive. Params `(addr_i, addr_j)`; scratches a `u64`
at `global0 - 8`. Swaps the two 8-byte words at `ai`, `aj`. -/
theorem func2_swaps (env : HostEnv Unit) (st : Store Unit) (ai aj g0 : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hiB  : ai.toNat + 8 ≤ st.mem.pages * 65536)
    (hjB  : aj.toNat + 8 ≤ st.mem.pages * 65536)
    (hij  : ai.toNat + 8 ≤ aj.toNat ∨ aj.toNat + 8 ≤ ai.toNat)
    (hia  : g0.toNat ≤ ai.toNat)
    (hja  : g0.toNat ≤ aj.toNat) :
    TerminatesWith env «module» 2 st [.i32 aj, .i32 ai]
      (fun st' rs => rs = [] ∧ SwappedAbove st st' g0 ai aj) := by
  refine TerminatesWith.of_returns_wp (f := func2Def) (rs := []) rfl rfl ?_ rfl
  simp only [func2Def]
  unfold func2 Returns
  have hle16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr (by simpa using hg16)
  have hle8  : (8 : UInt32) ≤ g0 :=
    UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : 8 ≤ g0.toNat))
  have hsub16 : (g0 - 16).toNat = g0.toNat - 16 := UInt32.toNat_sub_of_le g0 16 hle16
  have hsub8  : (g0 - 8).toNat = g0.toNat - 8 := UInt32.toNat_sub_of_le g0 8 hle8
  have etemp : (g0 - 16) + 8 = g0 - 8 := by bv_decide
  have htemp : ((g0 - 16) + 8).toNat = g0.toNat - 8 := by rw [etemp, hsub8]
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have hnt_ai : ¬ (ai.toNat + 8 > st.mem.pages * 65536) := by omega
  have hnt_aj : ¬ (aj.toNat + 8 > st.mem.pages * 65536) := by omega
  have hnt_temp : ¬ ((g0 - 16).toNat + 8 + 8 > st.mem.pages * 65536) := by rw [hsub16]; omega
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, hg, h0, h8, hnt_ai, hnt_aj, hnt_temp, Mem.write64_pages]
  -- `m3` is the three nested writes; each obligation folds through the trunk.
  refine ⟨_, rfl, ?_, ?_, ?_, rfl⟩
  · simp only [UInt32.add_zero]
    rw [Mem.read64_write64_disjoint _ ai aj _ hij, Mem.read64_write64_same,
        Mem.read64_write64_disjoint _ aj (g0 - 16 + 8) _ (Or.inr (by rw [htemp]; omega))]
  · simp only [UInt32.add_zero]
    rw [Mem.read64_write64_same,
        Mem.read64_write64_disjoint _ (g0 - 16 + 8) ai _ (Or.inl (by rw [htemp]; omega)),
        Mem.read64_write64_same]
  · simp only [UInt32.add_zero]
    intro k hk hka hkb
    rw [Mem.read64_write64_disjoint _ k aj _ hkb, Mem.read64_write64_disjoint _ k ai _ hka,
        Mem.read64_write64_disjoint _ k (g0 - 16 + 8) _ (Or.inr (by rw [htemp]; omega))]

/-- `func3` — spill a `(ptr, len)` fat pointer to the frame: `store32` at
`dest` and `dest + 4`. Straight-line, like `func2`. -/
theorem func3_spills (env : HostEnv Unit) (st : Store Unit) (dest ptr len ploc : UInt32)
    (hdw : (dest + 4).toNat = dest.toNat + 4)
    (hb  : dest.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 3 st [.i32 ploc, .i32 len, .i32 ptr, .i32 dest]
      (fun st' rs => rs = []
        ∧ st'.mem.read32 dest = ptr
        ∧ st'.mem.read32 (dest + 4) = len
        ∧ st'.mem.pages = st.mem.pages
        ∧ st'.globals = st.globals
        ∧ ∀ k : UInt32, k.toNat + 8 ≤ dest.toNat ∨ dest.toNat + 8 ≤ k.toNat →
            st'.mem.read64 k = st.mem.read64 k) := by
  refine TerminatesWith.of_returns_wp (f := func3Def) (rs := []) rfl rfl ?_ rfl
  simp only [func3Def]
  unfold func3 Returns
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h4 : (4 : UInt32).toNat = 4 := rfl
  have hnt0 : ¬ (dest.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
  have hnt4 : ¬ (dest.toNat + 4 + 4 > st.mem.pages * 65536) := by omega
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, h0, h4, hnt0, hnt4, Mem.write32_pages]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [UInt32.add_zero]; exact Mem.read32_write32_same _ _ _
  · simp only [UInt32.add_zero]
    rw [Mem.read32_write32_disjoint _ (dest + 4) dest _ (Or.inr (by omega))]
    exact Mem.read32_write32_same _ _ _
  · rfl
  · rfl
  · intro k hk
    simp only [UInt32.add_zero]
    rw [Mem.read64_write32_disjoint _ k dest _ (by omega),
        Mem.read64_write32_disjoint _ k (dest + 4) _ (by omega)]

/-- `func1` — bounds-check `i, j < len`, compute the element addresses
`ptr + 8*i`, `ptr + 8*j`, and `call func2`. Under `i < len ∧ j < len` the two
`call 56` panic paths are dead. -/
theorem func1_swaps (env : HostEnv Unit) (st : Store Unit) (ptr len i j ploc g0 : UInt32)
    (hi : i < len) (hj : j < len)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hiB  : (elemAddr ptr i).toNat + 8 ≤ st.mem.pages * 65536)
    (hjB  : (elemAddr ptr j).toNat + 8 ≤ st.mem.pages * 65536)
    (hij  : (elemAddr ptr i).toNat + 8 ≤ (elemAddr ptr j).toNat
            ∨ (elemAddr ptr j).toNat + 8 ≤ (elemAddr ptr i).toNat)
    (hia  : g0.toNat ≤ (elemAddr ptr i).toNat)
    (hja  : g0.toNat ≤ (elemAddr ptr j).toNat) :
    TerminatesWith env «module» 1 st [.i32 ploc, .i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs => rs = [] ∧ SwappedAbove st st' g0 (elemAddr ptr i) (elemAddr ptr j)) := by
  refine TerminatesWith.of_returns_wp (f := func1Def) (rs := []) rfl rfl ?_ rfl
  simp only [func1Def]
  unfold func1 Returns
  have hand : (1 : UInt32) &&& 1 = 1 := by decide
  have hne10 : (1 : UInt32) ≠ 0 := by decide
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, hi, hj, hand, hne10]
  -- The swap branch: stack is `[ptr + 8*j, ptr + 8*i]`; `i <<< 3 = 8*i`.
  have hai : i <<< (3 % 32) + ptr = elemAddr ptr i := by simp only [elemAddr]; bv_decide
  have haj : j <<< (3 % 32) + ptr = elemAddr ptr j := by simp only [elemAddr]; bv_decide
  simp only [hai, haj, List.drop_nil]
  apply wp_call_tw
    (func2_swaps env st (elemAddr ptr i) (elemAddr ptr j) g0 hg hg16 hgB hiB hjB hij hia hja)
  rintro st' vs ⟨rfl, h1, h2, h3, hgl⟩
  simp only [wp_simp]
  exact ⟨st', rfl, h1, h2, h3, hgl⟩

/-- `func0` — the thin wrapper that forwards `(ptr, len, i, j)` to `func1`. -/
theorem func0_swaps (env : HostEnv Unit) (st : Store Unit) (ptr len i j g0 : UInt32)
    (hi : i < len) (hj : j < len)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hiB  : (elemAddr ptr i).toNat + 8 ≤ st.mem.pages * 65536)
    (hjB  : (elemAddr ptr j).toNat + 8 ≤ st.mem.pages * 65536)
    (hij  : (elemAddr ptr i).toNat + 8 ≤ (elemAddr ptr j).toNat
            ∨ (elemAddr ptr j).toNat + 8 ≤ (elemAddr ptr i).toNat)
    (hia  : g0.toNat ≤ (elemAddr ptr i).toNat)
    (hja  : g0.toNat ≤ (elemAddr ptr j).toNat) :
    TerminatesWith env «module» 0 st [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs => rs = [] ∧ SwappedAbove st st' g0 (elemAddr ptr i) (elemAddr ptr j)) := by
  refine TerminatesWith.of_returns_wp (f := func0Def) (rs := []) rfl rfl ?_ rfl
  simp only [func0Def]
  unfold func0 Returns
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, List.drop_nil]
  apply wp_call_tw
    (func1_swaps env st ptr len i j 1048604 g0 hi hj hg hg16 hgB hiB hjB hij hia hja)
  rintro st' vs ⟨rfl, h1, h2, h3, hgl⟩
  simp only [wp_simp]
  exact ⟨st', rfl, h1, h2, h3, hgl⟩

/-- Under the addressability bound and the wasm32 page limit, the `k`-th element
address does not wrap: `(ptr + 8*k).toNat = ptr.toNat + 8 * k.toNat`. -/
theorem elemAddr_toNat (ptr k len : UInt32) (pages : Nat)
    (hk : k.toNat < len.toNat)
    (haddr : ptr.toNat + 8 * len.toNat ≤ pages * 65536)
    (hpg : pages ≤ 65536) :
    (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat := by
  simp only [elemAddr]
  have hlt : ptr.toNat + 8 * k.toNat < 4294967296 := by omega
  simp only [UInt32.toNat_add, UInt32.toNat_mul, show (8 : UInt32).toNat = 8 from rfl]
  omega

/-- **`swap_elements` is correct.** The exported `func4` sets up its frame,
spills the slice (`func3`), calls the swap (`func0 → func1 → func2`), and
restores the frame — swapping the two `u64` elements and leaving the rest of the
array untouched. Composed from the per-function lemmas above; all memory
reasoning goes through the `RustStd/Mem.lean` trunk. -/
@[proves Project.SwapElements.Spec.SwapElementsSpec]
theorem swap_elements_correct : SwapElementsSpec := by
  intro env st ptr len i j hi hj hne haddr hpg hptr hsp
  refine TerminatesWith.of_returns_wp (f := func4Def) (rs := []) rfl rfl ?_ rfl
  simp only [func4Def]
  unfold func4 Returns
  have hsub : (1048576 : UInt32) - 16 = 1048560 := by decide
  have hadd8 : (8 : UInt32) + 1048560 = 1048568 := by decide
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, hsp, hsub, hadd8]
  -- cross `call 3` (spill) with `func3_spills`
  refine wp_call_tw (func3_spills env _ 1048568 ptr len 1048652 ?_ ?_) ?_
  · decide
  · show (1048568 : UInt32).toNat + 8 ≤ st.mem.pages * 65536
    rw [show (1048568 : UInt32).toNat = 1048568 from by decide]; omega
  rintro st_b vs_b ⟨rfl, hr8, hr12, hpb, hgb, hfb⟩
  have hpb' : st_b.mem.pages = st.mem.pages := hpb
  have h12t : (12 : UInt32).toNat = 12 := rfl
  have h8t : (8 : UInt32).toNat = 8 := rfl
  have h60 : (1048560 : UInt32).toNat = 1048560 := by decide
  have hLa : (1048560 + 12 : UInt32) = 1048572 := by decide
  have hLb : (1048560 + 8 : UInt32) = 1048568 := by decide
  have hr12c : st_b.mem.read32 1048572 = len := by
    rw [show (1048572 : UInt32) = 1048568 + 4 from by decide]; exact hr12
  have hntLa : ¬ ((1048560 : UInt32).toNat + 12 + 4 > st_b.mem.pages * 65536) := by
    rw [hpb', h60]; omega
  have hntLb : ¬ ((1048560 : UInt32).toNat + 8 + 4 > st_b.mem.pages * 65536) := by
    rw [hpb', h60]; omega
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, h12t, h8t, hLa, hLb, hr8, hr12c, hntLa, hntLb]
  -- element-address expansions and index facts
  have ei : (elemAddr ptr i).toNat = ptr.toNat + 8 * i.toNat :=
    elemAddr_toNat ptr i len st.mem.pages (UInt32.lt_iff_toNat_lt.mp hi) haddr hpg
  have ej : (elemAddr ptr j).toNat = ptr.toNat + 8 * j.toNat :=
    elemAddr_toNat ptr j len st.mem.pages (UInt32.lt_iff_toNat_lt.mp hj) haddr hpg
  have hi' : i.toNat < len.toNat := UInt32.lt_iff_toNat_lt.mp hi
  have hj' : j.toNat < len.toNat := UInt32.lt_iff_toNat_lt.mp hj
  have hijn : i.toNat ≠ j.toNat := fun h => hne (UInt32.toNat.inj h)
  have hg' : st_b.globals.globals[0]? = some (.i32 1048560) := by
    obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hsp
    rw [hgb]; simp only [List.getElem?_set_self hlen]
  -- cross `call 0` (the swap) with `func0_swaps`
  refine wp_call_tw
    (func0_swaps env st_b ptr len i j 1048560 hi hj hg'
      (by rw [h60]; omega) (by rw [h60, hpb']; omega) (by rw [hpb', ei]; omega)
      (by rw [hpb', ej]; omega) (by rw [ei, ej]; omega) (by rw [ei, h60]; omega)
      (by rw [ej, h60]; omega)) ?_
  rintro st_c vs_c ⟨rfl, hc1, hc2, hc3, hc4⟩
  -- epilogue: restore global 0, return; memory is final. Thread `func0`'s result
  -- back through `func3`'s array frame (`hfb`) to the original `st.mem`.
  have hadd16 : (1048560 + 16 : UInt32) = 1048576 := by decide
  have h68 : (1048568 : UInt32).toNat = 1048568 := by decide
  have hgc : st_c.globals.globals[0]? = some (.i32 1048560) := by rw [hc4]; exact hg'
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, reduceIte, hadd16, hgc]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [hc1, hfb (elemAddr ptr j) (Or.inr (by rw [h68, ej]; omega))]
  · rw [hc2, hfb (elemAddr ptr i) (Or.inr (by rw [h68, ei]; omega))]
  · intro k hk hki hkj
    have ek : (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat :=
      elemAddr_toNat ptr k len st.mem.pages (UInt32.lt_iff_toNat_lt.mp hk) haddr hpg
    have hk' : k.toNat < len.toNat := UInt32.lt_iff_toNat_lt.mp hk
    have hkin : k.toNat ≠ i.toNat := fun h => hki (UInt32.toNat.inj h)
    have hkjn : k.toNat ≠ j.toNat := fun h => hkj (UInt32.toNat.inj h)
    rw [hc3 (elemAddr ptr k) (by rw [h60, ek]; omega) (by rw [ek, ei]; omega)
          (by rw [ek, ej]; omega),
        hfb (elemAddr ptr k) (Or.inr (by rw [h68, ek]; omega))]

end Project.SwapElements.Spec
