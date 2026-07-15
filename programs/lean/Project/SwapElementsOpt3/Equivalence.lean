import Project.SwapElements.Spec           -- opt-level 0 build + its `swap_elements_correct`
import Project.SwapElementsOpt3.Spec       -- opt-level 3 build + its `func0_swap`

/-!
# Equivalence of the two `swap_elements` builds (`opt-level = 0` vs `opt-level = 3`)

`swap_elements` and `swap_elements_opt3` are compiled from **byte-for-byte the
same Rust source** (`arr.swap(i, j)` on a `&mut [u64]`); only the optimisation
level differs.

* `mod0` (`opt-level = 0`) carves a 16-byte shadow-stack frame out of `global 0`,
  materialises the slice fat pointer through linear memory, forwards through a
  four-deep call chain, and exchanges the two elements via a **scratch slot** at
  `1048552`. `swap_elements` is exported at **func 4**.
* `mod3` (`opt-level = 3`) inlines everything into a single function: bounds
  checks, two `i64.load`s and two `i64.store`s through an `i64` local. It touches
  neither `global 0` nor any scratch memory. `swap_elements` is exported at
  **func 0**.

## Why the observation must include memory

`swap_elements` **returns nothing** and communicates only by mutating the
caller's array. Its `Store.host` is `Unit`. So the `Store.host` instance of
observational equivalence — `Wasm.ObservationallyEquiv`, the notion the
`num_integer` `gcd` pair uses — degenerates here to bare *co-termination*: it
says the two builds return `[]` together, and nothing whatsoever about the
array. It is true, and it is nearly vacuous.

The right observation is the one `CodeLib.Equivalence` was generalised for:
`ObservationallyEquivOn` at

    fun st => (st.host, st.mem.words64 ptr len.toNat)

— the host state together with **the caller's array, viewed as a `List UInt64`**.

Note this is deliberately weaker than "the final memories are equal", and it has
to be: the two builds' final memories are **not** the same function. `mod0`
additionally writes the exchanged value into the scratch slot at
`[1048552, 1048560)` — a write `mod3` never performs — so the memories agree
only away from that slot. Observing the array *region*, rather than all of
memory, is exactly what separates the caller-visible result from the scratch
traffic. That is the whole point, and it is why `Mem.words64` is the right
vocabulary.

## Preconditions

The two builds do **not** need the same hypotheses: `mod3` needs neither the
shadow-stack pin nor `1048576 ≤ ptr` (it has no scratch frame for the array to
alias). The equivalence is therefore stated under `mod0`'s — the stronger —
preconditions, which are exactly those of the merged `SwapElementsSpec`. On a
store violating them `mod0` can trap where `mod3` still succeeds, so they are
load-bearing, mirroring the `gcd` pair's use of a fixed initial store.
-/

namespace Project.SwapElementsOpt3.Equivalence

open Wasm

-- Both builds' specs define their own (definitionally equal) `elemAddr`; work
-- throughout in the opt0 spelling, so the two postconditions and the address
-- lemmas below all match syntactically.
open Project.SwapElements.Spec (elemAddr elemAddr_disjoint)

/-- The opt3 spec's `elemAddr` is the opt0 one; used to normalise that build's
postcondition into the shared spelling. -/
private theorem opt3_elemAddr_eq (ptr k : UInt32) :
    Project.SwapElementsOpt3.Spec.elemAddr ptr k = elemAddr ptr k := rfl

/-- The unoptimised (`opt-level = 0`) build: shadow-stack + scratch-slot version. -/
abbrev mod0 : Wasm.Module := Project.SwapElements.module

/-- The optimised (`opt-level = 3`) build: fully inlined, memory-scratch-free. -/
abbrev mod3 : Wasm.Module := Project.SwapElementsOpt3.module

/-- `swap_elements` is exported at func **4** in the `opt-level = 0` build. -/
abbrev entry0 : Nat := 4

/-- `swap_elements` is exported at func **0** in the `opt-level = 3` build. -/
abbrev entry3 : Nat := 0

/-- **The observation**: what a caller of `swap_elements` can see — the host
state, plus the array `[ptr, ptr + 8*len)` as a list of `u64`s. Scratch traffic
outside the array is deliberately not observed. -/
@[reducible] def arrayObs (ptr len : UInt32) (st : Store Unit) : Unit × List UInt64 :=
  (st.host, st.mem.words64 ptr len.toNat)

/-! ## From a per-element swap postcondition to the array view

Both builds' specs are stated per element (`read64 (elemAddr ptr k)`). This is
the shared bridge to the `Mem.words64` view, so each side reaches the *same*
observation and `of_common_outcome` applies. -/

/-- The per-element swap postcondition pins the array view: it is the initial
view with positions `i` and `j` exchanged. -/
private theorem words64_of_swap_post (m m' : Mem) (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (h_i : m'.read64 (elemAddr ptr i) = m.read64 (elemAddr ptr j))
    (h_j : m'.read64 (elemAddr ptr j) = m.read64 (elemAddr ptr i))
    (h_k : ∀ k : UInt32, k < len → k ≠ i → k ≠ j →
      m'.read64 (elemAddr ptr k) = m.read64 (elemAddr ptr k)) :
    m'.words64 ptr len.toNat =
      ((m.words64 ptr len.toNat).set i.toNat (m.read64 (elemAddr ptr j))).set j.toNat
        (m.read64 (elemAddr ptr i)) := by
  have hsize : (UInt32.size : Nat) = 4294967296 := rfl
  have hlen : len.toNat < UInt32.size := len.toNat_lt
  refine Mem.words64_swap (m := m) (m' := m') (base := ptr) (n := len.toNat)
    (i := i.toNat) (j := j.toNat) hi hj ?_ ?_ ?_ |>.trans ?_
  · simpa [elemAddr, UInt32.ofNat_toNat] using h_i
  · simpa [elemAddr, UInt32.ofNat_toNat] using h_j
  · intro k hk hki hkj
    have hkn : (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' (by omega)
    have hklt : (UInt32.ofNat k) < len := by show (UInt32.ofNat k).toNat < len.toNat; omega
    have hkine : (UInt32.ofNat k) ≠ i := by intro h; exact hki (by rw [← h, hkn])
    have hkjne : (UInt32.ofNat k) ≠ j := by intro h; exact hkj (by rw [← h, hkn])
    simpa [elemAddr] using h_k (UInt32.ofNat k) hklt hkine hkjne
  · simp [elemAddr, UInt32.ofNat_toNat]

/-! ## The equivalence -/

/-- **Program equivalence of the two `swap_elements` builds.**

For every in-bounds call, the two builds are `Wasm.ObservationallyEquivOn` at
the array observation: they agree on the returned values (`[]`), on the host
state, and on **the caller's array** — while the scratch slot `mod0` dirties,
and which `mod3` never touches, is left unobserved. -/
def SwapOptEquiv : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr len i j : UInt32),
    i < len → j < len →
    ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ ptr.toNat →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i32 1048576) →
    ObservationallyEquivOn env mod0 entry0 mod3 entry3 st
      [.i32 j, .i32 i, .i32 len, .i32 ptr] (arrayObs ptr len)

/-- The common outcome is the array with `i` and `j` exchanged. The opt0 side
reuses the merged `Project.SwapElements.Spec.swap_elements_correct`; the opt3
side uses `Project.SwapElementsOpt3.Spec.func0_swap`. Both are routed through
`words64_of_swap_post`, so they land on the *same* observation. -/
theorem swap_opt_equiv : SwapOptEquiv := by
  intro env st ptr len i j hi hj hbound hptr hpages hsp
  refine ObservationallyEquivOn.of_common_outcome
    (r := [])
    (o := ((), ((st.mem.words64 ptr len.toNat).set i.toNat
              (st.mem.read64 (elemAddr ptr j))).set j.toNat
              (st.mem.read64 (elemAddr ptr i)))) ?_ ?_
  · -- opt0: the merged total-correctness spec, per element.
    refine (Project.SwapElements.Spec.swap_elements_correct
      env st ptr len i j hi hj hbound hptr hpages hsp).mono ?_
    rintro st' vs ⟨rfl, h_i, h_j, h_k⟩
    exact ⟨rfl, Prod.ext rfl (words64_of_swap_post st.mem st'.mem ptr len i j hi hj h_i h_j h_k)⟩
  · -- opt3: the inlined build writes the two elements directly.
    refine (Project.SwapElementsOpt3.Spec.func0_swap
      env st ptr len i j hi hj hbound hpages).mono ?_
    rintro st' vs ⟨rfl, hmem⟩
    simp only [opt3_elemAddr_eq] at hmem
    have hli : i.toNat < len.toNat := hi
    have hlj : j.toNat < len.toNat := hj
    refine ⟨rfl, Prod.ext rfl (words64_of_swap_post st.mem st'.mem ptr len i j hi hj ?_ ?_ ?_)⟩
    · -- `i = j` is permitted: the two stores then coincide.
      by_cases hij : i = j
      · subst hij; rw [hmem, Mem.read64_write64_same]
      · rw [hmem,
            Mem.read64_write64_disjoint _ _ _ _
              (elemAddr_disjoint ptr i j (by omega) (by omega) hij),
            Mem.read64_write64_same]
    · rw [hmem, Mem.read64_write64_same]
    · intro k hk hki hkj
      have hlk : k.toNat < len.toNat := hk
      rw [hmem,
          Mem.read64_write64_disjoint _ _ _ _
            (elemAddr_disjoint ptr k j (by omega) (by omega) hkj),
          Mem.read64_write64_disjoint _ _ _ _
            (elemAddr_disjoint ptr k i (by omega) (by omega) hki)]

end Project.SwapElementsOpt3.Equivalence
