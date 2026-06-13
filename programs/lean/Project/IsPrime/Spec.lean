import Project.IsPrime.Program

/-!
# Specification for `is_prime`

The exported `check(n)` runs two trial-division primality tests on `n`
— a naive one (`d ∈ [2, n)`) and a faster one (`d ∈ [2, n / 2]`) —
and traps via `unreachable` iff they disagree. Proving the wasm export
terminates without trapping for every `n : UInt32` is therefore the
same as proving the two algorithms agree on every input.

At `opt-level=0` the live call graph is

```
func4 (exported `check` wrapper)
  └─ func3 (compare both algorithms, `unreachable` on disagreement)
       ├─ func2 (naive trial division over [2, n))
       └─ func1 (fast trial division over [2, n/2])
```

Every function carries the unoptimized shadow-stack discipline: the
prologue claims a 16-byte frame below `global 0` and spills values to
linear memory at fixed frame offsets (the loop counter lives at
`fp + 8`, the result flag byte at `fp + 7`, the argument spill at
`fp + 12`), and the epilogue restores `global 0`. With the canonical
instantiation (`global 0 = 1048576`, 17 pages of memory) the frames sit
at `1048560` (func4), `1048544` (func3) and `1048528` (func1/func2),
all comfortably in bounds.
-/

namespace Project.IsPrime.Spec

open Wasm

set_option maxRecDepth 1048576

/-- The exported `check` terminates without trapping (and returns no
values) on every `UInt32` input, when run from the module's canonical
instantiation.

The `initial = «module».initialStore` hypothesis is load-bearing: the
unoptimized body spills its locals to the shadow stack at
`global 0 − 16` and below, so under an adversarial store (e.g.
`mem.pages = 0`) the very first spill would trap. The canonical store
sets `global 0 = 1048576` with 17 pages (`17 · 65536 = 1114112`
bytes), so every frame access is in bounds.

Informal spec:
For any `n : UInt32`, the wasm export `check` terminates and leaves an
empty value stack. Termination-without-trapping is the whole content
of the spec — the body traps via `unreachable` iff the naive
(`d ∈ [2, n)`) and fast (`d ∈ [2, n / 2]`) trial-division loops
disagree on whether `n` is prime, so this property *is* the equivalence
claim between the two algorithms. -/
@[spec_of "rust-exported" "is_prime::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 4 initial [.i32 n]
      (fun _ rs => rs = [])

/-- `n` is prime in the `UInt32` sense iff `n ≥ 2` and no `d` in
`[2, n)` divides `n`. This is the predicate computed by the naive
loop in the wasm body. -/
def IsPrimeNat (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d, 2 ≤ d → d < n → n % d ≠ 0

/-- Key number-theoretic lemma: a divisor `d` strictly greater than
`n / 2` and strictly less than `n` cannot divide `n`. This is what
lets the fast loop stop at `n / 2` and still agree with the naive
loop, which scans all the way up to `n - 1`. -/
theorem not_dvd_of_gt_half {n d : Nat} (hlo : n / 2 < d) (hhi : d < n) :
    n % d ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  -- `n = d * k`. From `d < n` we get `k ≥ 2`, hence `2 * d ≤ n`, so `d ≤ n / 2`.
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk; omega
    · simp at hk; omega
    · omega
  have hle : 2 * d ≤ n := by
    calc 2 * d ≤ k * d := Nat.mul_le_mul_right _ hk2
    _ = n := by rw [hk]; ring
  omega

/-- Equivalence of the two trial-division ranges: scanning `[2, n)`
finds a divisor iff scanning `[2, n / 2]` does. Direct corollary of
[`not_dvd_of_gt_half`]; this is the algorithmic content of the
equivalence proof, independent of the wasm encoding. -/
theorem prime_iff_fast (n : Nat) (hn : 2 ≤ n) :
    IsPrimeNat n ↔ (∀ d, 2 ≤ d → d ≤ n / 2 → n % d ≠ 0) := by
  constructor
  · rintro ⟨_, hp⟩ d hd2 hdle
    exact hp d hd2 (by omega)
  · intro hfast
    refine ⟨hn, fun d hd2 hdn => ?_⟩
    by_cases hh : d ≤ n / 2
    · exact hfast d hd2 hh
    · exact not_dvd_of_gt_half (by omega) hdn

/-! ## UInt32 ↔ Nat bridges for the loop counters -/

/-- `n >>> 1` computes `n / 2` on the `Nat` view. -/
theorem toNat_shiftRight_one (n : UInt32) : (n >>> 1).toNat = n.toNat / 2 := by
  rw [UInt32.toNat_shiftRight]
  have hconst : (1 : UInt32).toNat = 1 := rfl
  rw [hconst]
  simp [Nat.shiftRight_eq_div_pow]

/-- A `UInt32` remainder is zero iff the corresponding `Nat` remainder is. -/
theorem rem_eq_zero_iff (a b : UInt32) : a % b = 0 ↔ a.toNat % b.toNat = 0 := by
  rw [← UInt32.toNat_mod]
  constructor
  · intro h; rw [h]; rfl
  · intro h; apply UInt32.toNat.inj; rw [h]; rfl

/-! ## Memory framing lemmas

The shadow-stack code spills the loop counter to `fp + 8` and the
result flag to `fp + 7`, and reads each back at the very address it
was last written. Only "read-after-same-address-write" facts (plus
page preservation) are needed; no disjointness reasoning is required
because every read in the live path is of the most recent write at
that address. -/

@[simp] private theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] private theorem write8_pages (m : Mem) (a : UInt32) (v : UInt8) :
    (m.write8 a v).pages = m.pages := rfl

/-- A 32-bit read sees the value of a same-address 32-bit write. -/
@[simp] private theorem read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.read32, Mem.write32]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1, e2, e3, e21, e31, e32, if_true, if_false]
  bv_decide

/-- A byte read sees the value of a same-address byte write. -/
@[simp] private theorem read8_write8_same (m : Mem) (a : UInt32) (v : UInt8) :
    (m.write8 a v).read8 a = v := by
  simp [Mem.read8, Mem.write8]

/-! ## Per-function correctness

The two trial-division functions both compute the primality indicator of
`n`; `func1` via the fast `[2, n/2]` range, `func2` via the naive `[2, n)`
range. We prove both produce `primeI n`, so the comparison in `func3`
never observes a difference (and never traps).

Both functions write linear memory (their shadow-stack frame at
`[1048528, 1048544)`), so no store-polymorphic `FuncSpec` exists for
them; the lemmas are `TerminatesWith`s at a parametric store
constrained to 17 pages and `global 0 = 1048544` (the value `func3`'s
prologue installs), discharged at the call sites via `wp_call_at`. -/

open scoped Classical in
/-- The primality indicator: `1` when `n` is prime, `0` otherwise. -/
noncomputable def primeI (n : UInt32) : UInt32 :=
  if IsPrimeNat n.toNat then 1 else 0

open scoped Classical in
/-- `func2` (naive `[2, n)` loop) returns the primality indicator of `n`.
Runs in a 16-byte shadow-stack frame at `1048528`; the loop counter `d`
lives in memory at `1048536 = fp + 8`, the result flag byte at
`1048535 = fp + 7`. The store's pages and `global 0` are restored on
exit. -/
theorem func2_at (env : HostEnv Unit) (st0 : Store Unit) (n : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048544, .i32 1049601, .i32 1049616]) :
    TerminatesWith env «module» 2 st0 [.i32 n]
      (fun st' vs => vs = [.i32 (primeI n)] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048544, .i32 1049601, .i32 1049616]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32], [.i32, .i32, .i32], func2, [.i32]⟩) rfl
  unfold func2
  wp_run
  simp only [hgl, hpg]
  -- Prologue done: frame at 1048528, `n` spilled to 1048540.
  simp
  apply wp_block_cons   -- A: everything up to the epilogue
  apply wp_block_cons   -- B: the `n < 2` early exit
  apply wp_block_cons   -- C: guard
  wp_run
  by_cases hn2 : n < 2
  · -- `n < 2`: flag := 0, exit; `n` is not prime.
    have hlt : n.toNat < 2 := by
      have := UInt32.lt_iff_toNat_lt.mp hn2
      simpa using this
    have hnp : ¬ IsPrimeNat n.toNat := by rintro ⟨h2, _⟩; omega
    simp [hn2, hpg, primeI, hnp]
  · -- `n ≥ 2`: seed the counter with 2 and run the loop.
    have hn2' : 2 ≤ n.toNat := by
      rcases Nat.lt_or_ge n.toNat 2 with h | h
      · exact absurd (UInt32.lt_iff_toNat_lt.mpr (by simpa using h)) hn2
      · exact h
    simp [hn2, hpg]
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048528, .i32 1049601, .i32 1049616] ∧
        ∃ (l2 l3 : Value) (d : UInt32),
          s' = { params := [.i32 n], locals := [.i32 1048528, l2, l3],
                 values := [] } ∧
          st'.mem.read32 1048536 = d ∧
          2 ≤ d.toNat ∧ d.toNat ≤ n.toNat ∧
          (∀ e, 2 ≤ e → e < d.toNat → n.toNat % e ≠ 0))
      (μ := fun st' _ => n.toNat + 1 - (st'.mem.read32 1048536).toNat)
    · -- invariant on entry (`d = 2`)
      refine ⟨by simp [hpg], by simp, .i32 0, .i32 0, 2, rfl, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hn2'
      · intro e he he2
        have : (2 : UInt32).toNat = 2 := rfl
        omega
    · -- one iteration preserves the invariant / establishes the post
      rintro st' s' ⟨hpg', hgl', l2, l3, d, rfl, hd, hd2, hdn, hdiv⟩
      have hdne0 : ¬ d = 0 := by
        intro h; subst h; simp at hd2
      apply wp_block_cons   -- D: the `d < n` loop-exit test
      wp_run
      simp [hd, hpg']
      by_cases hlt : d < n
      · -- `d < n`: check divisibility of `n` by `d`.
        simp [hlt]
        apply wp_block_cons   -- E: increment-or-exit
        apply wp_block_cons   -- F: panic guard
        apply wp_block_cons   -- G: the actual tests
        wp_run
        simp [hdne0, hpg']
        by_cases hrem : n % d = 0
        · -- divisor found: composite, flag := 0, result 0
          have hdlt : d.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hlt
          have hremn : n.toNat % d.toNat = 0 := (rem_eq_zero_iff n d).mp hrem
          have hnp : ¬ IsPrimeNat n.toNat := by
            rintro ⟨_, hP⟩
            exact hP d.toNat (by omega) (by omega) hremn
          simp [hrem, hgl', primeI, hnp]
        · -- no divisor: increment `d` and continue
          have hdlt : d.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hlt
          have hremn : n.toNat % d.toNat ≠ 0 :=
            fun h => hrem ((rem_eq_zero_iff n d).mpr h)
          simp [hrem, hd]
          have hmod : (1 + d.toNat) % 4294967296 = d.toNat + 1 := by
            have := n.toNat_lt
            omega
          rw [hmod]
          refine ⟨⟨hgl', by omega, by omega, ?_⟩, by omega⟩
          intro e he he2
          rcases Nat.lt_or_ge e d.toNat with h | h
          · exact hdiv e he h
          · have : e = d.toNat := by omega
            subst this; exact hremn
      · -- `d ≥ n`: every divisor in `[2, n)` checked → prime, flag := 1
        have hnd : n.toNat ≤ d.toNat := by
          rcases Nat.lt_or_ge d.toNat n.toNat with h | h
          · exact absurd (UInt32.lt_iff_toNat_lt.mpr h) hlt
          · exact h
        have hP : IsPrimeNat n.toNat :=
          ⟨hn2', fun e he2 hen => hdiv e he2 (by omega)⟩
        simp [hlt, hgl', primeI, hP]

open scoped Classical in
/-- `func1` (fast `[2, n/2]` loop) returns the primality indicator of `n`.
Same frame discipline as [`func2_at`]: counter at `1048536`, flag at
`1048535`, pages and `global 0` restored on exit. -/
theorem func1_at (env : HostEnv Unit) (st0 : Store Unit) (n : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048544, .i32 1049601, .i32 1049616]) :
    TerminatesWith env «module» 1 st0 [.i32 n]
      (fun st' vs => vs = [.i32 (primeI n)] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048544, .i32 1049601, .i32 1049616]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32], [.i32, .i32, .i32], func1, [.i32]⟩) rfl
  unfold func1
  wp_run
  simp only [hgl, hpg]
  simp
  apply wp_block_cons   -- A
  apply wp_block_cons   -- B
  apply wp_block_cons   -- C
  wp_run
  by_cases hn2 : n < 2
  · have hlt : n.toNat < 2 := by
      have := UInt32.lt_iff_toNat_lt.mp hn2
      simpa using this
    have hnp : ¬ IsPrimeNat n.toNat := by rintro ⟨h2, _⟩; omega
    simp [hn2, hpg, primeI, hnp]
  · have hn2' : 2 ≤ n.toNat := by
      rcases Nat.lt_or_ge n.toNat 2 with h | h
      · exact absurd (UInt32.lt_iff_toNat_lt.mpr (by simpa using h)) hn2
      · exact h
    have hhalf : (n >>> 1).toNat = n.toNat / 2 := toNat_shiftRight_one n
    simp [hn2, hpg]
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048528, .i32 1049601, .i32 1049616] ∧
        ∃ (l2 l3 : Value) (d : UInt32),
          s' = { params := [.i32 n], locals := [.i32 1048528, l2, l3],
                 values := [] } ∧
          st'.mem.read32 1048536 = d ∧
          2 ≤ d.toNat ∧ d.toNat ≤ n.toNat / 2 + 1 ∧
          (∀ e, 2 ≤ e → e < d.toNat → n.toNat % e ≠ 0))
      (μ := fun st' _ => n.toNat / 2 + 2 - (st'.mem.read32 1048536).toNat)
    · -- invariant on entry (`d = 2`)
      refine ⟨by simp [hpg], by simp, .i32 0, .i32 0, 2, rfl, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · have : (2 : UInt32).toNat = 2 := rfl
        omega
      · intro e he he2
        have : (2 : UInt32).toNat = 2 := rfl
        omega
    · rintro st' s' ⟨hpg', hgl', l2, l3, d, rfl, hd, hd2, hdn, hdiv⟩
      have hdne0 : ¬ d = 0 := by
        intro h; subst h; simp at hd2
      apply wp_block_cons   -- D: the `d ≤ n/2` loop-exit test
      wp_run
      simp [hd, hpg']
      by_cases hle : d ≤ n >>> 1
      · -- `d ≤ n/2`: check divisibility of `n` by `d`.
        have hdhalf : d.toNat ≤ n.toNat / 2 := by
          have := UInt32.le_iff_toNat_le.mp hle
          rw [hhalf] at this
          exact this
        simp [hle]
        apply wp_block_cons   -- E
        apply wp_block_cons   -- F
        apply wp_block_cons   -- G
        wp_run
        simp [hdne0, hpg']
        by_cases hrem : n % d = 0
        · -- divisor found: composite
          have hremn : n.toNat % d.toNat = 0 := (rem_eq_zero_iff n d).mp hrem
          have hnp : ¬ IsPrimeNat n.toNat := by
            rintro ⟨_, hP⟩
            exact hP d.toNat (by omega) (by omega) hremn
          simp [hrem, hgl', primeI, hnp]
        · -- no divisor: increment and continue
          have hremn : n.toNat % d.toNat ≠ 0 :=
            fun h => hrem ((rem_eq_zero_iff n d).mpr h)
          simp [hrem, hd]
          have hmod : (1 + d.toNat) % 4294967296 = d.toNat + 1 := by
            have := n.toNat_lt
            omega
          rw [hmod]
          refine ⟨⟨hgl', by omega, by omega, ?_⟩, by omega⟩
          intro e he he2
          rcases Nat.lt_or_ge e d.toNat with h | h
          · exact hdiv e he h
          · have : e = d.toNat := by omega
            subst this; exact hremn
      · -- `d > n/2`: every divisor in `[2, n/2]` checked → prime
        have hgt : n.toNat / 2 < d.toNat := by
          rcases Nat.lt_or_ge (n.toNat / 2) d.toNat with h | h
          · exact h
          · exact absurd (UInt32.le_iff_toNat_le.mpr (by rw [hhalf]; exact h)) hle
        have hP : IsPrimeNat n.toNat := by
          rw [prime_iff_fast n.toNat hn2']
          intro k hk2 hkhalf
          exact hdiv k hk2 (by omega)
        simp [hle, hgl', primeI, hP]

open scoped Classical in
/-- `func3` runs both tests, compares them, and (because they agree)
never trips the `unreachable`; it returns with an empty value stack,
its 16-byte frame at `1048544` released and `global 0` restored. -/
theorem func3_at (env : HostEnv Unit) (st0 : Store Unit) (n : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048560, .i32 1049601, .i32 1049616]) :
    TerminatesWith env «module» 3 st0 [.i32 n]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048560, .i32 1049601, .i32 1049616]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32], [.i32, .i32, .i32], func3, []⟩) rfl
  unfold func3
  wp_run
  simp only [hgl, hpg]
  simp
  -- `.call 2` (naive) at the post-prologue store
  refine wp_call_at
    (Post := fun st' vs => vs = [.i32 (primeI n)] ∧ st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048544, .i32 1049601, .i32 1049616])
    (func2_at env _ n (by simp [hpg]) (by simp)) ?_
  rintro st2 vs2 ⟨rfl, hpg2, hgl2⟩
  wp_run
  -- `.call 1` (fast) at the store func2 left behind
  refine wp_call_at
    (Post := fun st' vs => vs = [.i32 (primeI n)] ∧ st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048544, .i32 1049601, .i32 1049616])
    (func1_at env _ n hpg2 hgl2) ?_
  rintro st1 vs1 ⟨rfl, hpg1, hgl1⟩
  wp_run
  apply wp_block_cons
  wp_run
  -- both results are `primeI n`, so `ne` yields 0 and the `br_if`
  -- guarding the `unreachable` is never taken
  simp [hgl1, hpg1]

@[proves Project.IsPrime.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro env initial n hinit
  subst hinit
  have hpg : («module».initialStore : Store Unit).mem.pages = 17 := by rfl
  have hgl : («module».initialStore : Store Unit).globals.globals
      = [.i32 1048576, .i32 1049601, .i32 1049616] := by rfl
  -- `func4` is the exported `check` wrapper: spill `n`, forward to `func3`.
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32], func4, []⟩) rfl
  unfold func4
  wp_run
  simp only [hgl, hpg]
  simp
  refine wp_call_at
    (Post := fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048560, .i32 1049601, .i32 1049616])
    (func3_at env _ n (by simp [hpg]) (by simp)) ?_
  rintro st' vs ⟨rfl, hpg', hgl'⟩
  wp_run
  simp [hgl']

end Project.IsPrime.Spec
