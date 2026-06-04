import Project.IsPrime.Program

/-!
# Specification for `is_prime`

The exported `check(n)` runs two trial-division primality tests on `n`
— a naive one (`d ∈ [2, n)`) and a faster one (`d ∈ [2, n / 2]`) —
and traps via `unreachable` iff they disagree. Proving the wasm export
terminates without trapping for every `n : UInt32` is therefore the
same as proving the two algorithms agree on every input.
-/

namespace Project.IsPrime.Spec

open Wasm

/-- The exported `check` terminates without trapping (and returns no
values) on every `UInt32` input.

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
    TerminatesWith env «module» 3 initial [.i32 n]
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

/-- `d - 1` is encoded in the wasm as `d + 0xFFFFFFFF`. For `d ≥ 1` this is
the genuine predecessor. -/
theorem toNat_add_neg_one {d : UInt32} (hd : 1 ≤ d.toNat) :
    (d + 4294967295).toNat = d.toNat - 1 := by
  rw [UInt32.toNat_add]
  have hconst : (4294967295 : UInt32).toNat = 4294967295 := rfl
  have hlt := d.toNat_lt
  rw [hconst]; omega

/-- `d + 1` does not overflow as long as `d.toNat + 1 < 2 ^ 32`. -/
theorem toNat_add_one {d : UInt32} (hd : d.toNat + 1 < 2 ^ 32) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt32.toNat_add]
  have hconst : (1 : UInt32).toNat = 1 := rfl
  rw [hconst]; omega

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

/-! ## Per-function correctness

The two trial-division functions both compute the primality indicator of
`n`; `func0` via the fast `[2, n/2]` range, `func1` via the naive `[2, n)`
range. We prove both produce `primeI n`, so the comparison in `func2`
never observes a difference (and never traps). -/

open scoped Classical in
/-- The primality indicator: `1` when `n` is prime, `0` otherwise. -/
noncomputable def primeI (n : UInt32) : UInt32 :=
  if IsPrimeNat n.toNat then 1 else 0

open scoped Classical in
/-- `func1` (naive `[2, n)` loop) returns the primality indicator of `n`.
A `tail` of caller values below the argument is framed through unchanged. -/
theorem func1_spec (env : HostEnv Unit) (n : UInt32) (tail : List Value) :
    FuncSpec env «module» 1 (· = .i32 n :: tail)
      (fun _ vs => vs = .i32 (primeI n) :: tail) := by
  apply FuncSpec.of_wp_body (f := ⟨[.i32], [.i32, .i32, .i32], func1, [.i32]⟩) rfl
  rintro args rfl initial
  unfold func1
  apply wp_block_cons
  wp_run
  by_cases hn2 : 2 ≤ n
  · -- `n ≥ 2`: enter the main block.
    simp [hn2]
    apply wp_block_cons   -- outer block B
    apply wp_block_cons   -- inner block C (the `n == 2` early-prime test)
    wp_run
    simp
    by_cases hn3 : n = 2
    · -- `n = 2`: prime, the `br 1` exit carries `1`.
      subst hn3
      have hp : IsPrimeNat 2 := ⟨le_refl _, fun d hd hd2 => by omega⟩
      simp [primeI, hp]
    · -- `n ≥ 3`: run the naive trial-division loop over `[2, n)`.
      simp [hn3]
      have hn2' : 2 ≤ n.toNat := by
        have := UInt32.le_iff_toNat_le.mp hn2; simpa using this
      have hne : n.toNat ≠ 2 := by
        intro h; exact hn3 (UInt32.toNat.inj (by rw [h]; rfl))
      have hn3' : 3 ≤ n.toNat := by omega
      apply wp_loop_cons
        (Inv := fun _ s' => ∃ (a c : Value) (d : UInt32),
          s' = { params := [.i32 n], locals := [a, .i32 d, c], values := [] } ∧
            3 ≤ d.toNat ∧ d.toNat ≤ n.toNat ∧
            (∀ e, 2 ≤ e → e ≤ d.toNat - 2 → n.toNat % e ≠ 0))
        (μ := fun _ s' => match s'.locals with
          | [_, .i32 d, _] => n.toNat - d.toNat
          | _ => 0)
      · -- invariant holds on entry (`d = 3`)
        refine ⟨.i32 0, .i32 0, 3, rfl, le_refl _, hn3', fun e he he2 => ?_⟩
        have h3 : (3 : UInt32).toNat = 3 := rfl
        omega
      · -- one iteration preserves the invariant / establishes the post
        rintro st' s' ⟨a, c, d, rfl, hd3, hdn, hdiv⟩
        -- `4294967295 + d` is `d - 1` (no underflow since `d ≥ 3`)
        have hd1 : (4294967295 + d).toNat = d.toNat - 1 := by
          rw [UInt32.toNat_add]
          have hc : (4294967295 : UInt32).toNat = 4294967295 := rfl
          have hlt := d.toNat_lt
          rw [hc]; omega
        have hne0 : ¬ (4294967295 + d = 0) := by
          intro h
          have hz : (4294967295 + d).toNat = 0 := by rw [h]; rfl
          rw [hd1] at hz; omega
        have hrem : (n % (4294967295 + d) = 0) ↔ n.toNat % (d.toNat - 1) = 0 := by
          rw [rem_eq_zero_iff, hd1]
        wp_run
        simp
        refine ⟨hne0, ?_⟩
        by_cases h1 : n % (4294967295 + d) = 0
        · -- `d - 1` divides `n`: composite, result `0`
          have hdiv0 : n.toNat % (d.toNat - 1) = 0 := hrem.mp h1
          have hnp : ¬ IsPrimeNat n.toNat := by
            rintro ⟨_, hP⟩
            exact hP (d.toNat - 1) (by omega) (by omega) hdiv0
          simp [h1, primeI, hnp]
        · -- `d - 1` does not divide `n`
          have hd1ne : n.toNat % (d.toNat - 1) ≠ 0 := fun h => h1 (hrem.mpr h)
          by_cases h2 : n = d
          · -- reached `d = n`: every divisor in `[2, n)` checked → prime
            have heq : n.toNat = d.toNat := by rw [h2]
            have hP : IsPrimeNat n.toNat := by
              refine ⟨hn2', fun e he2 hen => ?_⟩
              by_cases he : e ≤ d.toNat - 2
              · exact hdiv e he2 he
              · have : e = d.toNat - 1 := by omega
                rw [this]; exact hd1ne
            simp only [if_neg h1, if_pos h2, primeI, if_pos hP]
          · -- continue the loop with `d + 1`
            have hdlt : d.toNat < n.toNat :=
              lt_of_le_of_ne hdn (fun h => h2 (UInt32.toNat.inj h).symm)
            have hnlt : n.toNat < 4294967296 := by have := n.toNat_lt; omega
            have hmod : (1 + d.toNat) % 4294967296 = d.toNat + 1 := by omega
            simp only [h1, h2, if_false]
            rw [hmod]
            refine ⟨⟨by omega, by omega, fun e he2 hee => ?_⟩, by omega⟩
            by_cases he : e ≤ d.toNat - 2
            · exact hdiv e he2 he
            · have : e = d.toNat - 1 := by omega
              rw [this]; exact hd1ne
  · -- `n < 2`: returns `0`, and `n` is not prime.
    have hlt : n.toNat < 2 := by
      rw [UInt32.le_iff_toNat_le] at hn2
      simpa using hn2
    have hnp : ¬ IsPrimeNat n.toNat := by rintro ⟨h2, _⟩; omega
    simp [hn2, primeI, hnp]

open scoped Classical in
/-- `func0` (fast `[2, n/2]` loop) returns the primality indicator of `n`.
A `tail` of caller values below the argument is framed through unchanged. -/
theorem func0_spec (env : HostEnv Unit) (n : UInt32) (tail : List Value) :
    FuncSpec env «module» 0 (· = .i32 n :: tail)
      (fun _ vs => vs = .i32 (primeI n) :: tail) := by
  apply FuncSpec.of_wp_body (f := ⟨[.i32], [.i32, .i32, .i32, .i32], func0, [.i32]⟩) rfl
  rintro args rfl initial
  unfold func0
  apply wp_block_cons
  wp_run
  by_cases hn2 : 2 ≤ n
  · simp [hn2]
    apply wp_block_cons   -- outer block B
    apply wp_block_cons   -- inner block C (`n < 4` early-prime test)
    wp_run
    simp
    by_cases hn4 : 4 ≤ n
    · -- `n ≥ 4`: run the fast trial-division loop over `[2, n/2]`
      have hn4' : 4 ≤ n.toNat := by
        have := UInt32.le_iff_toNat_le.mp hn4; simpa using this
      have hhalf : (n >>> 1).toNat = n.toNat / 2 := toNat_shiftRight_one n
      simp [hn4]
      apply wp_loop_cons
        (Inv := fun _ s' => ∃ (a e : Value) (d : UInt32),
          s' = { params := [.i32 n], locals := [a, .i32 (n >>> 1), .i32 d, e], values := [] } ∧
            2 ≤ d.toNat ∧ d.toNat ≤ n.toNat / 2 ∧
            (∀ k, 2 ≤ k → k < d.toNat → n.toNat % k ≠ 0))
        (μ := fun _ s' => match s'.locals with
          | [_, _, .i32 d, _] => n.toNat / 2 - d.toNat
          | _ => 0)
      · -- invariant on entry (`d = 2`)
        refine ⟨.i32 0, .i32 0, 2, rfl, by decide, ?_, fun k hk hk2 => ?_⟩
        · have h2t : (2 : UInt32).toNat = 2 := rfl; omega
        · have h2t : (2 : UInt32).toNat = 2 := rfl; omega
      · -- one iteration preserves the invariant / establishes the post
        rintro st' s' ⟨a, e, d, rfl, hd2, hdhalf, hdiv⟩
        have hne_d : ¬ d = 0 := by
          intro h; subst h; exact absurd hd2 (by decide)
        wp_run
        simp
        refine ⟨hne_d, ?_⟩
        by_cases heq : n >>> 1 = d
        · -- `d = n / 2`: this is the final divisor; the loop exits here
          have hdt : d.toNat = n.toNat / 2 := by rw [← heq]; exact hhalf
          simp only [heq, if_true]
          by_cases hdvd : n % d = 0
          · -- `n / 2` divides `n`: composite
            have hdvd0 : n.toNat % d.toNat = 0 := (rem_eq_zero_iff n d).mp hdvd
            have hnp : ¬ IsPrimeNat n.toNat := by
              rintro ⟨_, hP⟩
              exact hP d.toNat (by omega) (by omega) hdvd0
            simp [hdvd, primeI, hnp]
          · -- no divisor in `[2, n/2]`: prime
            have hdvdne : n.toNat % d.toNat ≠ 0 :=
              fun h => hdvd ((rem_eq_zero_iff n d).mpr h)
            have hP : IsPrimeNat n.toNat := by
              rw [prime_iff_fast n.toNat (by omega)]
              intro k hk2 hkhalf
              by_cases hkd : k < d.toNat
              · exact hdiv k hk2 hkd
              · have : k = d.toNat := by omega
                rw [this]; exact hdvdne
            simp [hdvd, primeI, hP]
        · -- `d < n / 2`: keep scanning
          have hdtlt : d.toNat < n.toNat / 2 := by
            refine lt_of_le_of_ne hdhalf (fun h => heq ?_)
            exact UInt32.toNat.inj (by rw [hhalf, h])
          simp only [heq, if_false]
          by_cases hdvd : n % d = 0
          · -- `d` divides `n`: composite
            have hdvd0 : n.toNat % d.toNat = 0 := (rem_eq_zero_iff n d).mp hdvd
            have hnp : ¬ IsPrimeNat n.toNat := by
              rintro ⟨_, hP⟩
              exact hP d.toNat (by omega) (by omega) hdvd0
            simp [hdvd, primeI, hnp]
          · -- `d` does not divide `n`: continue with `d + 1`
            have hdvdne : n.toNat % d.toNat ≠ 0 :=
              fun h => hdvd ((rem_eq_zero_iff n d).mpr h)
            have hnlt : n.toNat < 4294967296 := by have := n.toNat_lt; omega
            have hmod : (1 + d.toNat) % 4294967296 = d.toNat + 1 := by omega
            simp only [hmod]
            refine ⟨⟨by omega, by omega, fun k hk2 hkd => ?_⟩, by omega⟩
            by_cases hkd' : k < d.toNat
            · exact hdiv k hk2 hkd'
            · have : k = d.toNat := by omega
              rw [this]; exact hdvdne
    · -- `n ∈ {2, 3}`: prime
      have h2' : 2 ≤ n.toNat := by
        have := UInt32.le_iff_toNat_le.mp hn2; simpa using this
      have h4' : n.toNat < 4 := by
        rw [UInt32.le_iff_toNat_le] at hn4; simpa using hn4
      have hP : IsPrimeNat n.toNat := by
        refine ⟨h2', fun k hk2 hkn => ?_⟩
        interval_cases n.toNat <;> (interval_cases k <;> decide)
      simp [hn4, primeI, hP]
  · have hlt : n.toNat < 2 := by
      rw [UInt32.le_iff_toNat_le] at hn2; simpa using hn2
    have hnp : ¬ IsPrimeNat n.toNat := by rintro ⟨h2, _⟩; omega
    simp [hn2, primeI, hnp]

open scoped Classical in
/-- `func2` runs both tests, compares them, and (because they agree) never
trips the `unreachable`; it returns with an empty value stack. -/
theorem func2_spec (env : HostEnv Unit) (n : UInt32) :
    FuncSpec env «module» 2 (· = [.i32 n])
      (fun _ vs => vs = []) := by
  apply FuncSpec.of_wp_body (f := ⟨[.i32], [], func2, []⟩) rfl
  rintro args rfl initial
  unfold func2
  apply wp_block_cons
  wp_run
  -- stack: [.i32 n]; call func1 (naive)
  apply wp_call_cons (func1_spec env n [])
  · rfl
  · rintro st1 vs1 rfl
    wp_run
    -- stack: [.i32 n, .i32 (primeI n)]; call func0 (fast) framing the naive result
    apply wp_call_cons (func0_spec env n [.i32 (primeI n)])
    · rfl
    · rintro st0 vs0 rfl
      -- stack: [.i32 (primeI n), .i32 (primeI n)]; `ne` yields 0, `br_if` not taken, `ret`
      wp_run
      simp

/-- Proof that the wasm `check` export never traps.

Proof outline (to be filled in):

1.  Step through the export wrapper `func1` (`.localGet 0; .call 0`)
    to reduce to a `wp` obligation on `func0`.
2.  Unfold `func0` and use `wp_block_cons` to peel the outermost block.
3.  Handle the `n < 3` early-exit branch directly (both algorithms
    return `false` in lockstep).
4.  For `n ≥ 3`, apply `wp_loop_cons` to the naive loop with invariant
        `∃ d, 3 ≤ d ∧ (∀ d' ∈ [2, d), n % d' ≠ 0)`
    and termination measure `n - d`. The loop exits in two ways:
    either it finds a divisor (`local 2 = 0`) or it walks to `d = n`
    (prime).
5.  Apply `wp_loop_cons` to the fast loop with invariant
        `∃ d, 2 ≤ d ∧ (∀ d' ∈ [2, d), n % d' ≠ 0)`
    and termination measure `n / 2 - d`. Same two exits, bounded by
    `n / 2`.
6.  Close the post-loop comparison block by `prime_iff_fast`: both
    loops yield the same composite/prime verdict, so the
    `br_if`/`br 2 → unreachable` edge is never taken.
-/
@[proves Project.IsPrime.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro env initial n
  -- `func3` is the exported `check` wrapper: it just forwards `n` to `func2`.
  apply TerminatesWith.of_wp_entry (f := ⟨[.i32], [], func3, []⟩) rfl
  intro initial'
  unfold func3
  wp_run
  apply wp_call_cons (func2_spec env n)
  · rfl
  · rintro st' vs rfl
    wp_run
    rfl

end Project.IsPrime.Spec
