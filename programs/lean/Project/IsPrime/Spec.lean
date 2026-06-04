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
    TerminatesWith env «module» 0 initial [.i32 n]
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
  sorry

/-- Equivalence of the two trial-division ranges: scanning `[2, n)`
finds a divisor iff scanning `[2, n / 2]` does. Direct corollary of
[`not_dvd_of_gt_half`]; this is the algorithmic content of the
equivalence proof, independent of the wasm encoding. -/
theorem prime_iff_fast (n : Nat) (hn : 2 ≤ n) :
    IsPrimeNat n ↔ (∀ d, 2 ≤ d → d ≤ n / 2 → n % d ≠ 0) := by
  sorry

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
  sorry

end Project.IsPrime.Spec
