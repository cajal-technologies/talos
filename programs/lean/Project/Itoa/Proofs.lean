import Project.Itoa.Proofs.Base
import Project.Itoa.Proofs.NaiveU64
import Project.Itoa.Proofs.NaiveI64
import Project.Itoa.Proofs.Fast

/-!
# Proof of `CheckI64Spec` / `CheckU64Spec`

The exported `check_*(n, cap)` runs the `itoa`-crate formatter and a
naive `% 10` oracle into two on-stack buffers and traps via `unreachable`
iff they disagree. No-trap is therefore the equivalence of the two
formatters; both compute the decimal representation of `n`.

Unoptimized (`opt-level=0`) pipeline: the export chains are
`check_i64 = func31 → func28 → func21` (harness) and
`check_u64 = func32 → func29 → func23`. Inside a harness, the fast
formatter is `func24`/`func22` (wrapping the `itoa` core) and the naive
oracle is `func3 → func4` (i64) / `func5 → func6` (u64); `func7` clamps
the capacity and a byte-compare loop traps on any disagreement.

This file is built bottom-up:

1. `wp_call_of_terminates` — step a `.call id` from a `TerminatesWith`
   proof of the callee *at the concrete current store*. (`FuncSpec`
   quantifies over all stores and so is unusable for callees that can
   trap on a small/garbage memory; the harness only ever runs from
   `«module».initialStore`.)
2. `decimalDigits` — the shared decimal-string reference both formatters
   are proven to produce, plus the byte-level framing, `DIGIT_TABLE`,
   and magic-division lemma layers (all carried over from the
   pre-migration proof; only the table base moved, to `1049408`).
3. export-wrapper bridges (`func31`/`func32` and `func28`/`func29`)
   peeling the shadow-stack hops, and the conditional top-level
   theorems reducing `CheckI64Spec` / `CheckU64Spec` to `HarnessSpec
   21` / `HarnessSpec 23`.

The pre-migration proofs of the *old* register-allocated function
bodies (naive formatters `func0`/`func1`, fast-formatter base cases
`func13`, slice packaging `func14`, checked memcpy `func56`) do not
transfer: under `opt-level=0` those functions were regenerated as
memory-routed code with new indices. The whole naive side is re-proven
below, parametric in the shadow-stack pointer `g` as `HarnessSpec`'s
∀-`g` quantification requires: the u64 core `func6` (`func6_spec`, its
two memory-routed loops factored into standalone `wp` lemmas over an
abstract continuation so the per-iteration proofs stay small), its
wrapper `func5`, the i64 core `func4` (delegating to `func6` for
non-negative inputs, with its own loop lemmas for the negative path),
its wrapper `func3`, the capacity clamp `func7`, and the harness
byte-compare loop (`harness_compare_loop`, shared by `func23` and
`func21`). Re-proving the fast-formatter core (`func40` and its
helpers, behind `func22`/`func24`) — and then discharging the
`HarnessSpec` hypotheses — is the remaining open work.
-/

