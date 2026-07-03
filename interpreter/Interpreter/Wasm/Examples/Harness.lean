import Interpreter.Wasm.Semantics
import Interpreter.Wasm.Decoder.Wat

/-!
# `Wasm.Examples` — shared harness for the worked examples

The examples pin behaviour with `native_decide`, which needs a *decidable*
target. `Store α` has no `DecidableEq`, so a check cannot compare whole
`Result`s; it projects the piece it cares about (the returned stack, or a trap /
invalid message) out of the `Result` first. Every example used to re-declare its
own copy of that projection (under two spellings, `runValues` / `runVals`), plus
a `decode`-or-`default` wrapper. Those live here once.

* `runValues` / `runTrapMsg` / `runInvalidMsg` — run a function and project the
  success stack / trap message / invalid message. `env` defaults to the empty
  host env, so pure-wasm examples omit it.
* `decodeOrDefault` — decode a WAT module, falling back to `default` on error
  (each decoder example pins the success shape with a separate decidable check,
  so the fallback is never actually hit).

The two `UInt32.toNat_sub_one_*` lemmas support the loop / recursion examples,
whose invariants step a `UInt32` counter down by one; they replace a proof block
that was pasted six times across `SimpleLoop` / `Factorial` / `EvenOddRec`.
-/

namespace Wasm.Examples

/-- Run `m`'s function `idx` and keep the returned stack, or `[]` on any
non-`Success` outcome. Total, so `native_decide` can evaluate it without
`DecidableEq (Store Unit)`. -/
def runValues (fuel : Nat) (m : Module) (idx : Nat) (st : Store Unit)
    (args : List Value) (env : HostEnv Unit := {}) : List Value :=
  match run fuel m idx st args env with
  | .Success vs _ => vs
  | _ => []

/-- Project the trap message (if the run trapped) out of the `Result`. -/
def runTrapMsg (fuel : Nat) (m : Module) (idx : Nat) (st : Store Unit)
    (args : List Value) (env : HostEnv Unit := {}) : Option String :=
  match run fuel m idx st args env with
  | .Trap _ msg => some msg
  | _ => none

/-- Project the invalidation message (if the run was rejected as invalid) out of
the `Result`. -/
def runInvalidMsg (fuel : Nat) (m : Module) (idx : Nat) (st : Store Unit)
    (args : List Value) (env : HostEnv Unit := {}) : Option String :=
  match run fuel m idx st args env with
  | .Invalid msg => some msg
  | _ => none

/-- Decode a WAT module, falling back to `default` on a decode error. Decoder
examples check the decoded shape with a separate decidable projection, so the
fallback is a placeholder that is never reached on a well-formed input. -/
def decodeOrDefault (wat : String) : Wasm.Module :=
  match Wasm.Decoder.Wat.decode wat with
  | .ok m => m
  | .error _ => default

end Wasm.Examples

/-! ## `UInt32` counter-stepping lemmas

Shared by the loop / recursion examples: their measures step a `UInt32` counter
down by one, and both the decreasing-measure obligation and the invariant
re-establishment need `(x - 1).toNat` in `Nat` terms. `x ≠ 0` rules out the
`0 - 1` wraparound (`0 - 1 = 0xFFFFFFFF` on `UInt32`, but `0 - 1 = 0` on `Nat`).
-/

/-- On `UInt32`, when `x ≠ 0` the wrapping predecessor agrees with `Nat`
subtraction: `(x - 1).toNat = x.toNat - 1`. -/
theorem UInt32.toNat_sub_one_eq {x : UInt32} (hx : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  rw [UInt32.toNat_sub]
  simp only [show (1 : UInt32).toNat = 1 from rfl]
  have := x.toNat_lt
  omega

/-- On `UInt32`, when `x ≠ 0` the wrapping predecessor strictly decreases the
`Nat` value — the standard loop / recursion variant step. -/
theorem UInt32.toNat_sub_one_lt {x : UInt32} (hx : x.toNat ≠ 0) :
    (x - 1).toNat < x.toNat := by
  rw [UInt32.toNat_sub]
  simp only [show (1 : UInt32).toNat = 1 from rfl]
  have := x.toNat_lt
  omega
