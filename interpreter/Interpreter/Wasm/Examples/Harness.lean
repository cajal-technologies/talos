import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.SmallStep

/-!
# `Wasm.Examples` — shared harness for the worked examples

The remaining decoder-oriented examples pin behavior with `native_decide`.
These compatibility projections execute only the authoritative small-step
runner; they do not call the retained big-step semantics.

* `runValues` / `runTrapMsg` / `runInvalidMsg` — initialize a small-step
  configuration and project its success stack / structured trap / internal
  diagnostic. `env` defaults to the empty host environment.
* `decodeOrDefault` — decode a WAT module, falling back to `default` on error
  (each decoder example pins the success shape with a separate decidable check,
  so the fallback is never actually hit).
-/

namespace Wasm.Examples
open Wasm.SmallStep

/-- Legacy example fuel counted recursive big steps rather than individual
machine transitions. Compatibility projections deliberately over-approximate
it; no specification may depend on this scaling. -/
private def smallStepFuel (fuel : Nat) : Nat := fuel * 16

/-- Run `m`'s function `idx` and keep the returned stack, or `[]` on any
non-`Success` outcome. Total, so `native_decide` can evaluate it without
`DecidableEq (Store Unit)`. -/
def runValues (fuel : Nat) (m : Module) (idx : Nat) (st : Store Unit)
    (args : List Value) (env : HostEnv Unit := {}) : List Value :=
  match initConfig { module := m, host := env } idx st args with
  | .error _ => []
  | .ok config =>
    match (runSteps (smallStepFuel fuel) config).result with
    | .success values _ => values
    | _ => []

/-- Project the trap message (if the run trapped) out of the `Result`. -/
def runTrapMsg (fuel : Nat) (m : Module) (idx : Nat) (st : Store Unit)
    (args : List Value) (env : HostEnv Unit := {}) : Option String :=
  match initConfig { module := m, host := env } idx st args with
  | .error _ => none
  | .ok config =>
    match (runSteps (smallStepFuel fuel) config).result with
    | .trapped reason _ => some reason.message
    | _ => none

/-- Project the invalidation message (if the run was rejected as invalid) out of
the `Result`. -/
def runInvalidMsg (fuel : Nat) (m : Module) (idx : Nat) (st : Store Unit)
    (args : List Value) (env : HostEnv Unit := {}) : Option String :=
  match initConfig { module := m, host := env } idx st args with
  | .error error => some error.message
  | .ok config =>
    match (runSteps (smallStepFuel fuel) config).result with
    | .internalError error _ => some error.message
    | _ => none

/-- Decode a WAT module, falling back to `default` on a decode error. Decoder
examples check the decoded shape with a separate decidable projection, so the
fallback is a placeholder that is never reached on a well-formed input. -/
def decodeOrDefault (wat : String) : Wasm.Module :=
  match Wasm.Decoder.Wat.decode wat with
  | .ok m => m
  | .error _ => default

end Wasm.Examples
