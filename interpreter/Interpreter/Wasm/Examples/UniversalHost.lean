import Interpreter.Wasm.Host.Universal

/-!
# Worked examples: one host for every module

Three properties a per-host environment cannot have, demonstrated on concrete
modules run under `Universal.envFor`.

1. **Mixed imports.** A module may import `random.get` and `stdio.write`
   together. Neither `Random.env` nor `StdIO.env` can serve it: each is a fixed
   positional list, and this module's index 1 is a function the other host owns.
2. **Subsets, safely.** A module may import `stdio.write` alone. This one is
   worth dwelling on: `StdIO.env.funcs` is `[readHost, writeHost]`, so under
   `StdIO.env` a lone `stdio.write` import resolves at index 0 to *`read`* — it
   runs, silently, doing the wrong thing. Name-keyed resolution cannot make that
   mistake.
3. **No imports.** A module importing nothing is served by the empty
   environment, definitionally, so nothing about the universal host leaks into
   the 13 emitted programs that declare `imports := []`.
-/

namespace Wasm.Examples.UniversalHost

open Wasm.Universal

/-! ## 1. A module importing two different hosts

Draws one entropy byte into address zero, then writes that byte to standard
output. Both argument lists follow their own host's convention: `random.get`
takes `(pointer, length)`, `stdio.write` takes `(length, pointer)`. -/

def mixed : Module :=
  { imports :=
      [ { «module» := "random", name := "get",
          params := [.i32, .i32], results := [] }
      , { «module» := "stdio", name := "write",
          params := [.i32, .i32], results := [] } ]
    funcs := [{ body := [.const 0, .const 1, .call 0,
                         .const 1, .const 0, .call 1] }]
    memory := some { pagesMin := 1 }
    exports := [{ name := "roll", funcIdx := 2 }] }

theorem mixed_covered : covers mixed = true := by decide +kernel

def mixedStore (oracle : Random.Oracle) : Store State :=
  { (mixed.initialStore (α := State)) with
      host := State.ofInputAndOracle [] oracle }

/-- Run `mixed` and report what reached standard output. -/
def mixedOutput (oracle : Random.Oracle) (fuel : Nat) : Option (List UInt8) :=
  match SmallStep.initConfig { module := mixed, host := envFor mixed }
      2 (mixedStore oracle) [] with
  | .error _ => none
  | .ok config =>
    match (SmallStep.runSteps fuel config).result with
    | .success _ final => some final.wasm.host.stdio.output
    | _ => none

/-- The entropy byte crosses from one host's state, through linear memory, into
the other host's state — in a single run, under a single environment. -/
theorem mixed_writes_entropy_byte : mixedOutput (fun _ => 7) 50 = some [7] := by decide +kernel

/-- And it is genuinely the oracle's first byte that is written. -/
theorem mixed_writes_first_oracle_byte :
    mixedOutput (fun index => if index = 0 then 42 else 0) 50 = some [42] := by decide +kernel

/-! ## 2. A module importing one function of a two-function host -/

def writeOnly : Module :=
  { imports :=
      [ { «module» := "stdio", name := "write",
          params := [.i32, .i32], results := [] } ]
    funcs := [{ body := [.const 1, .const 0, .call 0] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := some 0, bytes := [9] }] }
    exports := [{ name := "emit", funcIdx := 1 }] }

theorem writeOnly_covered : covers writeOnly = true := by decide +kernel

def writeOnlyOutput (fuel : Nat) : Option (List UInt8) :=
  match SmallStep.initConfig { module := writeOnly, host := envFor writeOnly }
      1 { (writeOnly.initialStore (α := State)) with host := default } [] with
  | .error _ => none
  | .ok config =>
    match (SmallStep.runSteps fuel config).result with
    | .success _ final => some final.wasm.host.stdio.output
    | _ => none

/-- The declared import reaches `write`, because it was resolved by name. -/
theorem writeOnly_emits : writeOnlyOutput 30 = some [9] := by decide +kernel

/-- The hazard this avoids, stated as a fact rather than a warning: under the
hand-built positional environment the same module's `call 0` lands on `read`,
which writes memory and returns a count instead of emitting anything. -/
theorem writeOnly_positional_env_resolves_read :
    StdIO.env.funcs[0]?.map HostFn.results = some [.i32] := by decide +kernel

/-- Whereas name-keyed resolution gives it the arity `write` actually has. -/
theorem writeOnly_named_env_resolves_write :
    (envFor writeOnly).funcs[0]?.map HostFn.results = some [] := by decide +kernel

/-! ## 3. A module importing nothing -/

def pure : Module :=
  { funcs := [{ body := [.const 7], results := [.i32] }]
    exports := [{ name := "seven", funcIdx := 0 }] }

/-- Import-free modules are served by the empty environment definitionally, so
adopting the universal host costs them nothing. -/
theorem pure_env : envFor pure = HostEnv.empty := rfl

theorem pure_covered : covers pure = true := by decide +kernel

end Wasm.Examples.UniversalHost
