import Interpreter.Wasm.Host.Universal

/-!
# Worked examples: one host for every module

Four properties a per-host environment cannot have, demonstrated on concrete
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
4. **Semantic exported calls.** A parameterized export can be stated through
   semantic `args` and `result` adapters while the public proposition mentions
   only its input, output and mathematical property.
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

theorem mixed_covered : covers mixed = true := by native_decide

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
theorem mixed_writes_entropy_byte : mixedOutput (fun _ => 7) 50 = some [7] := by
  native_decide

/-- And it is genuinely the oracle's first byte that is written. -/
theorem mixed_writes_first_oracle_byte :
    mixedOutput (fun index => if index = 0 then 42 else 0) 50 = some [42] := by
  native_decide

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

theorem writeOnly_covered : covers writeOnly = true := by native_decide

theorem writeOnly_emit_zeroArgument : ZeroArgumentExport writeOnly "emit" := by
  native_decide

def writeOnlyOutput (fuel : Nat) : Option (List UInt8) :=
  match SmallStep.initConfig { module := writeOnly, host := envFor writeOnly }
      1 { (writeOnly.initialStore (α := State)) with host := default } [] with
  | .error _ => none
  | .ok config =>
    match (SmallStep.runSteps fuel config).result with
    | .success _ final => some final.wasm.host.stdio.output
    | _ => none

/-- The declared import reaches `write`, because it was resolved by name. -/
theorem writeOnly_emits : writeOnlyOutput 30 = some [9] := by native_decide

/-- The hazard this avoids, stated as a fact rather than a warning: under the
hand-built positional environment the same module's `call 0` lands on `read`,
which writes memory and returns a count instead of emitting anything. -/
theorem writeOnly_positional_env_resolves_read :
    StdIO.env.funcs[0]?.map HostFn.results = some [.i32] := by native_decide

/-- Whereas name-keyed resolution gives it the arity `write` actually has. -/
theorem writeOnly_named_env_resolves_write :
    (envFor writeOnly).funcs[0]?.map HostFn.results = some [] := by
  native_decide

/-! ## 3. A module importing nothing -/

def pure : Module :=
  { funcs := [{ body := [.const 7], results := [.i32] }]
    exports := [{ name := "seven", funcIdx := 0 }] }

/-- Import-free modules are served by the empty environment definitionally, so
adopting the universal host costs them nothing. -/
theorem pure_env : envFor pure = HostEnv.empty := rfl

theorem pure_covered : covers pure = true := by native_decide

/-! ## 4. A semantic specification for a parameterized export -/

namespace SemanticExport

/-- A one-argument identity export, deliberately small enough that the example
tests the specification interface rather than another Wasm feature. -/
def identity : Module :=
  { funcs :=
      [{ params := [.i32], body := [.localGet 0], results := [.i32] }]
    exports := [{ name := "identity", funcIdx := 0 }] }

/-- The semantic input of `identity`; its Wasm representation is kept in
`args` below. -/
structure Input where
  value : UInt32

/-- The semantic output of `identity`. -/
abbrev Output := UInt32

def identityConfig (input : UInt32) : SmallStep.Config State :=
  { expr := .running
      { locals := { params := [.i32 input] }
        code := [.localGet 0]
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := identity, host := envFor identity }]
            entry := ⟨0⟩ }
        wasm := { (identity.initialStore : Store State) with host := default } } }

/-- The ABI adapter is separate from the proposition: clients read `input`,
not a list of raw Wasm values. -/
def args (input : Input) : ExportCall State :=
  ExportCall.ofHost identity default [.i32 input.value]

/-- Likewise the result adapter gives a semantic name and type to the raw
return stack. -/
def result (output : Output) : ExportReturn State → Prop :=
  fun returned => returned.values = [.i32 output]

private abbrev Runs := RunsExport identity

theorem identity_rejects_missing_argument :
    startExportConfig? (envFor identity) identity "identity"
      (ExportCall.ofHost identity default) = none := by
  rfl

theorem identity_rejects_extra_argument :
    startExportConfig? (envFor identity) identity "identity"
      (ExportCall.ofHost identity default [.i32 1, .i32 2]) = none := by
  rfl

theorem identity_rejects_wrong_argument_type :
    startExportConfig? (envFor identity) identity "identity"
      (ExportCall.ofHost identity default [.i64 1]) = none := by
  rfl

/-- This is the intended public grammar. `Runs` still denotes a concrete
finite execution; the final conjunct states the mathematical property. -/
theorem identity_specification :
    ∀ input : Input,
      ∃ output : Output,
        Runs "identity" (args input) (result output) ∧
        output = input.value := by
  intro input
  refine ⟨input.value, ?_, rfl⟩
  unfold Runs RunsExport RunsExportWith
  refine ⟨identityConfig input.value, rfl, ?_⟩
  exact SmallStep.runSteps_values_terminates (fuel := 2) (by rfl)

theorem identity_output_unique
    (first : Runs "identity" (args input) (result firstOutput))
    (second : Runs "identity" (args input) (result secondOutput)) :
    firstOutput = secondOutput := by
  obtain ⟨returned, hfirst, hsecond⟩ :=
    RunsExportWith.deterministic first second
  have valuesEq : ([.i32 firstOutput] : List Value) = [.i32 secondOutput] :=
    hfirst.symm.trans hsecond
  injection valuesEq with headEq
  exact Value.i32.inj headEq

/-- A partial specification quantifies the semantic output *inside* the
postcondition for every raw successful return. This both decodes every return
and states its property; merely writing `Runs ... → property` would additionally
need a separate proof that `result` recognizes every raw return. -/
theorem identity_partial (input : Input) :
    PartiallyRunsExport identity "identity" (args input)
      (fun returned =>
        ∃ output : Output,
          result output returned ∧ output = input.value) := by
  unfold PartiallyRunsExport PartiallyRunsExportWith
  refine ⟨identityConfig input.value, rfl, ?_⟩
  refine (SmallStep.runSteps_values_terminates
    (fuel := 2) (by rfl)).toPartiallyMeets.mono ?_
  intro values final hvalues
  exact ⟨input.value, hvalues, rfl⟩

/-- The same packaged arguments feed the outcome-valued relation when a
specification needs to distinguish a return from a structural trap. -/
theorem identity_outcome :
    ∀ input : Input,
      RunsExportOutcome identity "identity" (args input)
        (fun observed =>
          observed.outcome = .done [.i32 input.value]) := by
  intro input
  unfold RunsExportOutcome RunsExportWithOutcome
  refine ⟨identityConfig input.value, rfl, ?_⟩
  obtain ⟨trace, values, store, execution, hvalues⟩ :=
    SmallStep.runSteps_values_terminates (fuel := 2) (by rfl :
      (SmallStep.runSteps 2 (identityConfig input.value)).result.values? =
        some [.i32 input.value])
  subst values
  exact ⟨trace, .done [.i32 input.value], store, execution, rfl⟩

end SemanticExport

end Wasm.Examples.UniversalHost
