import Lean.Data.Json
import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Host.Run
import Interpreter.Wasm.SpecTest.Run
import Interpreter.Wasm.SpecTest.Verdict
import Interpreter.Wasm.SpecTest.Gen.Basic
import Interpreter.Wasm.SpecTest.Gen.Module
import Interpreter.Wasm.SpecTest.Json

/-!
# The `spec_test` command line

A problem workspace instantiates `runCli` with a `Problem`: its compiled module,
the specification's start configuration (parametric in the module, so a mutant
starts from the same state), its codec, and the executable postcondition.

```
lake exe spec_test [--wat f] [--diff f] [--n N] [--seed S] [--exhaustive-to K]
                   [--budget-seconds T] [--input <hex>] [--trace] [--max-len L]
                   [--len L] [--families edge,exhaustive,module,random]
                   [--config config.json] [--keep-going]
```

One JSON object on stdout; diagnostics on stderr. Exit codes: `0` pass (or
vacuous-only, or `--diff` identical), `1` counterexample (or `--diff`
different), `2` error. The specification's shape is read from `config.json`
(`spec_test.shape`).

Fuel: the unmodified module runs with a fixed cap (`10^7`); an out-of-fuel run
there is counted separately (`out_of_fuel`), never as a counterexample. A module
loaded with `--wat`/`--diff` runs each input with
`max(10 × steps of the original on that input, 10^6)`.
-/

namespace Wasm.SpecTest

open Lean (Json toJson)

/-- What a problem workspace supplies. -/
structure Problem (ι : Type) where
  /-- The export the specification runs. -/
  op : String
  /-- The compiled module the specification is about. -/
  «module» : Module
  /-- The start configuration exactly as the specification builds it, for any
  module with the same interface. -/
  start : Module → ι → Option (SmallStep.Config Universal.State)
  /-- The executable postcondition (`@[spec_test] post`) on an observation. -/
  post : ι → Observation → Bool
  /-- The input's byte encoding (for reports and `--input`). -/
  encode : ι → List UInt8
  decode? : List UInt8 → Option ι

structure Options where
  wat : Option String := none
  diff : Option String := none
  n : Nat := 1000
  seed : Nat := 0x5EED
  exhaustiveTo : Option Nat := none
  budgetSeconds : Option Nat := none
  input : Option String := none
  trace : Bool := false
  maxLen : Nat := 32
  fixedLen : Option Nat := none
  families : List Family := Family.all
  configPath : String := "config.json"
  fuelCap : Nat := 10_000_000
  keepGoing : Bool := false

def usage : String :=
  "usage: spec_test [--wat f] [--diff f] [--n N] [--seed S] [--exhaustive-to K] [--budget-seconds T] " ++
  "[--input <hex>] [--trace] [--max-len L] [--len L] [--families edge,exhaustive,module,random] " ++
  "[--config config.json] [--keep-going]"

def parseNat (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a natural number, got `{value}`"

def parseFamilies (value : String) : Except String (List Family) :=
  (value.splitOn ",").mapM fun s =>
    match Family.ofString? s with
    | some f => .ok f
    | none => .error s!"unknown family `{s}` (edge, exhaustive, module, random)"

partial def parseOptions : List String → Options → Except String Options
  | [], o => .ok o
  | "--wat" :: f :: rest, o => parseOptions rest { o with wat := some f }
  | "--diff" :: f :: rest, o => parseOptions rest { o with diff := some f }
  | "--n" :: v :: rest, o => do parseOptions rest { o with n := ← parseNat "--n" v }
  | "--seed" :: v :: rest, o => do parseOptions rest { o with seed := ← parseNat "--seed" v }
  | "--exhaustive-to" :: v :: rest, o => do
    parseOptions rest { o with exhaustiveTo := some (← parseNat "--exhaustive-to" v) }
  | "--budget-seconds" :: v :: rest, o => do
    parseOptions rest { o with budgetSeconds := some (← parseNat "--budget-seconds" v) }
  | "--input" :: v :: rest, o => parseOptions rest { o with input := some v }
  | "--trace" :: rest, o => parseOptions rest { o with trace := true }
  | "--max-len" :: v :: rest, o => do parseOptions rest { o with maxLen := ← parseNat "--max-len" v }
  | "--len" :: v :: rest, o => do parseOptions rest { o with fixedLen := some (← parseNat "--len" v) }
  | "--families" :: v :: rest, o => do parseOptions rest { o with families := ← parseFamilies v }
  | "--config" :: f :: rest, o => parseOptions rest { o with configPath := f }
  | "--fuel-cap" :: v :: rest, o => do parseOptions rest { o with fuelCap := ← parseNat "--fuel-cap" v }
  | "--keep-going" :: rest, o => parseOptions rest { o with keepGoing := true }
  | arg :: _, _ => .error s!"unknown or incomplete argument `{arg}`"

/-- The shape recorded in `config.json` under `spec_test.shape`. -/
def readShape (path : String) : IO (Except String Shape) := do
  let text ← try IO.FS.readFile path catch e => return .error s!"cannot read {path}: {e}"
  match Json.parse text with
  | .error e => return .error s!"{path}: {e}"
  | .ok json =>
    match json.getObjVal? "spec_test" with
    | .error _ => return .error s!"{path} has no `spec_test` block"
    | .ok block =>
      match block.getObjValAs? String "shape" with
      | .error _ => return .error s!"{path}: `spec_test.shape` is missing"
      | .ok name =>
        match Shape.ofString? name with
        | some shape => return .ok shape
        | none => return .error s!"{path}: unknown `spec_test.shape` `{name}`"

/-- Parse a `.wat` file at runtime with the verification decoder, which refuses
to silently drop an unsupported instruction. -/
def loadWat (path : String) : IO (Except String Module) := do
  let text ← try IO.FS.readFile path catch e => return .error s!"cannot read {path}: {e}"
  match Wasm.Decoder.Wat.decodeForVerification text with
  | .ok m => return .ok m
  | .error e => return .error s!"{path}: {e}"

def errorObservation (message : String) : Observation :=
  { termination := .internalError message, output := [], oomRaised := false, steps := 0,
    functions := [] }

def originalFuel (o : Options) : Nat := o.fuelCap

def candidateFuel (originalSteps : Nat) : Nat := max (10 * originalSteps) 1_000_000

section
variable {ι : Type} [Domain ι] (p : Problem ι) (shape : Shape) (o : Options)

/-- Run one module on one input. -/
def observeOn (m : Module) (fuel : Nat) (x : ι) : Observation :=
  match p.start m x with
  | some config => observe fuel config (m.findExport p.op)
  | none => errorObservation s!"export `{p.op}` cannot be entered"

/-- The observation that decides an input's verdict, with the verdict: the
original module under its fixed cap, or a candidate under the relative fuel. The
flag says whether a candidate's observation differs from the original's on this
input (always `false` for the original). -/
def evaluate (candidate : Option Module) (x : ι) : Observation × Verdict × Bool :=
  match candidate with
  | none =>
    let obs := observeOn p p.module (originalFuel o) x
    (obs, classify shape true (p.post x) obs, false)
  | some m =>
    let reference := observeOn p p.module (originalFuel o) x
    let obs := observeOn p m (candidateFuel reference.steps) x
    (obs, classify shape false (p.post x) obs, !reference.sameAs obs)

/-- Greedy shrinking: repeatedly move to the first simpler input that still fails. -/
partial def shrinkFailure (candidate : Option Module) (x : ι) (obs : Observation)
    (verdict : Verdict) (budget : Nat) : ι × Observation × Verdict × Nat :=
  if budget = 0 then (x, obs, verdict, 0) else
  let next := (Domain.shrink x).findSome? fun y =>
    let (obs', verdict', _) := evaluate p shape o candidate y
    if verdict'.isFail then some (y, obs', verdict') else none
  match next with
  | some (y, obs', verdict') =>
    let (z, obsZ, verdictZ, steps) := shrinkFailure candidate y obs' verdict' (budget - 1)
    (z, obsZ, verdictZ, steps + 1)
  | none => (x, obs, verdict, 0)

end

/-- The inputs of one family for this problem's input type. -/
def inputsOf {ι : Type} [Domain ι] (_p : Problem ι) (o : Options) (fam : Family)
    (cfg : GenConfig) (constants : List Nat) : List ι :=
  match fam with
  | .edge => Domain.edges
  | .exhaustive => Domain.exhaustive cfg
  | .moduleDerived => Domain.fromConstants cfg constants
  | .random =>
    let rec draw : Nat → Rng → List ι → List ι
      | 0, _, acc => acc.reverse
      | k + 1, g, acc => let (x, g) := Domain.random cfg g; draw k g (x :: acc)
    draw o.n (Rng.ofSeed (UInt64.ofNat o.seed)) []

structure Tally where
  inputs : Nat := 0
  pass : Nat := 0
  /-- Passes on inputs with no simpler input (`Domain.shrink x = []`: the empty list, `(0, 0)`). -/
  trivialPass : Nat := 0
  /-- Passes where a candidate's observation differs from the original's: the specification accepts
  a different normal outcome (a witness that the contract is weaker than the program). -/
  passDifferent : Nat := 0
  fail : Nat := 0
  vacuousOom : Nat := 0
  vacuousDivergent : Nat := 0
  outOfFuel : Nat := 0
  error : Nat := 0

def Tally.add (t : Tally) : Verdict → Tally
  | .pass => { t with inputs := t.inputs + 1, pass := t.pass + 1 }
  | .fail _ => { t with inputs := t.inputs + 1, fail := t.fail + 1 }
  | .vacuousOom => { t with inputs := t.inputs + 1, vacuousOom := t.vacuousOom + 1 }
  | .vacuousDivergent => { t with inputs := t.inputs + 1, vacuousDivergent := t.vacuousDivergent + 1 }
  | .outOfFuelOriginal => { t with inputs := t.inputs + 1, outOfFuel := t.outOfFuel + 1 }
  | .error _ => { t with inputs := t.inputs + 1, error := t.error + 1 }

def Tally.json (t : Tally) : Json :=
  Json.mkObj [("inputs", toJson t.inputs), ("pass", toJson t.pass), ("fail", toJson t.fail),
    ("trivial_pass", toJson t.trivialPass), ("pass_different", toJson t.passDifferent),
    ("vacuous_oom", toJson t.vacuousOom), ("vacuous_divergent", toJson t.vacuousDivergent),
    ("out_of_fuel", toJson t.outOfFuel), ("error", toJson t.error)]

/-- Count a pass on a shrink-minimal input as trivial, and a pass whose observation
differs from the original's as a different pass. -/
def Tally.noteTrivial (t : Tally) (verdict : Verdict) (minimal differs : Bool) : Tally :=
  match verdict with
  | .pass =>
    let t := if minimal then { t with trivialPass := t.trivialPass + 1 } else t
    if differs then { t with passDifferent := t.passDifferent + 1 } else t
  | _ => t

def configJson (o : Options) (shape : Shape) (source : String) (truncated : Bool) : Json :=
  Json.mkObj
    [ ("shape", Json.str shape.name), ("module", Json.str source), ("seed", toJson o.seed)
    , ("n", toJson o.n), ("exhaustive_to", toJson o.exhaustiveTo)
    , ("budget_seconds", toJson o.budgetSeconds), ("max_len", toJson o.maxLen)
    , ("len", toJson o.fixedLen)
    , ("families", Json.arr (o.families.map (Json.str ·.name)).toArray)
    , ("fuel", Json.mkObj [("original_cap", toJson o.fuelCap),
        ("candidate", Json.str "max(10 * steps of the original, 1000000)")])
    , ("truncated_by_budget", toJson truncated) ]

def coverageJson (m : Module) (executed : List Nat) : Json :=
  let total := m.imports.length + m.funcs.length
  let never := (List.range total).filter fun i => !executed.contains i
  Json.mkObj [("functions_total", toJson total), ("executed", toJson executed),
    ("never_executed", toJson never)]

def emit (json : Json) (code : UInt32) : IO UInt32 := do
  IO.println json.compress
  return code

def fail2 (message : String) : IO UInt32 := do
  IO.eprintln s!"spec_test: {message}"
  emit (Json.mkObj [("verdict", Json.str "error"), ("message", Json.str message)]) 2

def inputJson {ι : Type} [Domain ι] (p : Problem ι) (x : ι) (fam : Option Family) : Json :=
  Json.mkObj ([("value", Domain.toJson x), ("hex", Json.str (hexOfBytes (p.encode x)))] ++
    (match fam with | some f => [("family", Json.str f.name)] | none => []))

def sortNats (xs : List Nat) : List Nat := xs.mergeSort (fun a b => decide (a ≤ b))

/-- Test the subject module (the original, or `--wat`) on every generated input. -/
def testAll {ι : Type} [Domain ι] (p : Problem ι) (shape : Shape) (o : Options)
    (candidate : Option Module) (source : String) : IO UInt32 := do
  let started ← IO.monoMsNow
  let subject := candidate.getD p.module
  let cfg : GenConfig := { exhaustiveTo := o.exhaustiveTo, maxLen := o.maxLen, fixedLen := o.fixedLen }
  let constants := moduleConstants subject
  let mut total : Tally := {}
  let mut perFamily : Array Tally := #[{}, {}, {}, {}]
  let mut seen : Std.HashSet Nat := {}
  let mut counterexample : Option Json := none
  let mut firstError : Option String := none
  let mut truncated := false
  let mut maxSteps := 0
  for fam in o.families do
    if counterexample.isSome && !o.keepGoing then break
    for x in inputsOf p o fam cfg constants do
      if let some secs := o.budgetSeconds then
        if (← IO.monoMsNow) - started ≥ secs * 1000 then
          truncated := true
          break
      let (obs, verdict, differs) := evaluate p shape o candidate x
      let minimal := (Domain.shrink x).isEmpty
      total := (total.add verdict).noteTrivial verdict minimal differs
      perFamily := perFamily.modify fam.index (fun t => (t.add verdict).noteTrivial verdict minimal differs)
      for f in obs.functions do seen := seen.insert f
      maxSteps := max maxSteps obs.steps
      if let .error message := verdict then
        if firstError.isNone then firstError := some message
      if verdict.isFail && counterexample.isNone then
        let (small, smallObs, smallVerdict, shrinkSteps) :=
          shrinkFailure p shape o candidate x obs verdict 100
        counterexample := some (Json.mkObj
          [ ("input", inputJson p small (some fam))
          , ("original_input", inputJson p x (some fam))
          , ("shrink_steps", toJson shrinkSteps)
          , ("failed_clause", Json.str (smallVerdict.detail.getD ""))
          , ("outcome", observationJson smallObs) ])
        if !o.keepGoing then break
    if truncated then break
  let elapsed := (← IO.monoMsNow) - started
  let verdict :=
    if counterexample.isSome then "fail"
    else if total.error > 0 then "error"
    -- every non-trivial input ended vacuously: a module that cannot allocate still "sorts" the empty list
    else if total.pass == total.trivialPass && total.vacuousOom + total.vacuousDivergent > 0 then "vacuous-only"
    else if total.inputs == 0 then "error"
    else "pass"
  let families := Family.all.map fun f => (f.name, (perFamily.getD f.index {}).json)
  let json := Json.mkObj
    [ ("verdict", Json.str verdict)
    , ("counts", total.json)
    , ("families", Json.mkObj families)
    , ("counterexample", counterexample.getD Json.null)
    , ("first_error", match firstError with | some m => Json.str m | none => Json.null)
    , ("coverage", coverageJson subject (sortNats seen.toList))
    , ("max_steps", toJson maxSteps)
    , ("wall_clock_ms", toJson elapsed)
    , ("config", configJson o shape source truncated) ]
  let code : UInt32 := match verdict with
    | "fail" => 1
    | "error" => 2
    | _ => 0
  emit json code

/-- Run the original and a candidate on the same inputs and report whether any
observable outcome differs. -/
def diffAll {ι : Type} [Domain ι] (p : Problem ι) (shape : Shape) (o : Options)
    (candidate : Module) (source : String) : IO UInt32 := do
  let started ← IO.monoMsNow
  let cfg : GenConfig := { exhaustiveTo := o.exhaustiveTo, maxLen := o.maxLen, fixedLen := o.fixedLen }
  let constants := dedup (moduleConstants p.module ++ moduleConstants candidate)
  let mut inputs := 0
  let mut differences := 0
  let mut first : Option Json := none
  let mut originalSeen : Std.HashSet Nat := {}
  let mut candidateSeen : Std.HashSet Nat := {}
  let mut truncated := false
  let mut errors := 0
  for fam in o.families do
    for x in inputsOf p o fam cfg constants do
      if let some secs := o.budgetSeconds then
        if (← IO.monoMsNow) - started ≥ secs * 1000 then
          truncated := true
          break
      let reference := observeOn p p.module (originalFuel o) x
      let obs := observeOn p candidate (candidateFuel reference.steps) x
      inputs := inputs + 1
      for f in reference.functions do originalSeen := originalSeen.insert f
      for f in obs.functions do candidateSeen := candidateSeen.insert f
      if let .internalError _ := obs.termination then errors := errors + 1
      if !reference.sameAs obs then
        differences := differences + 1
        if first.isNone then
          first := some (Json.mkObj
            [ ("input", inputJson p x (some fam))
            , ("original", observationJson reference)
            , ("candidate", observationJson obs) ])
        if !o.keepGoing then break
    if truncated || (first.isSome && !o.keepGoing) then break
  let elapsed := (← IO.monoMsNow) - started
  let verdict := if differences > 0 then "different" else if errors > 0 then "error" else "identical"
  let json := Json.mkObj
    [ ("mode", Json.str "diff")
    , ("verdict", Json.str verdict)
    , ("inputs", toJson inputs)
    , ("differences", toJson differences)
    , ("first_difference", first.getD Json.null)
    , ("original_coverage", coverageJson p.module (sortNats originalSeen.toList))
    , ("candidate_coverage", coverageJson candidate (sortNats candidateSeen.toList))
    , ("wall_clock_ms", toJson elapsed)
    , ("config", configJson o shape source truncated) ]
  emit json (if differences > 0 then 1 else if errors > 0 then 2 else 0)

/-- One input given as hex bytes of its encoding. -/
def testOne {ι : Type} [Domain ι] (p : Problem ι) (shape : Shape) (o : Options)
    (candidate : Option Module) (hex : String) : IO UInt32 := do
  match (bytesOfHex? hex).bind p.decode? with
  | none => fail2 s!"`{hex}` is not the encoding of an input in the specification's domain"
  | some x =>
    let (obs, verdict, _) := evaluate p shape o candidate x
    let json := Json.mkObj
      ([ ("mode", Json.str "single")
       , ("verdict", Json.str verdict.name)
       , ("failed_clause", match verdict.detail with | some d => Json.str d | none => Json.null)
       , ("input", inputJson p x none)
       , ("outcome", observationJson obs) ] ++
       (if o.trace then [("functions_entered", toJson obs.functions),
          ("output_hex_full", Json.str (hexOfBytes obs.output))] else []))
    let code : UInt32 := match verdict with
      | .fail _ => 1
      | .error _ => 2
      | _ => 0
    emit json code

/-- Entry point for a problem's `spec_test` executable. -/
def runCli {ι : Type} [Domain ι] (p : Problem ι) (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  match parseOptions args {} with
  | .error message => IO.eprintln usage; fail2 message
  | .ok o =>
    match ← readShape o.configPath with
    | .error message => fail2 message
    | .ok shape =>
      let loadCandidate (path : String) : IO (Except String Module) := loadWat path
      match o.diff with
      | some path =>
        match ← loadCandidate path with
        | .error message => fail2 message
        | .ok m => diffAll p shape o m s!"diff:{path}"
      | none =>
        let candidate ← match o.wat with
          | some path =>
            match ← loadCandidate path with
            | .error message => return (← fail2 message)
            | .ok m => pure (some m)
          | none => pure none
        let source := match o.wat with | some path => s!"wat:{path}" | none => "compiled"
        match o.input with
        | some hex => testOne p shape o candidate hex
        | none => testAll p shape o candidate source

end Wasm.SpecTest
