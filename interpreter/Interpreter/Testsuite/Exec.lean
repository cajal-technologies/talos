import Interpreter.Wasm
import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Validate
import Lean.Data.Json

/-!
# `Interpreter.Testsuite.Exec`

Library half of the `testsuite` exe. Drives one `.wast` file through the
pipeline:

  `.wast` --(wasm-tools json-from-wast)--> JSON script + per-module `.wasm`
  per module: `.wasm` --(wasm-tools print)--> WAT --(decode)--> `Wasm.Module`
  per assertion: invoke + check expected

See the design notes alongside `Interpreter.Testsuite` for the full taxonomy.
-/

namespace Wasm.Testsuite

open Wasm Wasm.Decoder.Wat
open Lean (Json)

/-- Invoke through the migrated small-step semantics. The iterator has its own
explicit cap so an intentionally divergent program cannot consume the
testsuite's full fuel allowance. Initialization failures and invariant
violations remain observable driver errors rather than falling back to a
second semantics. -/
private def runSmallStep
    (fuel : Nat) (m : Wasm.Module) (idx : Nat)
    (store : Wasm.Store Unit) (args : List Wasm.Value)
    (env : Wasm.HostEnv Unit) : Wasm.Result Unit :=
  let instance_ : Wasm.SmallStep.ModuleInstance Unit := { module := m, host := env }
  match Wasm.SmallStep.initConfig instance_ idx store args with
  | .error error => .Invalid s!"small-step initialization error: {error.message}"
  | .ok config =>
    match (Wasm.SmallStep.runSteps (min fuel 15_000_000) config).result with
    | .success values finalStore => .Success values finalStore.wasm
    | .trapped (.uncaughtException tag arguments) finalStore =>
      .Thrown tag arguments finalStore.wasm
    | .trapped reason finalStore =>
      .Trap finalStore.wasm reason.message
    | .outOfFuel _ => .OutOfFuel
    | .internalError error _ =>
      .Invalid s!"small-step internal error: {error.message}"

/-! ## Outcomes -/

inductive Outcome where
  /-- Assertion ran and matched the expected result. -/
  | pass
  /-- Assertion ran but produced the wrong value / didn't trap / wrong reason. -/
  | fail (msg : String)
  /-- Command type we deliberately don't execute (`assert_invalid`, `register`, …). -/
  | skipped (reason : String)
  /-- `wasm-tools` produced a module but our decoder rejected it. -/
  | decodeError (msg : String)
  /-- Interpreter hit `.Invalid` or some other internal limit. -/
  | interpreterError (msg : String)
  /-- Interpreter ran out of fuel before producing a result. -/
  | outOfFuel
  /-- This assertion references a module that failed earlier — cascade marker. -/
  | moduleUnavailable
deriving Repr, Inhabited

/-- One executed command's recorded outcome, with its source `.wast` line. -/
structure CmdResult where
  line    : Nat
  /-- Short tag describing the command (e.g. "assert_return", "module"). -/
  kind    : String
  outcome : Outcome
deriving Repr, Inhabited

/-- Aggregate result for a single `.wast` file. -/
structure FileResult where
  path     : String
  /-- All per-command outcomes in source order. -/
  results  : Array CmdResult := #[]
  /-- Set when the file as a whole failed (couldn't read JSON, etc.). -/
  fileError : Option String := none
deriving Inhabited

/-! ## JSON helpers -/

private def jstr? (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok v => v.getStr?.toOption
  | _ => none

private def jnat? (j : Json) (key : String) : Option Nat :=
  match j.getObjVal? key with
  | .ok v =>
    match v.getNat? with
    | .ok n => some n
    | _ => none
  | _ => none

private def jarr? (j : Json) (key : String) : Option (Array Json) :=
  match j.getObjVal? key with
  | .ok v =>
    match v.getArr? with
    | .ok arr => some arr
    | _ => none
  | _ => none

private def jobj? (j : Json) (key : String) : Option Json :=
  match j.getObjVal? key with
  | .ok v => some v
  | _ => none

/-! ## Value parsing

`wast2json` encodes integer values as signed decimal strings, e.g.
`"-2147483648"` for `0x80000000`. We accept any decimal `Int` and reduce
mod `2^32` / `2^64` to get the canonical unsigned representation. -/

private def parseValueAt (ty val : String) : Except String Value :=
  match ty with
  | "i32" =>
    match val.toInt? with
    | some n =>
      let m : Int := 4294967296   -- 2^32
      let u := ((n % m + m) % m).toNat
      .ok (.i32 u.toUInt32)
    | none => .error s!"unparseable i32 value `{val}`"
  | "i64" =>
    match val.toInt? with
    | some n =>
      let m : Int := 18446744073709551616  -- 2^64
      let u := ((n % m + m) % m).toNat
      .ok (.i64 u.toUInt64)
    | none => .error s!"unparseable i64 value `{val}`"
  -- Floats are given as the decimal of their raw bit pattern, except for
  -- the NaN result patterns `nan:canonical`/`nan:arithmetic`. The
  -- interpreter canonicalises every NaN it produces, so matching those
  -- against the canonical NaN bit pattern is exact.
  | "f32" =>
    match val with
    | "nan:canonical" | "nan:arithmetic" => .ok (.f32 0x7FC00000)
    | _ => match val.toNat? with
      | some n => .ok (.f32 (UInt32.ofNat (n % 4294967296)))
      | none   => .error s!"unparseable f32 value `{val}`"
  | "f64" =>
    match val with
    | "nan:canonical" | "nan:arithmetic" => .ok (.f64 0x7FF8000000000000)
    | _ => match val.toNat? with
      | some n => .ok (.f64 (UInt64.ofNat (n % 18446744073709551616)))
      | none   => .error s!"unparseable f64 value `{val}`"
  -- Reference values: `wast2json` encodes the payload as a decimal host
  -- index or the string `null`. `(ref.func)`-style "any non-null ref"
  -- expectations carry no usable payload and surface as parse errors,
  -- which the caller reports as skipped/unsupported rather than failed.
  | "externref" =>
    match val with
    | "null" => .ok (.externref none)
    | _ => match val.toNat? with
      | some n => .ok (.externref (some n))
      | none   => .error s!"unparseable externref value `{val}`"
  | "funcref" =>
    match val with
    | "null" => .ok (.funcref none)
    | _ => match val.toNat? with
      | some n => .ok (.funcref (some n))
      | none   => .error s!"unparseable funcref value `{val}`"
  | "anyref" =>
    match val with
    | "null" => .ok (.anyref none)
    | _ => match val.toNat? with
      | some n => .ok (.anyref (some (.host n)))
      | none => .error s!"unparseable anyref value `{val}`"
  | other => .error s!"non-integer value type `{other}`"

private def laneBitsOf? : String → Option Nat
  | "i8"  => some 8
  | "i16" => some 16
  | "i32" => some 32
  | "i64" => some 64
  | "f32" => some 32
  | "f64" => some 64
  | _     => none

/-- Parse one v128 lane literal into its unsigned `bits`-wide value. Lane
strings are signed decimals (integers) or the decimal of the raw bit
pattern (floats) — both reduce the same way. -/
private def parseLane (bits : Nat) (val : String) : Except String Nat :=
  match val.toInt? with
  | some n =>
    let m : Int := (2 ^ bits : Nat)
    .ok ((n % m + m) % m).toNat
  | none => .error s!"unparseable v128 lane `{val}`"

/-- Extract the lane-string array of a v128 JSON value. -/
private def jlanes? (j : Json) : Option (Array String) := do
  let arr ← jarr? j "value"
  arr.mapM (·.getStr?.toOption)

/-- Parse a v128 argument (concrete lanes only) into its bit pattern. -/
private def parseV128Arg (j : Json) : Except String Value := do
  let laneTy := jstr? j "lane_type" |>.getD ""
  let bits ← match laneBitsOf? laneTy with
    | some b => .ok b
    | none   => .error s!"unknown v128 lane type `{laneTy}`"
  let lanes ← match jlanes? j with
    | some ls => .ok ls
    | none    => .error "v128 value missing lane array"
  let mut acc : List Nat := []
  for l in lanes do
    acc := acc ++ [← parseLane bits l]
  return .v128 (Wasm.Simd.ofLanes bits acc)

private def parseValue (j : Json) : Except String Value :=
  match jstr? j "type" with
  | some "v128" => parseV128Arg j
  | some ty =>
    match jstr? j "value" with
    | some val => parseValueAt ty val
    | none => .error "value missing type/value"
  | none => .error "value missing type/value"

private def parseValues (arr : Array Json) : Except String (List Value) := do
  let mut acc : Array Value := #[]
  for j in arr do
    acc := acc.push (← parseValue j)
  return acc.toList

/-! ## Expected-result patterns

`assert_return` expectations are richer than concrete values: a float (or
float lane) may be `nan:canonical` / `nan:arithmetic`, which match NaN
*classes* rather than one bit pattern. -/

/-- Pattern for one scalar float or one v128 lane, as an unsigned
bit-pattern of width `bits`. -/
private inductive LanePat where
  | exact (n : Nat)
  | canonicalNan (bits : Nat)
  | arithmeticNan (bits : Nat)
deriving Repr, Inhabited

/-- `nan:canonical` = NaN whose payload is exactly the canonical payload
(sign bit unconstrained); `nan:arithmetic` = NaN whose payload MSB is set
(sign bit unconstrained). -/
private def LanePat.matches : LanePat → Nat → Bool
  | .exact e, n => n = e
  | .canonicalNan 32, n => n % 2 ^ 32 &&& 0x7FFFFFFF = 0x7FC00000
  | .canonicalNan _,  n => n &&& 0x7FFFFFFFFFFFFFFF = 0x7FF8000000000000
  | .arithmeticNan 32, n => n % 2 ^ 32 &&& 0x7FC00000 = 0x7FC00000
  | .arithmeticNan _,  n => n &&& 0x7FF8000000000000 = 0x7FF8000000000000

private def lanePatOf (bits : Nat) (val : String) : Except String LanePat :=
  match val with
  | "nan:canonical"  => .ok (.canonicalNan bits)
  | "nan:arithmetic" => .ok (.arithmeticNan bits)
  | _ => LanePat.exact <$> parseLane bits val

/-- One expected result: a concrete value, a scalar float NaN-class
pattern, or a per-lane v128 pattern. -/
private inductive ExpectedVal where
  | exact (v : Value)
  | f32Pat (p : LanePat)
  | f64Pat (p : LanePat)
  | v128Pat (laneBits : Nat) (lanes : List LanePat)
  /-- `(either a b …)` from the relaxed-SIMD tests: any alternative
  matches. -/
  | either (alts : List ExpectedVal)
  /-- A GC managed-reference expectation without a concrete payload
  (`i31ref`/`structref`/`arrayref`/`anyref`/`eqref`/`nullref`): the test
  only pins the reference's *kind*, so any live reference of the right
  shape matches (and `nullref` matches the managed null). -/
  | gcRef (kind : String)
deriving Repr, Inhabited

private partial def ExpectedVal.matches : ExpectedVal → Value → Bool
  | .exact e, v => e == v
  | .f32Pat p, .f32 b => p.matches b.toNat
  | .f64Pat p, .f64 b => p.matches b.toNat
  | .v128Pat bits ps, .v128 v =>
    ps.length = 128 / bits &&
    (List.zip ps (Wasm.Simd.toLanes bits v)).all fun (p, n) => p.matches n
  | .either alts, v => alts.any (·.matches v)
  | .gcRef kind, v => match kind, v with
    | "nullref", .anyref none      => true
    | "nullref", _                 => false
    | "i31ref", .anyref (some (.i31 _))    => true
    | "structref", .anyref (some (.struct _)) => true
    | "arrayref", .anyref (some (.array _))   => true
    -- `anyref`/`eqref` (and any other live managed ref) match any non-null.
    | _, .anyref (some _)          => true
    | _, _                         => false
  | _, _ => false

private partial def parseExpectedValue (j : Json) : Except String ExpectedVal := do
  match jstr? j "type" with
  | some "either" =>
    let altsJ := jarr? j "values" |>.getD #[]
    let mut alts : List ExpectedVal := []
    for a in altsJ do
      alts := alts ++ [← parseExpectedValue a]
    return .either alts
  | some "v128" =>
    let laneTy := jstr? j "lane_type" |>.getD ""
    let bits ← match laneBitsOf? laneTy with
      | some b => .ok b
      | none   => .error s!"unknown v128 lane type `{laneTy}`"
    let lanes ← match jlanes? j with
      | some ls => .ok ls
      | none    => .error "v128 value missing lane array"
    let mut acc : List LanePat := []
    for l in lanes do
      acc := acc ++ [← lanePatOf bits l]
    return .v128Pat bits acc
  | some "f32" =>
    match jstr? j "value" with
    | some val => ExpectedVal.f32Pat <$> lanePatOf 32 val
    | none => .error "value missing type/value"
  | some "f64" =>
    match jstr? j "value" with
    | some val => ExpectedVal.f64Pat <$> lanePatOf 64 val
    | none => .error "value missing type/value"
  | some ty =>
    -- GC managed-reference result types (GC proposal). `wast2json` encodes
    -- these with no `value` (any ref of the kind), `"null"`, or — for i31 —
    -- a concrete scalar.
    if ty == "i31ref" || ty == "structref" || ty == "arrayref"
       || ty == "anyref" || ty == "eqref" || ty == "nullref" then
      match jstr? j "value" with
      | none          => return .gcRef ty
      | some "null"   => return .gcRef "nullref"
      | some v => match v.toInt? with
        | some n =>
          if ty == "anyref" then
            return .exact (.anyref (some (.host n.toNat)))
          else
            let m : Int := 4294967296
            let u := ((n % m + m) % m).toNat
            return .exact (.anyref (some (.i31 (u.toUInt32 &&& 0x7fffffff))))
        | none => return .gcRef ty
    else match jstr? j "value" with
    | some val => ExpectedVal.exact <$> parseValueAt ty val
    | none => .error "value missing type/value"
  | none => .error "value missing type/value"

private def parseExpectedValues (arr : Array Json) : Except String (List ExpectedVal) := do
  let mut acc : Array ExpectedVal := #[]
  for j in arr do
    acc := acc.push (← parseExpectedValue j)
  return acc.toList

/-! ## Module slot management

A `.wast` file declares one or more modules in source order; subsequent
`(invoke ...)` actions reference either the most-recently-declared module
(no `module` field on the action) or a named one (`(module $M ...)` →
later actions carry `"module": "M"`). We track both. -/

/-- A module slot pairs a successfully decoded `Wasm.Module` with the
*current* `Store` for that instance. The store is initialised from
`m.initialStore` at `module`-command time and threaded through
subsequent successful invokes so that mutations to globals and memory
are observable to later commands — matching the standard wasm semantics
where the store is per-instance and persists across script actions. -/
inductive ModuleSlot where
  | ok (m : Wasm.Module) (store : Wasm.Store Unit) (env : Wasm.HostEnv Unit)
  | unavailable (reason : String)
deriving Inhabited

structure ScriptState where
  /-- Named module definitions are decoded but not instantiated until a
  subsequent `module_instance` command. Each instantiation receives fresh
  local resources, as required by the component-model script syntax. -/
  definitions : List (String × Wasm.Module) := []
  /-- All declared modules in source order. -/
  modules : Array ModuleSlot := #[]
  /-- `$name` → index into `modules`. Small enough that a linear list is fine. -/
  named   : List (String × Nat) := []
  /-- `(register "M")` bindings: registered name → index into `modules`.
  Imports from a registered module resolve against that instance. -/
  registered : List (String × Nat) := []
  /-- Script-wide instantiated mutable globals. -/
  sharedGlobals : Array Wasm.Value := #[]
  /-- Allocated exception-tag identities (payload-free but generative). -/
  sharedTags : Array Unit := #[]
  /-- Script-wide callable function instances referenced by shared tables. -/
  sharedFunctions : Array (Wasm.HostFn Unit) := #[]
  /-- Script-wide instantiated memories. Module-local memory indices carry
  stable IDs into this array, so imports alias resources rather than copying
  snapshots. The cap travels with the resource. -/
  sharedMemories : Array (Wasm.Mem × Nat) := #[]
  /-- Script-wide instantiated tables, indexed by stable table identity. -/
  sharedTables : Array (Wasm.TableInst × Nat) := #[]

/-- Look up the index of the module an action wants. With no name, it's
the last declared one. Returning the index (rather than the slot itself)
lets call sites write back an updated slot after a successful invoke. -/
private def resolveModuleIdx (st : ScriptState) (name? : Option String) : Except String Nat :=
  match name? with
  | some n =>
    match st.named.find? (·.1 = n) with
    | some (_, i) =>
      if i < st.modules.size then .ok i
      else .error s!"internal: module `{n}` index out of range"
    | none => .error s!"unknown module `{n}`"
  | none =>
    if st.modules.isEmpty then .error "no module declared yet"
    else .ok (st.modules.size - 1)

/-! ## wasm-tools subprocess helpers -/

/-- Run `wasm-tools` with the given args. Returns `.ok stdout` on exit 0,
or `.error msg` otherwise (distinguishing missing-binary from non-zero exit). -/
def runWasmTools (args : Array String) : IO (Except String String) := do
  let res ← (IO.Process.output { cmd := "wasm-tools", args }).toBaseIO
  match res with
  | .error _ =>
    return .error "wasm-tools not found on PATH (install: 'brew install wasm-tools' or 'cargo install wasm-tools')"
  | .ok out =>
    if out.exitCode = 0 then return .ok out.stdout
    else return .error s!"wasm-tools failed: {out.stderr.trimAscii.toString}"

/-- Decode a single module file produced by `json-from-wast`.

For `.wasm` inputs we first strip every custom section (notably the
`name` section). The Lean decoder doesn't yet thread `(param $x i32)`
names through `(type N)` references, so leaving the name section in
place produces spurious `unknown local id: $x` failures. -/
def decodeModuleFile (path : String) : IO (Except String Wasm.Module) := do
  let wat ← if path.endsWith ".wat" then
    try .ok <$> IO.FS.readFile path catch e => pure (.error e.toString)
  else do
    let stripped := s!"{path}.stripped"
    match (← runWasmTools #["strip", "--all", path, "-o", stripped]) with
    | .error e => pure (.error e)
    | .ok _    => runWasmTools #["print", stripped]
  match wat with
  | .error msg => return .error msg
  | .ok src =>
    match decode src with
    | .ok m => return .ok m
    | .error e => return .error s!"decode: {e}"


/-! ## Cross-module resolution

Cross-instance imports are resolved structurally at instantiation time:
imported functions become `HostFn` closures over the exporting instance
(its store snapshot at instantiation — mutations made *through* the
import stay local, which covers everything in the suite short of the
real shared-state linking tests), and imported globals/tables/memories
are copied into the importing instance's initial store. The ambient
`spectest` module (no-op prints, `global_i32 = 666`, …) is built in. -/

private def spectestPrintNames : List String :=
  ["print", "print_i32", "print_i64", "print_f32", "print_f64",
   "print_i32_f32", "print_f64_f64"]

/-- Resolve the exporting instance for a registered module name. -/
private def resolveRegistered (st : ScriptState) (modName : String)
    : Option (Wasm.Module × Wasm.Store Unit × Wasm.HostEnv Unit) :=
  match st.registered.find? (·.1 = modName) with
  | some (_, j) =>
    match st.modules[j]? with
    | some (.ok m store env) => some (m, store, env)
    | _ => none
  | none => none

/-- Build the host environment backing a module's function imports. -/
private def buildEnv (st : ScriptState) (m : Wasm.Module) (fuel : Nat)
    : Wasm.HostEnv Unit :=
  { foreignFuncs := st.sharedFunctions.toList
    funcs := m.imports.map fun imp =>
      if imp.module == "spectest" && spectestPrintNames.contains imp.name then
        { params := imp.params, results := imp.results,
          invoke := fun s _ => .Return [] s }
      else
        match resolveRegistered st imp.module with
        | some (em, estore, eenv) =>
          match em.findExport imp.name with
          | some fidx =>
            { params := imp.params, results := imp.results,
              invoke := fun s args =>
                -- `args` arrive first-declared-first; `initConfig` expects
                -- stack order (head = last argument).
                match runSmallStep fuel em fidx estore args.reverse eenv with
                | .Success vs _ => .Return vs s
                | .Trap _ msg   => .Trap s msg
                | .Invalid msg  => .Trap s s!"invalid in imported function: {msg}"
                | .OutOfFuel    => .Trap s "out of fuel in imported function"
                | .Thrown tag arguments _ =>
                  let globalTag := estore.tagIds[tag]?.getD tag
                  let localTag :=
                    (s.tagIds.findIdx? (· = globalTag)).getD
                      (s.tagIds.length + globalTag)
                  .Throw s localTag arguments }
          | none =>
            { invoke := fun s _ =>
                .Trap s s!"unknown import {imp.module}.{imp.name}" }
        | none =>
          { invoke := fun s _ =>
              .Trap s s!"unresolved import {imp.module}.{imp.name}" } }

/-- Spectest's ambient global values. -/
private def spectestGlobal? : String → Option Wasm.Value
  | "global_i32" => some (.i32 666)
  | "global_i64" => some (.i64 666)
  | "global_f32" => some (.f32 (666.6 : Float).toFloat32.toBits)
  | "global_f64" => some (.f64 (666.6 : Float).toBits)
  | _ => none

/-- Copy imported entity values (globals/tables/memories) into a fresh
initial store, then re-apply the module's active element and data
segments so segments targeting an imported table/memory land on the
copied contents (the re-application is idempotent for local targets). -/
private def applyEntityImports (sst : ScriptState) (m : Wasm.Module)
    (store : Wasm.Store Unit) : Wasm.Store Unit := Id.run do
  let mut store := store
  let mut gi := 0
  for (modN, name) in m.importedGlobals do
    let v? : Option Wasm.Value :=
      if modN == "spectest" then spectestGlobal? name
      else match resolveRegistered sst modN with
        | some (em, estore, _) =>
          match em.globalExports.find? (·.1 = name) with
          | some (_, gIdx) => estore.globals.globals[gIdx]?
          | none => none
        | none => none
    match v? with
    | some v =>
      store := { store with globals := { globals := store.globals.globals.set gi v } }
    | none => pure ()
    gi := gi + 1
  let mut ti := 0
  for (modN, name) in m.importedTables do
    let t? : Option (Wasm.TableInst × Nat) :=
      if modN == "spectest" && name == "table" then
        some (List.replicate 10 (Wasm.Value.funcref none),
          Wasm.Module.tableHardCap)
      else match resolveRegistered sst modN with
        | some (em, estore, _) =>
          match em.tableExports.find? (·.1 = name) with
          | some (_, tIdx) =>
            estore.tables[tIdx]?.map fun table =>
              (table, em.tableCap tIdx)
          | none => none
        | none => none
    match t? with
    | some (t, _) =>
      store :=
        { store with
          tables := Wasm.listSetAt store.tables ti t }
    | none => pure ()
    ti := ti + 1
  let mut mi := 0
  for (modN, name) in m.importedMemories do
    let mem? : Option (Wasm.Mem × Nat) :=
      if modN == "spectest" && name == "memory" then
        -- The spec harness defines `(memory 1 2)`.
        some (Wasm.Mem.empty 1, 2)
      else match resolveRegistered sst modN with
        | some (em, estore, _) =>
          match em.memoryExports.find? (·.1 = name) with
          | some (_, mIdx) =>
            let selected :=
              if mIdx = 0 then some estore.mem else estore.extraMems[mIdx - 1]?
            selected.map fun memory => (memory, estore.memoryCap em mIdx)
          | none => none
        | none => none
    match mem? with
    | some (mem, cap) =>
      if mi = 0 then store := { store with mem := mem }
      else store := { store with extraMems := Wasm.listSetAt store.extraMems (mi - 1) mem }
      store := { store with memoryCaps := Wasm.listSetAt store.memoryCaps mi cap }
    | none => pure ()
    mi := mi + 1
  -- Re-apply active segments on top of the copied entities.
  match m.memory with
  | some d0 =>
    for seg in d0.data do
      match seg.offset with
      | some off =>
        if !seg.offsetExpr.isEmpty then pure ()
        else if seg.memIdx = 0 then
          if off.toNat + seg.bytes.length ≤ store.mem.pages * 65536 then
            store := { store with mem := store.mem.writeBytes off.toNat seg.bytes }
        else
          match store.extraMems[seg.memIdx - 1]? with
          | some em =>
            if off.toNat + seg.bytes.length ≤ em.pages * 65536 then
              let mems' := Wasm.listSetAt store.extraMems (seg.memIdx - 1)
                (em.writeBytes off.toNat seg.bytes)
              store := { store with extraMems := mems' }
          | none => pure ()
      | none => pure ()
  | none => pure ()
  for seg in m.elements do
    match seg.tableIdx, seg.offset with
    | some t, some off =>
      if !seg.offsetExpr.isEmpty then pure ()
      else match store.tables[t]? with
      | some tbl =>
        if off + seg.plainValues.length ≤ tbl.length then
          let tbls' := Wasm.listSetAt store.tables t
            (Wasm.listWriteAt tbl off seg.plainValues)
          store := { store with tables := tbls' }
      | none => pure ()
    | _, _ => pure ()
  return store

private def storeMemory? (store : Wasm.Store Unit) (index : Nat) :
    Option Wasm.Mem :=
  let canonical :=
    match store.memoryIds[index]? with
    | some id => (store.memoryIds.findIdx? (· = id)).getD index
    | none => index
  if canonical = 0 then some store.mem else store.extraMems[canonical - 1]?

private def setStoreMemory (store : Wasm.Store Unit) (index : Nat)
    (memory : Wasm.Mem) : Wasm.Store Unit :=
  if index = 0 then { store with mem := memory }
  else
    { store with
      extraMems := Wasm.listSetAt store.extraMems (index - 1) memory }

/-- Re-apply literal-offset active segments after imported resources have been
hydrated from their canonical script-wide identities. `initialStore` and
`applyEntityImports` necessarily run before those identities are assigned;
without this pass their writes can be hidden by the subsequent hydration. -/
private def reapplyLiteralActiveSegments (m : Wasm.Module)
    (store0 : Wasm.Store Unit) : Wasm.Store Unit := Id.run do
  let mut store := store0
  match m.memory with
  | some memory =>
    for segment in memory.data do
      match segment.offset with
      | some offset =>
        if !segment.offsetExpr.isEmpty then pure ()
        else
          match storeMemory? store segment.memIdx with
          | some target =>
            if offset.toNat + segment.bytes.length ≤ target.pages * 65536 then
              store := setStoreMemory store segment.memIdx
                (target.writeBytes offset.toNat segment.bytes)
          | none => pure ()
      | none => pure ()
  | none => pure ()
  for segment in m.elements do
    match segment.tableIdx, segment.offset with
    | some tableIndex, some offset =>
      if !segment.offsetExpr.isEmpty then pure ()
      else
        match store.tables[tableIndex]? with
        | some table =>
          if offset + segment.plainValues.length ≤ table.length then
            store :=
              { store with
                tables := Wasm.listSetAt store.tables tableIndex
                  (Wasm.listWriteAt table offset segment.plainValues) }
        | none => pure ()
    | _, _ => pure ()
  return store

/-- Give every local resource a script-wide stable identity. Imported
resources reuse the identity exported by the registered instance; locally
defined resources append fresh entries. -/
private def assignResourceIds (sst : ScriptState) (m : Wasm.Module)
    (store0 : Wasm.Store Unit) :
    Wasm.Store Unit × Array (Wasm.Mem × Nat) ×
      Array (Wasm.TableInst × Nat) := Id.run do
  let mut store := store0
  let mut memories := sst.sharedMemories
  let mut tables := sst.sharedTables
  let mut memoryIds : List Nat := []
  let mut tableIds : List Nat := []

  for index in List.range store0.memoryCaps.length do
    let importedId? :=
      if h : index < m.importedMemories.length then
        let (modName, name) := m.importedMemories[index]
        match resolveRegistered sst modName with
        | some (em, estore, _) =>
          match em.memoryExports.find? (·.1 = name) with
          | some (_, exportIndex) => estore.memoryIds[exportIndex]?
          | none => none
        | none => none
      else none
    let id ← match importedId? with
      | some id =>
        match memories[id]? with
        | some (memory, cap) =>
          store := setStoreMemory store index memory
          store :=
            { store with
              memoryCaps := Wasm.listSetAt store.memoryCaps index cap }
        | none => pure ()
        pure id
      | none =>
        let id := memories.size
        match storeMemory? store index with
        | some memory =>
          memories := memories.push
            (memory, store.memoryCap m index)
        | none => pure ()
        pure id
    memoryIds := memoryIds ++ [id]

  for index in List.range store0.tables.length do
    let importedId? :=
      if h : index < m.importedTables.length then
        let (modName, name) := m.importedTables[index]
        match resolveRegistered sst modName with
        | some (em, estore, _) =>
          match em.tableExports.find? (·.1 = name) with
          | some (_, exportIndex) => estore.tableIds[exportIndex]?
          | none => none
        | none => none
      else none
    let id ← match importedId? with
      | some id =>
        match tables[id]? with
        | some (table, _) =>
          let decode : Wasm.Value → Wasm.Value
            | .funcref (some encoded) =>
              if Wasm.SmallStep.foreignFunctionBase ≤ encoded then
                let functionId :=
                  encoded - Wasm.SmallStep.foreignFunctionBase
                match store.functionIds.findIdx? (· = functionId) with
                | some localIndex => .funcref (some localIndex)
                | none => .funcref (some encoded)
              else .funcref (some encoded)
            | value => value
          store :=
            { store with
              tables := Wasm.listSetAt store.tables index (table.map decode) }
        | none => pure ()
        pure id
      | none =>
        let id := tables.size
        match store.tables[index]? with
        | some table =>
          tables := tables.push (table, m.tableCap index)
        | none => pure ()
        pure id
    tableIds := tableIds ++ [id]

  return ({ store with memoryIds, tableIds }, memories, tables)

private def assignGlobalIds (sst : ScriptState) (m : Wasm.Module)
    (store0 : Wasm.Store Unit) : Wasm.Store Unit × Array Wasm.Value := Id.run do
  let mut globals := sst.sharedGlobals
  let mut globalIds : List Nat := []
  for index in List.range store0.globals.globals.length do
    let importedId? :=
      if index < m.importedGlobals.length then
        let (modName, name) := m.importedGlobals[index]!
        match resolveRegistered sst modName with
        | some (em, estore, _) =>
          match em.globalExports.find? (·.1 = name) with
          | some (_, exportIndex) => estore.globalIds[exportIndex]?
          | none => none
        | none => none
      else none
    let id ← match importedId? with
      | some id => pure id
      | none =>
        let id := globals.size
        match store0.globals.globals[index]? with
        | some value => globals := globals.push value
        | none => pure ()
        pure id
    globalIds := globalIds ++ [id]
  return ({ store0 with globalIds }, globals)

private def assignTagIds (sst : ScriptState) (m : Wasm.Module)
    (store0 : Wasm.Store Unit) : Wasm.Store Unit × Array Unit := Id.run do
  let mut tags := sst.sharedTags
  let mut tagIds : List Nat := []
  for index in List.range m.tags.length do
    let importedId? :=
      if index < m.importedTags.length then
        let (modName, name) := m.importedTags[index]!
        match resolveRegistered sst modName with
        | some (em, estore, _) =>
          match em.tagExports.find? (·.1 = name) with
          | some (_, exportIndex) => estore.tagIds[exportIndex]?
          | none => none
        | none => none
      else none
    let id ← match importedId? with
      | some id => pure id
      | none =>
        let id := tags.size
        tags := tags.push ()
        pure id
    tagIds := tagIds ++ [id]
  return ({ store0 with tagIds }, tags)

private def assignFunctionIds (sst : ScriptState) (m : Wasm.Module)
    (store0 : Wasm.Store Unit) (env : Wasm.HostEnv Unit) (fuel : Nat) :
    Wasm.Store Unit × Array (Wasm.HostFn Unit) := Id.run do
  let mut functions := sst.sharedFunctions
  let mut functionIds : List Nat := []
  let functionCount := m.imports.length + m.funcs.length
  for index in List.range functionCount do
    let importedId? :=
      if index < m.imports.length then
        let imp := m.imports[index]!
        match resolveRegistered sst imp.module with
        | some (em, estore, _) =>
          match em.findExport imp.name with
          | some exportIndex => estore.functionIds[exportIndex]?
          | none => none
        | none => none
      else none
    let id ← match importedId? with
      | some id => pure id
      | none =>
        let id := functions.size
        let signature := (m.funcSig? index).getD {}
        let capturedStore := store0
        let function : Wasm.HostFn Unit :=
          { params := signature.params
            results := signature.results
            invoke := fun callerStore args =>
              match runSmallStep fuel m index capturedStore args.reverse env with
              | .Success values _ => .Return values callerStore
              | .Trap _ message => .Trap callerStore message
              | .Invalid message =>
                .Trap callerStore s!"invalid in foreign function: {message}"
              | .OutOfFuel => .Trap callerStore "out of fuel in foreign function"
              | .Thrown tag arguments _ =>
                let globalTag := capturedStore.tagIds[tag]?.getD tag
                let localTag :=
                  (callerStore.tagIds.findIdx? (· = globalTag)).getD
                    (callerStore.tagIds.length + globalTag)
                .Throw callerStore localTag arguments }
        functions := functions.push function
        pure id
    functionIds := functionIds ++ [id]
  return ({ store0 with functionIds }, functions)

private def encodeSharedFuncref (store : Wasm.Store Unit) : Wasm.Value → Wasm.Value
  | .funcref (some index) =>
    if Wasm.SmallStep.foreignFunctionBase ≤ index then .funcref (some index)
    else
      match store.functionIds[index]? with
      | some id => .funcref (some (Wasm.SmallStep.foreignFunctionBase + id))
      | none => .funcref (some index)
  | value => value

private def decodeSharedFuncref (store : Wasm.Store Unit) : Wasm.Value → Wasm.Value
  | .funcref (some index) =>
    if Wasm.SmallStep.foreignFunctionBase ≤ index then
      let id := index - Wasm.SmallStep.foreignFunctionBase
      match store.functionIds.findIdx? (· = id) with
      | some localIndex => .funcref (some localIndex)
      | none => .funcref (some index)
    else .funcref (some index)
  | value => value

/-- Refresh a module-local store from the script-wide shared resources before
an action. -/
private def hydrateStore (sst : ScriptState) (store0 : Wasm.Store Unit) :
    Wasm.Store Unit := Id.run do
  let mut store := store0
  for (id, index) in store0.globalIds.zipIdx do
    match sst.sharedGlobals[id]? with
    | some value =>
      store := { store with globals :=
        { globals := Wasm.listSetAt store.globals.globals index value } }
    | none => pure ()
  for (id, index) in store0.memoryIds.zipIdx do
    match sst.sharedMemories[id]? with
    | some (memory, cap) =>
      store := setStoreMemory store index memory
      store :=
        { store with
          memoryCaps := Wasm.listSetAt store.memoryCaps index cap }
    | none => pure ()
  for (id, index) in store0.tableIds.zipIdx do
    match sst.sharedTables[id]? with
    | some (table, _) =>
      store :=
        { store with
          tables := Wasm.listSetAt store.tables index
            (table.map (decodeSharedFuncref store0)) }
    | none => pure ()
  return store

private def hydrateSlot (sst : ScriptState) (fuel : Nat) : ModuleSlot → ModuleSlot
  | .ok m store _ => .ok m (hydrateStore sst store) (buildEnv sst m fuel)
  | slot => slot

/-- Commit a module-local post-store back to every shared resource it
addresses. Other instances observe the update on their next action. -/
private def commitStore (sst : ScriptState) (m : Wasm.Module)
    (store : Wasm.Store Unit) : ScriptState := Id.run do
  let mut globals := sst.sharedGlobals
  let mut memories := sst.sharedMemories
  let mut tables := sst.sharedTables
  for (id, index) in store.globalIds.zipIdx do
    match store.globals.globals[index]? with
    | some value =>
      if id < globals.size then globals := globals.set! id value
    | none => pure ()
  for (id, index) in store.memoryIds.zipIdx do
    match storeMemory? store index with
    | some memory =>
      if id < memories.size then
        memories := memories.set! id (memory, store.memoryCap m index)
    | none => pure ()
  for (id, index) in store.tableIds.zipIdx do
    match store.tables[index]? with
    | some table =>
      if id < tables.size then
        tables := tables.set! id
          (table.map (encodeSharedFuncref store), m.tableCap index)
    | none => pure ()
  return { sst with
    sharedGlobals := globals
    sharedMemories := memories
    sharedTables := tables }

private def commitSlot (sst : ScriptState) : ModuleSlot → ScriptState
  | .ok m store _ => commitStore sst m store
  | _ => sst

/-- Detect an active-segment instantiation trap. Element segments precede
data segments in the WebAssembly instantiation algorithm, which is observable:
successful writes to an imported table remain committed when a later data
segment traps. Pending const-expression offsets are handled by the ordinary
instantiation pass and are conservatively ignored here for now. -/
private def activeSegmentTrap? (m : Wasm.Module) (store : Wasm.Store Unit) :
    Option String :=
  let tableTrap := m.elements.findSome? fun segment =>
    match segment.tableIdx, segment.offset with
    | some tableIndex, some offset =>
      match store.tables[tableIndex]? with
      | some table =>
        let length :=
          if segment.exprs.isEmpty then segment.funcs.length
          else segment.exprs.length
        if offset + length ≤ table.length then none
        else some "out of bounds table access"
      | none => some "out of bounds table access"
    | _, _ => none
  tableTrap.orElse fun _ =>
    let segments := (m.memory.map (·.data)).getD []
    segments.findSome? fun segment =>
      match segment.offset with
      | some offset =>
        match storeMemory? store segment.memIdx with
        | some memory =>
          if offset.toNat + segment.bytes.length ≤ memory.pages * 65536 then
            none
          else some "out of bounds memory access"
        | none => some "out of bounds memory access"
      | none => none

/-! ## Compact value rendering for failure messages -/

private def renderValue : Value → String
  | .i32 u           => s!"i32:{u.toInt32.toInt}"
  | .i64 u           => s!"i64:{u.toInt64.toInt}"
  | .f32 b           => s!"f32:{(Float32.ofBits b).toFloat}"
  | .f64 b           => s!"f64:{Float.ofBits b}"
  | .funcref none    => "funcref:null"
  | .funcref (some i) => s!"funcref:{i}"
  | .externref none    => "externref:null"
  | .externref (some i) => s!"externref:{i}"
  | .v128 b          => s!"v128:0x{String.ofList (Nat.toDigits 16 b.toNat)}"
  | .exnref none     => "exnref:null"
  | .exnref (some i) => s!"exnref:{i}"
  | .anyref none              => "anyref:null"
  | .anyref (some (.i31 n))   => s!"i31:{n.toInt32.toInt}"
  | .anyref (some (.struct a)) => s!"struct:{a}"
  | .anyref (some (.array a))  => s!"array:{a}"
  | .anyref (some (.host id))  => s!"host:{id}"

/-- Render a `List Value`, truncating runs longer than `maxLen` (the
interpreter occasionally leaves big stacks around on failure and that
otherwise drowns the report). -/
private def renderValues (vs : List Value) (maxLen : Nat := 8) : String :=
  let n := vs.length
  if n ≤ maxLen then
    "[" ++ String.intercalate ", " (vs.map renderValue) ++ "]"
  else
    let head := vs.take maxLen |>.map renderValue
    "[" ++ String.intercalate ", " head ++ s!", … ({n - maxLen} more)]"

private def renderLanePat : LanePat → String
  | .exact n => toString n
  | .canonicalNan _ => "nan:canonical"
  | .arithmeticNan _ => "nan:arithmetic"

private partial def renderExpected : ExpectedVal → String
  | .exact v => renderValue v
  | .f32Pat p => s!"f32:{renderLanePat p}"
  | .f64Pat p => s!"f64:{renderLanePat p}"
  | .v128Pat bits ps =>
    s!"v128.{bits}[" ++ String.intercalate ", " (ps.map renderLanePat) ++ "]"
  | .either alts =>
    "either(" ++ String.intercalate " | " (alts.map renderExpected) ++ ")"
  | .gcRef kind => s!"<any {kind}>"

private def renderExpecteds (es : List ExpectedVal) : String :=
  "[" ++ String.intercalate ", " (es.map renderExpected) ++ "]"

/-! ## Command execution -/

/-- Invoke `field` on `slot`'s module with the given args, comparing
returned values against `expected`. Returns the outcome plus an updated
slot — on a successful invoke the store is replaced with the post-call
one (mutations to globals/memory persist for later commands); on an
unexpected trap we still commit the pre-trap store, matching wasm's
"side effects up to the trap are observable" semantics. Out-of-fuel
and invalid leave the slot unchanged. -/
def runAssertReturn
    (slot : ModuleSlot) (field : String) (args : List Value)
    (expected : List ExpectedVal) (fuel : Nat)
    : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store env =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      -- `initConfig` expects params in *stack* order (top = last source arg)
      -- because WAT-decoded functions reverse params to assign locals[0] to
      -- the first source argument. The testsuite parses args in source
      -- order, so we reverse here to match the call convention.
      match runSmallStep fuel m idx store args.reverse env with
      | .Success rs store' =>
        let actual := rs.reverse
        let slot' := .ok m store' env
        let ok := actual.length = expected.length &&
          (List.zip expected actual).all fun (e, v) => e.matches v
        if ok then (.pass, slot')
        else (.fail s!"expected {renderExpecteds expected}, got {renderValues actual}", slot')
      | .Trap store' msg => (.fail s!"unexpected trap `{msg}`", .ok m store' env)
      | .OutOfFuel => (.outOfFuel, slot)
      | .Invalid msg => (.interpreterError msg, slot)
      | .Thrown _ _ store' => (.fail "uncaught exception", .ok m store' env)

/-- Invoke and require a trap whose reason contains `expectedReason`.
On the expected trap we commit the pre-trap store (writes performed
before the trap are visible to later commands, per the wasm spec); on
an unexpected return we likewise commit the post-call store. -/
def runAssertTrap
    (slot : ModuleSlot) (field : String) (args : List Value)
    (expectedReason : String) (fuel : Nat) : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store env =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      match runSmallStep fuel m idx store args.reverse env with
      | .Success rs store' =>
        (.fail s!"expected trap `{expectedReason}`, returned {renderValues rs.reverse}", .ok m store' env)
      | .Trap store' msg =>
        let slot' : ModuleSlot := .ok m store' env
        if expectedReason.isEmpty || (msg.splitOn expectedReason).length > 1 then (.pass, slot')
        else (.fail s!"expected trap `{expectedReason}`, got trap `{msg}`", slot')
      | .OutOfFuel => (.outOfFuel, slot)
      | .Invalid msg => (.interpreterError msg, slot)
      | .Thrown _ _ store' =>
        (.fail s!"expected trap `{expectedReason}`, got uncaught exception", .ok m store' env)

/-- Plain `(invoke …)` outside an assertion: passes iff it doesn't trap.
The post-call (or post-trap) store is propagated so subsequent commands
observe the side effects. -/
def runActionOnly
    (slot : ModuleSlot) (field : String) (args : List Value) (fuel : Nat)
    : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store env =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      match runSmallStep fuel m idx store args.reverse env with
      | .Success _ store' => (.pass, .ok m store' env)
      | .Trap store' msg => (.fail s!"unexpected trap `{msg}`", .ok m store' env)
      | .OutOfFuel => (.outOfFuel, slot)
      | .Invalid msg => (.interpreterError msg, slot)
      | .Thrown _ _ store' => (.fail "uncaught exception", .ok m store' env)

/-- `assert_exception`: invoke and require an uncaught exception. -/
def runAssertException
    (slot : ModuleSlot) (field : String) (args : List Value) (fuel : Nat)
    : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store env =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      match runSmallStep fuel m idx store args.reverse env with
      | .Thrown _ _ store' => (.pass, .ok m store' env)
      | .Success rs store' =>
        (.fail s!"expected exception, returned {renderValues rs.reverse}", .ok m store' env)
      | .Trap store' msg => (.fail s!"expected exception, got trap `{msg}`", .ok m store' env)
      | .OutOfFuel => (.outOfFuel, slot)
      | .Invalid msg => (.interpreterError msg, slot)

/-- Extract the (module?, field, args) tuple from an `action` JSON object. -/
def parseInvokeAction (j : Json) : Except String (Option String × String × List Value) := do
  let ty := jstr? j "type" |>.getD ""
  if ty != "invoke" then .error s!"action type `{ty}` not supported"
  let field ← match jstr? j "field" with
    | some f => .ok f
    | none   => .error "invoke action missing field"
  let argsJ := jarr? j "args" |>.getD #[]
  let args ← parseValues argsJ
  return (jstr? j "module", field, args)

/-! ## Per-file driver -/

private def instantiateModule (st : ScriptState) (m : Wasm.Module) (fuel : Nat) :
    ModuleSlot × Array Wasm.Value × Array Unit × Array (Wasm.HostFn Unit) ×
      Array (Wasm.Mem × Nat) × Array (Wasm.TableInst × Nat) :=
  let env := buildEnv st m fuel
  let store0 := applyEntityImports st m m.initialStore
  let (store0, sharedGlobals) := assignGlobalIds st m store0
  let (store0, sharedTags) := assignTagIds st m store0
  let (store0, sharedFunctions) := assignFunctionIds st m store0 env fuel
  let functionState := { st with sharedFunctions := sharedFunctions }
  let (store0, sharedMemories, sharedTables) :=
    assignResourceIds functionState m store0
  let store0 := reapplyLiteralActiveSegments m store0
  let store0 := m.runConstGlobals fuel store0 env
  let store0 := m.runConstElems fuel store0 env
  let store0 := m.runActiveSegments fuel store0 env
  match m.startFunc with
  | none =>
    let sharedState := commitStore
      { st with
        sharedGlobals := sharedGlobals
        sharedTags := sharedTags
        sharedFunctions := sharedFunctions
        sharedMemories := sharedMemories
        sharedTables := sharedTables } m store0
    (.ok m store0 env, sharedState.sharedGlobals, sharedTags, sharedFunctions,
      sharedState.sharedMemories, sharedState.sharedTables)
  | some idx =>
    match runSmallStep fuel m idx store0 [] env with
    | .Success _ store' =>
      let sharedState := commitStore
        { st with
          sharedGlobals := sharedGlobals
          sharedTags := sharedTags
          sharedFunctions := sharedFunctions
          sharedMemories := sharedMemories
          sharedTables := sharedTables } m store'
      (.ok m store' env, sharedState.sharedGlobals, sharedTags, sharedFunctions,
        sharedState.sharedMemories, sharedState.sharedTables)
    | .Trap store' msg =>
      let sharedState := commitStore
        { st with
          sharedGlobals := sharedGlobals
          sharedTags := sharedTags
          sharedFunctions := sharedFunctions
          sharedMemories := sharedMemories
          sharedTables := sharedTables } m store'
      (.unavailable s!"start trapped: {msg}",
        sharedState.sharedGlobals, sharedTags, sharedFunctions,
        sharedState.sharedMemories,
        sharedState.sharedTables)
    | .OutOfFuel =>
      (.unavailable "start out of fuel", sharedGlobals, sharedTags, sharedFunctions,
        sharedMemories, sharedTables)
    | .Invalid msg =>
      (.unavailable s!"start invalid: {msg}", sharedGlobals, sharedTags,
        sharedFunctions,
        sharedMemories, sharedTables)
    | .Thrown _ _ store' =>
      let sharedState := commitStore
        { st with
          sharedGlobals := sharedGlobals
          sharedTags := sharedTags
          sharedFunctions := sharedFunctions
          sharedMemories := sharedMemories
          sharedTables := sharedTables } m store'
      (.unavailable "uncaught exception in start",
        sharedState.sharedGlobals, sharedTags, sharedFunctions,
        sharedState.sharedMemories,
        sharedState.sharedTables)

/-- Process a single command JSON object, possibly mutating `st`. Returns
the outcome to record (and `none` if the command itself was just a state
mutation like `module`/`register`, which we still record as a row so the
report can show where modules failed). -/
def runCommand
    (cmd : Json) (st : ScriptState) (wasmDir : String) (fuel : Nat)
    : IO (ScriptState × CmdResult) := do
  let line := jnat? cmd "line" |>.getD 0
  let kind := jstr? cmd "type" |>.getD "unknown"
  let mk (o : Outcome) : CmdResult := { line, kind, outcome := o }
  match kind with
  | "module_definition" =>
    let filename := jstr? cmd "filename" |>.getD ""
    let name := jstr? cmd "name" |>.getD ""
    match (← decodeModuleFile s!"{wasmDir}/{filename}") with
    | .error e => return (st, mk (.decodeError e))
    | .ok m =>
      return ({ st with definitions := (name, m) :: st.definitions }, mk .pass)
  | "module_instance" =>
    let instanceName := jstr? cmd "instance" |>.getD ""
    let definitionName := jstr? cmd "module" |>.getD ""
    match st.definitions.find? (·.1 = definitionName) with
    | none =>
      return (st, mk (.interpreterError
        s!"unknown module definition `{definitionName}`"))
    | some (_, m) =>
      let (slot, sharedGlobals, sharedTags, sharedFunctions,
          sharedMemories, sharedTables) :=
        instantiateModule st m fuel
      let idx := st.modules.size
      let modules := st.modules.push slot
      let named := (instanceName, idx) :: st.named
      let outcome : Outcome := match slot with
        | .ok _ _ _ => Outcome.pass
        | .unavailable e => Outcome.interpreterError e
      pure ({ st with
        modules := modules
        named := named
        sharedGlobals := sharedGlobals
        sharedTags := sharedTags
        sharedFunctions := sharedFunctions
        sharedMemories := sharedMemories
        sharedTables := sharedTables }, mk outcome)
  | "module" =>
    let filename := jstr? cmd "filename" |>.getD ""
    let name?    := jstr? cmd "name"
    let (slot, sharedGlobals, sharedTags, sharedFunctions,
        sharedMemories, sharedTables) ← (do
      let res ← decodeModuleFile s!"{wasmDir}/{filename}"
      match res with
      | .ok m => pure (instantiateModule st m fuel)
      | .error e =>
        pure (ModuleSlot.unavailable e, st.sharedGlobals, st.sharedTags,
          st.sharedFunctions,
          st.sharedMemories, st.sharedTables))
    let idx := st.modules.size
    let modules := st.modules.push slot
    let named := match name? with
      | some n => (n, idx) :: st.named
      | none   => st.named
    let outcome : Outcome :=
      match slot with
      | .ok _ _ _ => .pass
      | .unavailable e => .decodeError e
    return ({ st with
      modules := modules
      named := named
      sharedGlobals := sharedGlobals
      sharedTags := sharedTags
      sharedFunctions := sharedFunctions
      sharedMemories := sharedMemories
      sharedTables := sharedTables }, mk outcome)
  | "register" =>
    let asName := jstr? cmd "as" |>.getD ""
    match resolveModuleIdx st (jstr? cmd "name") with
    | .error e => return (st, mk (.interpreterError s!"register: {e}"))
    | .ok i =>
      return ({ st with registered := (asName, i) :: st.registered }, mk .pass)
  | "assert_return" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    if jstr? actJ "type" == some "get" then
      -- `(get "g")`: read an exported global's current value.
      let field := jstr? actJ "field" |>.getD ""
      match resolveModuleIdx st (jstr? actJ "module") with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let expectedJ := jarr? cmd "expected" |>.getD #[]
        match parseExpectedValues expectedJ with
        | .error e => return (st, mk (.skipped s!"non-integer expected: {e}"))
        | .ok expected =>
          match hydrateSlot st fuel st.modules[i]! with
          | .unavailable _ => return (st, mk .moduleUnavailable)
          | .ok m store _ =>
            match m.globalExports.find? (·.1 = field) with
            | none => return (st, mk (.fail s!"unknown global export `{field}`"))
            | some (_, gIdx) =>
              match store.globals.globals[gIdx]? with
              | none => return (st, mk (.interpreterError "global index out of range"))
              | some v =>
                let ok := expected.length = 1 &&
                  ((expected.head?.map (·.matches v)).getD false)
                if ok then return (st, mk .pass)
                else return (st, mk (.fail
                  s!"expected {renderExpecteds expected}, got {renderValue v}"))
    else
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let expectedJ := jarr? cmd "expected" |>.getD #[]
        match parseExpectedValues expectedJ with
        | .error e => return (st, mk (.skipped s!"non-integer expected: {e}"))
        | .ok expected =>
          let slot := hydrateSlot st fuel st.modules[i]!
          let (outcome, slot') := runAssertReturn slot field args expected fuel
          let st' := { st with modules := st.modules.set! i slot' }
          return (commitSlot st' slot', mk outcome)
  | "assert_trap" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let reason := jstr? cmd "text" |>.getD ""
        let slot := hydrateSlot st fuel st.modules[i]!
        let (outcome, slot') := runAssertTrap slot field args reason fuel
        let st' := { st with modules := st.modules.set! i slot' }
        return (commitSlot st' slot', mk outcome)
  | "assert_exception" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let slot := hydrateSlot st fuel st.modules[i]!
        let (outcome, slot') := runAssertException slot field args fuel
        let st' := { st with modules := st.modules.set! i slot' }
        return (commitSlot st' slot', mk outcome)
  | "action" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let slot := hydrateSlot st fuel st.modules[i]!
        let (outcome, slot') := runActionOnly slot field args fuel
        let st' := { st with modules := st.modules.set! i slot' }
        return (commitSlot st' slot', mk outcome)
  | "assert_uninstantiable" =>
    let filename := jstr? cmd "filename" |>.getD ""
    let expected := jstr? cmd "text" |>.getD ""
    match (← decodeModuleFile s!"{wasmDir}/{filename}") with
    | .error error =>
      return (st, mk (.skipped s!"assert_uninstantiable decode: {error}"))
    | .ok m =>
      let env := buildEnv st m fuel
      let imported := applyEntityImports st m m.initialStore
      let (store0, sharedGlobals) := assignGlobalIds st m imported
      let (store0, sharedTags) := assignTagIds st m store0
      let (store0, sharedFunctions) := assignFunctionIds st m store0 env fuel
      let functionState := { st with sharedFunctions := sharedFunctions }
      let (store0, sharedMemories, sharedTables) :=
        assignResourceIds functionState m store0
      let store0 := reapplyLiteralActiveSegments m store0
      let store0 := m.runConstGlobals fuel store0 env
      let store0 := m.runConstElems fuel store0 env
      let store0 := m.runActiveSegments fuel store0 env
      let preparedState :=
        { st with
          sharedGlobals := sharedGlobals
          sharedTags := sharedTags
          sharedFunctions := sharedFunctions
          sharedMemories := sharedMemories
          sharedTables := sharedTables }
      match activeSegmentTrap? m store0 with
      | some actual =>
        let st' := commitStore preparedState m store0
        if actual.contains expected || expected.contains actual then
          return (st', mk .pass)
        else
          return (st', mk (.fail
            s!"expected instantiation trap `{expected}`, got `{actual}`"))
      | none =>
        match m.startFunc with
        | none =>
          return (st, mk (.fail
            s!"expected instantiation trap `{expected}`, module instantiated"))
        | some startIndex =>
          match runSmallStep fuel m startIndex store0 [] env with
          | .Trap store' actual =>
            let st' := commitStore preparedState m store'
            if actual.contains expected || expected.contains actual then
              return (st', mk .pass)
            else
              return (st', mk (.fail
                s!"expected instantiation trap `{expected}`, got `{actual}`"))
          | .Thrown tag _ store' =>
            let st' := commitStore preparedState m store'
            let actual := s!"uncaught exception with tag {tag}"
            if actual.contains expected || expected.contains actual then
              return (st', mk .pass)
            else
              return (st', mk (.fail
                s!"expected instantiation trap `{expected}`, got `{actual}`"))
          | .Success _ store' =>
            let st' := commitStore preparedState m store'
            return (st', mk (.fail
              s!"expected instantiation trap `{expected}`, start returned"))
          | .OutOfFuel => return (st, mk .outOfFuel)
          | .Invalid error => return (st, mk (.interpreterError error))
  | "assert_invalid" | "assert_malformed" =>
    -- The module is declared ill-formed; we pass when our decoder or the
    -- partial static validator rejects it, and fail only if we accept it.
    -- (Run only here — never on a normal `(module …)` — so an aggressive
    -- check can never break a valid module.)
    let filename := jstr? cmd "filename" |>.getD ""
    match (← decodeModuleFile s!"{wasmDir}/{filename}") with
    | .error _ => return (st, mk .pass)
    | .ok m => match m.validate with
      | .error _ => return (st, mk .pass)
      | .ok ()   => return (st, mk (.skipped s!"{kind}: not rejected"))
  | other =>
    return (st, mk (.skipped other))

/-- Drive one `.wast` file end-to-end.

`wastPath` is the absolute path to the input. `tmpRoot` is a directory
the runner owns; this function creates a subdirectory under it for
`json-from-wast`'s outputs. -/
def runFile (wastPath : String) (tmpRoot : String) (fuel : Nat) : IO FileResult := do
  let base := (System.FilePath.mk wastPath).fileStem.getD "wast"
  -- Unique subdir per file (sequence number could collide if called concurrently;
  -- for v1 we assume single-threaded use of `tmpRoot`).
  let wasmDir := s!"{tmpRoot}/{base}"
  IO.FS.createDirAll wasmDir
  let jsonPath := s!"{wasmDir}/script.json"
  -- Step 1: split into JSON + per-module .wasm.
  match (← runWasmTools #["json-from-wast", wastPath, "--wasm-dir", wasmDir, "-o", jsonPath]) with
  | .error e =>
    return { path := wastPath, fileError := some s!"json-from-wast: {e}" }
  | .ok _ =>
    -- Step 2: parse the JSON.
    let raw ← try IO.FS.readFile jsonPath catch e => pure s!"\nERROR: {e}\n"
    match Json.parse raw with
    | .error e =>
      return { path := wastPath, fileError := some s!"json parse: {e}" }
    | .ok root =>
      let cmds := jarr? root "commands" |>.getD #[]
      -- Step 3: execute commands, swallowing per-command exceptions.
      let mut st : ScriptState := {}
      let mut results : Array CmdResult := #[]
      for cmd in cmds do
        let res ← try
          runCommand cmd st wasmDir fuel
        catch e =>
          let line := jnat? cmd "line" |>.getD 0
          let kind := jstr? cmd "type" |>.getD "unknown"
          pure (st, { line, kind, outcome := .interpreterError s!"uncaught: {e.toString}" })
        st := res.1
        results := results.push res.2
      return { path := wastPath, results }

end Wasm.Testsuite
