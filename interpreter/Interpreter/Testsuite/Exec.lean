import Interpreter.Wasm
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
  /-- All declared modules in source order. -/
  modules : Array ModuleSlot := #[]
  /-- `$name` → index into `modules`. Small enough that a linear list is fine. -/
  named   : List (String × Nat) := []
  /-- `(register "M")` bindings: registered name → index into `modules`.
  Imports from a registered module resolve against that instance. -/
  registered : List (String × Nat) := []

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
  { funcs := m.imports.map fun imp =>
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
                -- `args` arrive first-declared-first; `Wasm.run` expects
                -- stack order (head = last argument).
                match Wasm.run fuel em fidx estore args.reverse eenv with
                | .Success vs _ => .Return vs s
                | .Trap _ msg   => .Trap s msg
                | .Invalid msg  => .Trap s s!"invalid in imported function: {msg}"
                | .OutOfFuel    => .Trap s "out of fuel in imported function"
                | .Thrown _ _ _ => .Trap s "uncaught exception" }
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
    let t? : Option Wasm.TableInst :=
      if modN == "spectest" && name == "table" then
        some (List.replicate 10 (Wasm.Value.funcref none))
      else match resolveRegistered sst modN with
        | some (em, estore, _) =>
          match em.tableExports.find? (·.1 = name) with
          | some (_, tIdx) => estore.tables[tIdx]?
          | none => none
        | none => none
    match t? with
    | some t => store := { store with tables := Wasm.listSetAt store.tables ti t }
    | none => pure ()
    ti := ti + 1
  let mut mi := 0
  for (modN, name) in m.importedMemories do
    let mem? : Option Wasm.Mem :=
      if modN == "spectest" && name == "memory" then some (Wasm.Mem.empty 1)
      else match resolveRegistered sst modN with
        | some (em, estore, _) =>
          match em.memoryExports.find? (·.1 = name) with
          | some (_, mIdx) =>
            if mIdx = 0 then some estore.mem else estore.extraMems[mIdx - 1]?
          | none => none
        | none => none
    match mem? with
    | some mem =>
      if mi = 0 then store := { store with mem := mem }
      else store := { store with extraMems := Wasm.listSetAt store.extraMems (mi - 1) mem }
    | none => pure ()
    mi := mi + 1
  -- Re-apply active segments on top of the copied entities.
  match m.memory with
  | some d0 =>
    for seg in d0.data do
      match seg.offset with
      | some off =>
        if seg.memIdx = 0 then
          store := { store with mem := store.mem.writeBytes off.toNat seg.bytes }
        else
          match store.extraMems[seg.memIdx - 1]? with
          | some em =>
            let mems' := Wasm.listSetAt store.extraMems (seg.memIdx - 1)
              (em.writeBytes off.toNat seg.bytes)
            store := { store with extraMems := mems' }
          | none => pure ()
      | none => pure ()
  | none => pure ()
  for seg in m.elements do
    match seg.tableIdx, seg.offset with
    | some t, some off =>
      match store.tables[t]? with
      | some tbl =>
        let tbls' := Wasm.listSetAt store.tables t
          (Wasm.listWriteAt tbl off (seg.funcs.map Wasm.Value.funcref))
        store := { store with tables := tbls' }
      | none => pure ()
    | _, _ => pure ()
  return store

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
      -- `Wasm.run` expects params in *stack* order (top = last source arg)
      -- because WAT-decoded functions reverse params to assign locals[0] to
      -- the first source argument. The testsuite parses args in source
      -- order, so we reverse here to match the call convention.
      match Wasm.run fuel m idx store args.reverse env with
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
      match Wasm.run fuel m idx store args.reverse env with
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
      match Wasm.run fuel m idx store args.reverse env with
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
      match Wasm.run fuel m idx store args.reverse env with
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
  | "module" =>
    let filename := jstr? cmd "filename" |>.getD ""
    let name?    := jstr? cmd "name"
    let slot ← (do
      let res ← decodeModuleFile s!"{wasmDir}/{filename}"
      match res with
      | .ok m =>
        -- Resolve imports (registered instances + ambient spectest) and
        -- copy imported entity values into the fresh store; then, per the
        -- wasm spec, invoke the optional `(start $f)` once. A trap kills
        -- the instance.
        let env := buildEnv st m fuel
        let store0 := applyEntityImports st m m.initialStore
        -- Run constant-expression global initializers (GC `struct.new` /
        -- `array.new*` allocate on the heap) now that imports are in place,
        -- then GC element-segment item initializers into their tables.
        let store0 := m.runConstGlobals fuel store0 env
        let store0 := m.runConstElems fuel store0 env
        -- Data/elem segments whose offset is itself a const-expr
        -- (`global.get`, extended-const) are deferred by `initialStore`;
        -- write them now that the globals hold their real values.
        let store0 := m.runActiveSegments fuel store0 env
        match m.startFunc with
        | none => pure (ModuleSlot.ok m store0 env)
        | some idx =>
          match Wasm.run fuel m idx store0 [] env with
          | .Success _ store' => pure (ModuleSlot.ok m store' env)
          | .Trap _ msg       => pure (ModuleSlot.unavailable s!"start trapped: {msg}")
          | .OutOfFuel        => pure (ModuleSlot.unavailable "start out of fuel")
          | .Invalid msg      => pure (ModuleSlot.unavailable s!"start invalid: {msg}")
          | .Thrown _ _ _     => pure (ModuleSlot.unavailable "uncaught exception in start")
      | .error e => pure (ModuleSlot.unavailable e))
    let idx := st.modules.size
    let modules := st.modules.push slot
    let named := match name? with
      | some n => (n, idx) :: st.named
      | none   => st.named
    let outcome : Outcome :=
      match slot with
      | .ok _ _ _ => .pass
      | .unavailable e => .decodeError e
    return ({ st with modules, named }, mk outcome)
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
          match st.modules[i]! with
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
          let slot := st.modules[i]!
          let (outcome, slot') := runAssertReturn slot field args expected fuel
          return ({ st with modules := st.modules.set! i slot' }, mk outcome)
  | "assert_trap" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let reason := jstr? cmd "text" |>.getD ""
        let slot := st.modules[i]!
        let (outcome, slot') := runAssertTrap slot field args reason fuel
        return ({ st with modules := st.modules.set! i slot' }, mk outcome)
  | "assert_exception" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let slot := st.modules[i]!
        let (outcome, slot') := runAssertException slot field args fuel
        return ({ st with modules := st.modules.set! i slot' }, mk outcome)
  | "action" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let slot := st.modules[i]!
        let (outcome, slot') := runActionOnly slot field args fuel
        return ({ st with modules := st.modules.set! i slot' }, mk outcome)
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
