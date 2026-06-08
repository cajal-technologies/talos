import Interpreter.Wasm
import Interpreter.Wasm.Decoder.Wat
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

def Outcome.isFail : Outcome → Bool
  | .fail _ | .interpreterError _ | .outOfFuel => true
  | _ => false

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
  | other => .error s!"non-integer value type `{other}`"

private def parseValue (j : Json) : Except String Value :=
  match jstr? j "type", jstr? j "value" with
  | some ty, some val => parseValueAt ty val
  | _, _ => .error "value missing type/value"

private def parseValues (arr : Array Json) : Except String (List Value) := do
  let mut acc : Array Value := #[]
  for j in arr do
    acc := acc.push (← parseValue j)
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
  | ok (m : Wasm.Module) (store : Wasm.Store Unit)
  | unavailable (reason : String)
deriving Inhabited

structure ScriptState where
  /-- All declared modules in source order. -/
  modules : Array ModuleSlot := #[]
  /-- `$name` → index into `modules`. Small enough that a linear list is fine. -/
  named   : List (String × Nat) := []

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

/-! ## Compact value rendering for failure messages -/

private def renderValue : Value → String
  | .i32 u           => s!"i32:{u.toInt32.toInt}"
  | .i64 u           => s!"i64:{u.toInt64.toInt}"
  | .f32 b           => s!"f32:{(Float32.ofBits b).toFloat}"
  | .f64 b           => s!"f64:{Float.ofBits b}"
  | .funcref none    => "funcref:null"
  | .funcref (some i) => s!"funcref:{i}"

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

/-! ## Command execution -/

/-- Invoke `field` on `slot`'s module with the given args, comparing
returned values against `expected`. Returns the outcome plus an updated
slot — on a successful invoke the store is replaced with the post-call
one (mutations to globals/memory persist for later commands); on an
unexpected trap we still commit the pre-trap store, matching wasm's
"side effects up to the trap are observable" semantics. Out-of-fuel
and invalid leave the slot unchanged. -/
def runAssertReturn
    (slot : ModuleSlot) (field : String) (args expected : List Value) (fuel : Nat)
    : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      -- `Wasm.run` expects params in *stack* order (top = last source arg)
      -- because WAT-decoded functions reverse params to assign locals[0] to
      -- the first source argument. The testsuite parses args in source
      -- order, so we reverse here to match the call convention.
      match Wasm.run fuel m idx store args.reverse with
      | .Success rs store' =>
        let actual := rs.reverse
        let slot' := .ok m store'
        if actual = expected then (.pass, slot')
        else (.fail s!"expected {renderValues expected}, got {renderValues actual}", slot')
      | .Trap store' msg => (.fail s!"unexpected trap `{msg}`", .ok m store')
      | .OutOfFuel => (.outOfFuel, slot)
      | .Invalid msg => (.interpreterError msg, slot)

/-- Invoke and require a trap whose reason contains `expectedReason`.
On the expected trap we commit the pre-trap store (writes performed
before the trap are visible to later commands, per the wasm spec); on
an unexpected return we likewise commit the post-call store. -/
def runAssertTrap
    (slot : ModuleSlot) (field : String) (args : List Value)
    (expectedReason : String) (fuel : Nat) : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      match Wasm.run fuel m idx store args.reverse with
      | .Success rs store' =>
        (.fail s!"expected trap `{expectedReason}`, returned {renderValues rs.reverse}", .ok m store')
      | .Trap store' msg =>
        let slot' : ModuleSlot := .ok m store'
        if expectedReason.isEmpty || (msg.splitOn expectedReason).length > 1 then (.pass, slot')
        else (.fail s!"expected trap `{expectedReason}`, got trap `{msg}`", slot')
      | .OutOfFuel => (.outOfFuel, slot)
      | .Invalid msg => (.interpreterError msg, slot)

/-- Plain `(invoke …)` outside an assertion: passes iff it doesn't trap.
The post-call (or post-trap) store is propagated so subsequent commands
observe the side effects. -/
def runActionOnly
    (slot : ModuleSlot) (field : String) (args : List Value) (fuel : Nat)
    : Outcome × ModuleSlot :=
  match slot with
  | .unavailable _ => (.moduleUnavailable, slot)
  | .ok m store =>
    match m.findExport field with
    | none => (.fail s!"unknown export `{field}`", slot)
    | some idx =>
      match Wasm.run fuel m idx store args.reverse with
      | .Success _ store' => (.pass, .ok m store')
      | .Trap store' msg => (.fail s!"unexpected trap `{msg}`", .ok m store')
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
        -- Per the wasm spec, if `(start $f)` is present we invoke it once
        -- during instantiation with no args. A trap kills the instance.
        -- We skip start entirely on modules with host imports: the
        -- testsuite driver has no `HostEnv` to bind them, and the affected
        -- modules in the spec testsuite (spectest's `print`/`print_i32`)
        -- have no observable side effects anyway.
        match m.startFunc with
        | none => pure (ModuleSlot.ok m m.initialStore)
        | some idx =>
          if !m.imports.isEmpty then
            pure (ModuleSlot.ok m m.initialStore)
          else
            match Wasm.run fuel m idx m.initialStore [] with
            | .Success _ store' => pure (ModuleSlot.ok m store')
            | .Trap _ msg       => pure (ModuleSlot.unavailable s!"start trapped: {msg}")
            | .OutOfFuel        => pure (ModuleSlot.unavailable "start out of fuel")
            | .Invalid msg      => pure (ModuleSlot.unavailable s!"start invalid: {msg}")
      | .error e => pure (ModuleSlot.unavailable e))
    let idx := st.modules.size
    let modules := st.modules.push slot
    let named := match name? with
      | some n => (n, idx) :: st.named
      | none   => st.named
    let outcome : Outcome :=
      match slot with
      | .ok _ _ => .pass
      | .unavailable e => .decodeError e
    return ({ modules, named }, mk outcome)
  | "register" =>
    -- Register itself is just bookkeeping for imports we don't support.
    return (st, mk (.skipped "register"))
  | "assert_return" =>
    let actJ := jobj? cmd "action" |>.getD Json.null
    match parseInvokeAction actJ with
    | .error e => return (st, mk (.interpreterError s!"action parse: {e}"))
    | .ok (modName?, field, args) =>
      match resolveModuleIdx st modName? with
      | .error e => return (st, mk (.interpreterError e))
      | .ok i =>
        let expectedJ := jarr? cmd "expected" |>.getD #[]
        match parseValues expectedJ with
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
