import Interpreter.Testsuite.Exec

/-!
# `testsuite` — run the W3C Wasm spec testsuite against this interpreter

  lake exe testsuite [--fuel N] [--json|--report] [-h|--help] [PATTERN]

If `PATTERN` is omitted, runs every top-level `.wast` file under
`vendor/testsuite/`. Otherwise filters to files whose relative path
contains `PATTERN` as a substring (case-sensitive). Subdirectories of
`vendor/testsuite/` (e.g. `proposals/`, `legacy/`) are not recursed.

Per `.wast` file we shell out to `wasm-tools json-from-wast` to split the
script into a JSON manifest plus per-module `.wasm` files, then walk the
commands. `module`, `register`, `assert_return`, `assert_trap`,
`assert_exception`, and `action` are executed against the interpreter.
`assert_invalid`/`assert_malformed` are also run — we decode and statically
validate the module, pass when it is rejected, and record
`Skipped(<kind>: not rejected)` only if we wrongly accept it. Every remaining
command type (`assert_unlinkable`, etc.) falls through to `Skipped(<kind>)`.

Output is the human-readable per-file report by default. `--json` emits the
results as a JSON array instead; `--report` emits the stable text coverage
report (one sorted line per command, outcome tag only) that CI byte-compares
to detect coverage drift. The two are mutually exclusive.

Exit code: `1` iff any `Fail`, `InterpreterError`, or `OutOfFuel` outcome was
recorded, and `3` for a setup failure (bad arguments, an unreadable testsuite
directory, no matching files, or temp-dir creation failure). `DecodeError`/
`ModuleUnavailable`/`Skipped` don't fail the run — they're "feature not
implemented" signal, not regressions. `--report` always exits 0 (the report
diff, not the exit code, is the gate).
-/

namespace Wasm.Testsuite

/-! ## Setup -/

-- Large enough for the deepest fuel consumers in the suite (the
-- million-deep tail-call chains in return_call*.wast, ~10 fuel per
-- link); fuel is a bound, not a cost, so this only affects runaway
-- programs.
def defaultFuel : Nat := 50_000_000

def testsuiteDir : String := "vendor/testsuite"

def usage : String :=
"Usage: lake exe testsuite [--fuel N] [--json|--report] [-h|--help] [PATTERN]

  PATTERN     If given, only run .wast files whose path contains this substring.
              If omitted, run every top-level .wast file under vendor/testsuite/.
  --fuel N    Per-assertion reduction-step cap, default 50_000_000.
  --json      Emit results as a JSON array instead of the human-readable report.
  --report    Emit the stable text coverage report (one line per command,
              sorted, outcome tag only — used by CI to detect coverage drift).
              Always exits 0 (the diff against the committed report is the gate).
  -h, --help  Print this message and exit 0."

structure FlagState where
  fuel   : Nat
  help   : Bool := false
  json   : Bool := false
  report : Bool := false

structure Args where
  pattern : Option String
  fuel    : Nat
  json    : Bool := false
  report  : Bool := false

partial def splitFlags
    (toks : List String) (acc : List String) (st : FlagState)
    : Except String (List String × FlagState) :=
  match toks with
  | [] => .ok (acc.reverse, st)
  | "-h" :: rest | "--help" :: rest =>
    splitFlags rest acc { st with help := true }
  | "--fuel" :: nStr :: rest =>
    match nStr.toNat? with
    | some n => splitFlags rest acc { st with fuel := n }
    | none   => .error s!"--fuel expects a non-negative integer, got `{nStr}`"
  | "--fuel" :: [] => .error "--fuel expects an argument"
  | "--json" :: rest => splitFlags rest acc { st with json := true }
  | "--report" :: rest => splitFlags rest acc { st with report := true }
  | tok :: rest => splitFlags rest (tok :: acc) st

def parseArgs (argv : List String) : Except String (Sum Unit Args) := do
  let (pos, st) ← splitFlags argv [] { fuel := defaultFuel }
  if st.help then return .inl ()
  if st.json && st.report then
    .error "--json and --report are mutually exclusive"
  else
  match pos with
  | [] => return .inr { pattern := none, fuel := st.fuel, json := st.json, report := st.report }
  | [p] => return .inr { pattern := some p, fuel := st.fuel, json := st.json, report := st.report }
  | _ => .error "expected at most one PATTERN argument"

/-! ## File discovery -/

/-- Top-level `.wast` files in `vendor/testsuite/`, sorted, optionally
filtered by substring. Errors propagate as `IO` exceptions. -/
def discoverFiles (pattern? : Option String) : IO (Array String) := do
  let entries ← (System.FilePath.mk testsuiteDir).readDir
  let mut out : Array String := #[]
  for e in entries do
    let name := e.fileName
    if name.endsWith ".wast" then
      let keep : Bool := match pattern? with
        | some p => decide ((name.splitOn p).length > 1)
        | none   => true
      if keep then
        out := out.push s!"{testsuiteDir}/{name}"
  return out.qsort (· < ·)

/-! ## Counters and formatting -/

structure Counts where
  pass             : Nat := 0
  fail             : Nat := 0
  skipped          : Nat := 0
  decodeError      : Nat := 0
  interpreterError : Nat := 0
  outOfFuel        : Nat := 0
  cascade          : Nat := 0
deriving Inhabited

def Counts.add (a b : Counts) : Counts := {
  pass := a.pass + b.pass,
  fail := a.fail + b.fail,
  skipped := a.skipped + b.skipped,
  decodeError := a.decodeError + b.decodeError,
  interpreterError := a.interpreterError + b.interpreterError,
  outOfFuel := a.outOfFuel + b.outOfFuel,
  cascade := a.cascade + b.cascade,
}

instance : Add Counts := ⟨Counts.add⟩

def tallyOne (c : Counts) : Outcome → Counts
  | .pass               => { c with pass := c.pass + 1 }
  | .fail _             => { c with fail := c.fail + 1 }
  | .skipped _          => { c with skipped := c.skipped + 1 }
  | .decodeError _      => { c with decodeError := c.decodeError + 1 }
  | .interpreterError _ => { c with interpreterError := c.interpreterError + 1 }
  | .outOfFuel          => { c with outOfFuel := c.outOfFuel + 1 }
  | .moduleUnavailable  => { c with cascade := c.cascade + 1 }

def tally (rs : Array CmdResult) : Counts :=
  rs.foldl (fun c r => tallyOne c r.outcome) {}

/-- True if this file's overall outcome should bump the exit code. -/
def Counts.hasFailure (c : Counts) : Bool :=
  c.fail > 0 || c.interpreterError > 0 || c.outOfFuel > 0

/-- Pad a string on the right to `width` columns. -/
def padR (s : String) (width : Nat) : String :=
  let n := s.length
  if n >= width then s else s ++ "".pushn ' ' (width - n)

private def basename (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- Short one-line summary of the outcome, for failure detail lines. -/
def outcomeSummary : Outcome → String
  | .pass               => "Pass"
  | .fail msg           => s!"Fail  {msg}"
  | .skipped r          => s!"Skipped({r})"
  | .decodeError m      => s!"DecodeError  {m}"
  | .interpreterError m => s!"InterpreterError  {m}"
  | .outOfFuel          => "OutOfFuel"
  | .moduleUnavailable  => "ModuleUnavailable"

/-- Build the per-file report. Renders one summary row, plus zero or more
detail lines: one per failed `module`/`assert_*`/`action`, with cascade
runs collapsed by suppressing `ModuleUnavailable` lines (their count is
in the summary). -/
def renderFile (fr : FileResult) : String := Id.run do
  let mut buf : String := ""
  let c := tally fr.results
  let name := basename fr.path
  -- Summary row.
  let row := s!"{padR name 32}  {padR (toString c.pass) 4} pass  {padR (toString c.fail) 4} fail  {padR (toString c.skipped) 4} skip"
  let row := if c.cascade > 0 then s!"{row}  {padR (toString c.cascade) 4} cascade" else row
  let row := if c.decodeError > 0 then s!"{row}  {c.decodeError} decode-err" else row
  let row := if c.interpreterError > 0 then s!"{row}  {c.interpreterError} interp-err" else row
  let row := if c.outOfFuel > 0 then s!"{row}  {c.outOfFuel} out-of-fuel" else row
  buf := buf ++ row ++ "\n"
  match fr.fileError with
  | some e => buf := buf ++ s!"  ERROR  {e}\n"; return buf
  | none => pure ()
  -- Detail lines for everything except pass / moduleUnavailable / skipped.
  for r in fr.results do
    match r.outcome with
    | .pass | .moduleUnavailable | .skipped _ => pure ()
    | _ =>
      buf := buf ++ s!"  L{r.line}  {padR r.kind 14}  {outcomeSummary r.outcome}\n"
  return buf

/-! ## JSON output -/

section
open Lean (Json)

private def outcomeToJsonFields : Outcome → String × Json
  | .pass               => ("pass",               .null)
  | .fail msg           => ("fail",               .str msg)
  | .skipped r          => ("skipped",            .str r)
  | .decodeError m      => ("decode_error",       .str m)
  | .interpreterError m => ("interpreter_error",  .str m)
  | .outOfFuel          => ("out_of_fuel",        .null)
  | .moduleUnavailable  => ("module_unavailable", .null)

private def cmdResultToJson (file : String) (r : CmdResult) : Json :=
  let (outcomeTag, detail) := outcomeToJsonFields r.outcome
  .mkObj [
    ("file",    .str file),
    ("line",    .num ⟨(r.line : Int), 0⟩),
    ("kind",    .str r.kind),
    ("outcome", .str outcomeTag),
    ("detail",  detail)
  ]

private def fileResultToJson (fr : FileResult) : Array Json :=
  let file := basename fr.path
  let rows := fr.results.map (cmdResultToJson file)
  match fr.fileError with
  | none => rows
  | some e =>
    rows.push (.mkObj [
      ("file",    .str file),
      ("line",    .num ⟨(0 : Int), 0⟩),
      ("kind",    .str "file_error"),
      ("outcome", .str "error"),
      ("detail",  .str e)
    ])

end

/-! ## Report output (stable text for CI freshness check) -/

/-- Bucket free-form skipped reasons into a small stable enumeration. The
report file is byte-compared in CI, so anything emitted here must not depend
on incidental error wording. Free-form sources are:
  * `non-integer expected: <parser err>` — collapse to `non-integer-expected`.
All other reasons are already stable strings (`assert_invalid`/`assert_malformed`
+ `: not rejected` when we accept an ill-formed module, and raw wast command
names like `assert_unlinkable` from the fallthrough) and pass through. -/
private def skippedBucket (r : String) : String :=
  if r.startsWith "non-integer expected" then "non-integer-expected"
  else r

private def outcomeReportTag : Outcome → String
  | .pass               => "pass"
  | .fail _             => "fail"
  | .skipped r          => s!"skipped:{skippedBucket r}"
  | .decodeError _      => "decode_error"
  | .interpreterError _ => "interpreter_error"
  | .outOfFuel          => "out_of_fuel"
  | .moduleUnavailable  => "module_unavailable"

private def cmdResultToReportLine (file : String) (r : CmdResult) : String :=
  s!"{file}:{r.line} {r.kind} {outcomeReportTag r.outcome}"

private def fileResultToReportLines (fr : FileResult) : Array String :=
  let file := basename fr.path
  let rows := fr.results.map (cmdResultToReportLine file)
  match fr.fileError with
  | none => rows
  | some _ => rows.push s!"{file}:0 file_error error"

/-! ## Main loop -/

def EXIT_OK   : UInt32 := 0
def EXIT_FAIL : UInt32 := 1
def EXIT_ERR  : UInt32 := 3

/-- Make a process-scoped temp dir and return its path. On Unix this shells out to mktemp -d; on Windows, which has no mktemp, it creates a uniquely named directory under TEMP (or TMP) with IO.FS.createDirAll. Returns .error if the directory can't be created. -/
def makeTempDir : IO (Except String String) := do
  if System.Platform.isWindows then
    let base ← do
      match ← IO.getEnv "TEMP" with
      | some d => pure d
      | none   =>
        match ← IO.getEnv "TMP" with
        | some d => pure d
        | none   => return .error "could not determine temp directory (TEMP and TMP are unset)"
    let ns ← IO.monoMsNow
    let path := System.FilePath.mk base / s!"wasm-testsuite-{ns}"
    try
      IO.FS.createDirAll path
      return .ok path.toString
    catch e =>
      return .error s!"could not create temp directory {path}: {e.toString}"
  else
    let res ← (IO.Process.output { cmd := "mktemp", args := #["-d", "-t", "wasm-testsuite.XXXXXXXX"] }).toBaseIO
    match res with
    | .ok out =>
      if out.exitCode = 0 then return .ok out.stdout.trimAscii.toString
      else return .error s!"mktemp failed: {out.stderr.trimAscii.toString}"
    | .error _ =>
      return .error "could not create a temporary directory (mktemp not found)"

def runAll (a : Args) : IO UInt32 := do
  let files ← try discoverFiles a.pattern
    catch e =>
      IO.eprintln s!"error: could not read {testsuiteDir}: {e.toString}"
      if a.json then IO.println "[]"
      return EXIT_ERR
  if files.isEmpty then
    let msg := match a.pattern with
      | some p => s!"no .wast files matched `{p}` in {testsuiteDir}"
      | none   => s!"no .wast files in {testsuiteDir}"
    IO.eprintln msg
    if a.json then IO.println "[]"
    return EXIT_ERR

  let tmpRoot ← match (← makeTempDir) with
    | .ok d    => pure d
    | .error e =>
      IO.eprintln s!"error: {e}"
      if a.json then IO.println "[]"
      return EXIT_ERR

  let mut totals : Counts := {}
  let mut anyFailure := false
  let mut jsonRows : Array Lean.Json := #[]
  let mut reportLines : Array String := #[]

  try
    for path in files do
      let fr ← Wasm.Testsuite.runFile path tmpRoot a.fuel
      if a.json then
        jsonRows := jsonRows.append (fileResultToJson fr)
      else if a.report then
        reportLines := reportLines.append (fileResultToReportLines fr)
      else
        IO.print (renderFile fr)
      let c := tally fr.results
      totals := totals + c
      if c.hasFailure then anyFailure := true
  finally
    -- Best-effort cleanup; if it fails, the OS will reap eventually.
    try IO.FS.removeDirAll tmpRoot catch _ => pure ()

  if a.json then
    IO.println (toString (Lean.Json.arr jsonRows))
  else if a.report then
    for ln in reportLines do IO.println ln
  else do
    IO.println ""
    IO.println s!"Totals: {totals.pass} pass  {totals.fail} fail  {totals.skipped} skip  {totals.cascade} cascade  {totals.decodeError} decode-err  {totals.interpreterError} interp-err  {totals.outOfFuel} out-of-fuel"

  -- In report mode the byte-for-byte diff against the committed report is
  -- the CI gate, not the exit code — always succeed so the report still
  -- regenerates when something regressed.
  if a.report then return EXIT_OK
  return if anyFailure then EXIT_FAIL else EXIT_OK

end Wasm.Testsuite

open Wasm.Testsuite in
def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln usage
    return EXIT_ERR
  | .ok (.inl ()) =>
    IO.println usage
    return EXIT_OK
  | .ok (.inr a) => runAll a
