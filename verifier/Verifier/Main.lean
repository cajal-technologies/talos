import Verifier.Emit
import Verifier.Path
import Verifier.Extract
import Interpreter.Wasm.Decoder.Wat
import Cli

/-!
# `verifier` CLI

Run from the project root (directory with `rust/` and `lean/`).

Subcommands: init, del, build, emit, prove, check, extract, report.
Omit crate names for all workspace crates. `foo_bar` maps to `Project.FooBar`.

## Template layout

The scaffolding lives entirely under `verifier/template/`, decoupled from this
code — editing it never requires touching Lean. Two independent trees:

* `template/project/` — a whole project (`rust/` + `lean/`) with a worked
                        `is_even`/`IsEven` example. Copied verbatim by `init`.
* `template/module/`  — the hand-written Lean files that accompany the
                        auto-generated `Program.lean` (currently `Spec.lean`).
                        Copied by `emit` into the crate's Lean module, with
                        `CRATE_NAME` / `MODULE_NAME` replaced, never clobbering
                        files that already exist.

Adding a file to a crate's Lean module, or changing the starter rust, is a pure
template edit. The verifier only ever copies these trees and substitutes names.
-/

open System (FilePath)
open Verifier.Path

namespace Verifier

-- ----------------------------------------------------------------------------
-- Small helpers
-- ----------------------------------------------------------------------------

private def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

private def writeFile (p : FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then IO.FS.createDirAll parent
  IO.FS.writeFile p content

private def runOrDie (cmd : String) (args : Array String)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := cmd, args := args, cwd := cwd, env := env,
    stdin := .inherit, stdout := .inherit, stderr := .inherit
  }
  let code ← child.wait
  if code ≠ 0 then
    die s!"`{cmd} {String.intercalate " " args.toList}` failed (exit {code})"

private def captureStdout (cmd : String) (args : Array String)
    (cwd : Option FilePath := none) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd }
  if out.exitCode ≠ 0 then
    die s!"`{cmd}` failed (exit {out.exitCode}):\n{out.stderr}"
  pure out.stdout

/-- `is_even` → `IsEven`. -/
private def snakeToPascal (s : String) : String :=
  String.intercalate "" <| (s.splitOn "_").map fun part =>
    match part.toList with
    | []      => ""
    | c :: cs => String.ofList (c.toUpper :: cs)

private def isValidCrateName (s : String) : Bool :=
  match s.toList with
  | []        => false
  | c :: rest => c != '_' && (c.isAlphanum || c = '_') &&
                 rest.all (fun ch => ch.isAlphanum || ch = '_')

private def projectDirFromCwd : IO FilePath := do
  absNormalize (← IO.currentDir)

private def fileContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- `true` iff `a` is newer than `b`, or `b` does not exist. Returns `false` if `a` is missing. -/
private def isNewer (a b : FilePath) : IO Bool := do
  if ¬ (← System.FilePath.pathExists b) then return true
  if ¬ (← System.FilePath.pathExists a) then return false
  let ma ← a.metadata
  let mb ← b.metadata
  return ma.modified > mb.modified

-- ----------------------------------------------------------------------------
-- Template tree
-- ----------------------------------------------------------------------------

/-- Locate `verifier/template/` relative to the running binary.
    Binary lives at `<verifier-root>/.lake/build/bin/verifier`. -/
private def locateTemplateRoot : IO FilePath := do
  let app ← IO.appPath
  let some verifierRoot := app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | die s!"cannot locate template root (binary path: {app})"
  let root := verifierRoot / "template"
  unless ← System.FilePath.pathExists (root / "project" / "lean" / "Project.lean") do
    die s!"template not found at {root}"
  pure root

/-- Build/VCS directories we never copy out of a template tree, in case stray
    artefacts are sitting on disk next to the source files. -/
private def denyDir (name : String) : Bool :=
  name == ".lake" || name == "target" || name == "build"
    || name == ".git" || name == "node_modules"

/-- Recursively copy `src` into `dst`, rewriting the text of every file through
    `subst`. Directories named in `denyDir` are skipped. -/
private partial def copyTree (src dst : FilePath) (subst : String → String) : IO Unit := do
  IO.FS.createDirAll dst
  for entry in (← src.readDir) do
    let child  := entry.path
    let target := dst / entry.fileName
    if ← child.isDir then
      unless denyDir entry.fileName do copyTree child target subst
    else
      IO.FS.writeFile target (subst (← IO.FS.readFile child))

/-- Like `copyTree`, but never overwrites a file that already exists at the
    destination. Returns the files actually written. -/
private partial def copyTreeNoClobber (src dst : FilePath) (subst : String → String) :
    IO (Array FilePath) := do
  let mut written : Array FilePath := #[]
  for entry in (← src.readDir) do
    let child  := entry.path
    let target := dst / entry.fileName
    if ← child.isDir then
      unless denyDir entry.fileName do
        written := written ++ (← copyTreeNoClobber child target subst)
    else
      unless ← System.FilePath.pathExists target do
        if let some parent := target.parent then IO.FS.createDirAll parent
        IO.FS.writeFile target (subst (← IO.FS.readFile child))
        written := written.push target
  pure written

-- ----------------------------------------------------------------------------
-- Workspace / import bookkeeping
-- ----------------------------------------------------------------------------

private def removeWorkspaceMember (cargoToml : FilePath) (crate : String) : IO Unit := do
  unless ← System.FilePath.pathExists cargoToml do return
  let txt ← IO.FS.readFile cargoToml
  let entry := s!"\"{crate}\""
  unless fileContains txt entry do return
  -- Handle every format a `members = [...]` entry can take (manual edits, tooling).
  let cleaned :=
    txt
    |>.replace (s!"\n  {entry},") ""   -- entry written on its own line
    |>.replace (s!",{entry}")     ""   -- inline trailing, no space
    |>.replace (s!", {entry}")    ""   -- inline trailing, with space
    |>.replace (s!"{entry},")     ""   -- inline leading, no space after
    |>.replace entry               ""  -- sole entry fallback
  IO.FS.writeFile cargoToml cleaned
  IO.println s!"    removed `{crate}` from {cargoToml}"

private def removeProjectImport (projectLean : FilePath) (pascal : String) : IO Unit := do
  unless ← System.FilePath.pathExists projectLean do return
  let importLine := s!"import Project.{pascal}.Spec"
  let txt ← IO.FS.readFile projectLean
  unless fileContains txt importLine do return
  let cleaned := txt.replace (importLine ++ "\n") "" |>.replace importLine ""
  IO.FS.writeFile projectLean cleaned
  IO.println s!"    removed `{importLine}` from {projectLean}"

-- ----------------------------------------------------------------------------
-- `del`
-- ----------------------------------------------------------------------------

private def cmdDel (crate : String) : IO Unit := do
  unless isValidCrateName crate do
    die s!"invalid crate name `{crate}` (use snake_case: letters, digits, underscores)"
  let projectDir ← projectDirFromCwd
  let pascal   := snakeToPascal crate
  let rustCrate := projectDir / "rust" / crate
  let leanMod  := projectDir / "lean" / "Project" / pascal
  let buildDir := projectDir / "rust" / "build" / crate
  let hasRust ← System.FilePath.pathExists rustCrate
  let hasLean ← System.FilePath.pathExists leanMod
  unless hasRust || hasLean do
    die s!"crate `{crate}` not found (looked in {rustCrate} and {leanMod})"
  IO.println s!"==> removing crate `{crate}` (Project.{pascal})"
  if hasRust then
    runOrDie "rm" #["-rf", rustCrate.toString]
    IO.println s!"    deleted {rustCrate}"
  if hasLean then
    runOrDie "rm" #["-rf", leanMod.toString]
    IO.println s!"    deleted {leanMod}"
  if ← System.FilePath.pathExists buildDir then
    runOrDie "rm" #["-rf", buildDir.toString]
    IO.println s!"    deleted {buildDir}"
  removeWorkspaceMember (projectDir / "rust" / "Cargo.toml") crate
  removeProjectImport   (projectDir / "lean" / "Project.lean") pascal
  IO.println s!"==> done"

-- ----------------------------------------------------------------------------
-- Crate discovery
-- ----------------------------------------------------------------------------

/-- One rust crate in the workspace, paired with its (possibly not-yet-created)
    lean module dir. The lean dir is materialised by `emit`, so discovery never
    requires it to exist. -/
structure Crate where
  name    : String
  rustDir : FilePath
  leanDir : FilePath

private def discoverCrates (projectDir : FilePath) : IO (Array Crate) := do
  let rustRoot := projectDir / "rust"
  unless ← System.FilePath.pathExists rustRoot do
    die s!"{rustRoot} not found — are you in a verifier project root?"
  let leanRoot := projectDir / "lean" / "Project"
  let entries ← rustRoot.readDir
  let mut acc : Array Crate := #[]
  for entry in entries do
    let p := entry.path
    if ¬ (← p.isDir) then continue
    unless ← System.FilePath.pathExists (p / "Cargo.toml") do continue
    let name := entry.fileName
    acc := acc.push { name, rustDir := p, leanDir := leanRoot / snakeToPascal name }
  pure acc

private def selectCrates (all : Array Crate) (names : List String) : IO (Array Crate) := do
  if names.isEmpty then return all
  let mut out : Array Crate := #[]
  for n in names do
    match all.find? (·.name == n) with
    | some c => out := out.push c
    | none   => die s!"crate `{n}` not found (available: {String.intercalate ", " (all.toList.map (·.name))})"
  pure out

private def discoverSelected (projectDir : FilePath) (names : List String) : IO (Array Crate) := do
  let all ← discoverCrates projectDir
  if all.isEmpty then die s!"{projectDir}/rust has no crate subdirectories"
  selectCrates all names

private def printCrateBanner (crates : Array Crate) : IO Unit :=
  IO.println s!"==> {crates.size} crate(s): {String.intercalate ", " (crates.toList.map (·.name))}"

-- ----------------------------------------------------------------------------
-- `build` / `emit` / `prove` / `check`
-- ----------------------------------------------------------------------------

private def emitProgramFile (c : Crate) (m : Wasm.Module) : IO Unit := do
  IO.FS.createDirAll c.leanDir
  let modName := s!"Project.{snakeToPascal c.name}"
  let body :=
    String.intercalate "\n" [
      "/-",
      "  AUTO-GENERATED by `verifier emit`. Do not edit by hand.",
      "-/",
      "",
      "import CodeLib",
      "",
      "set_option maxRecDepth 1048576",
      "",
      s!"namespace {modName}",
      "",
      "open Wasm",
      "",
      Emit.funcBodies m,
      "",
      "def «module» : Wasm.Module :=",
      Emit.module m,
      "",
      s!"end {modName}",
      ""
    ]
  IO.FS.writeFile (c.leanDir / "Program.lean") body

/-- Copy the hand-written lean files (`template/module/`) that accompany the
    generated `Program.lean` into the crate's lean module, substituting names.
    Existing files are never overwritten, so user edits — and the committed
    `programs/` corpus — survive re-emits untouched. -/
private def scaffoldModuleFiles (c : Crate) : IO Unit := do
  let moduleRoot := (← locateTemplateRoot) / "module"
  let pascal := snakeToPascal c.name
  let subst := fun (s : String) => (s.replace "MODULE_NAME" pascal).replace "CRATE_NAME" c.name
  let written ← copyTreeNoClobber moduleRoot c.leanDir subst
  for f in written do
    IO.println s!"    scaffolded {f}"

private def reproducibleRustflags (rustDir : FilePath) : IO String := do
  let sysrootOut ← IO.Process.output
    { cmd := "rustc", args := #["--print", "sysroot"], cwd := some rustDir }
  let sysroot :=
    if sysrootOut.exitCode = 0 then sysrootOut.stdout.trimAscii else ""
  let cargoHome ← do
    match ← IO.getEnv "CARGO_HOME" with
    | some v => pure v
    | none =>
      match ← IO.getEnv "HOME" with
      | some h => pure (h ++ "/.cargo")
      | none   => pure ""
  let home := (← IO.getEnv "HOME").getD ""
  let mut remaps : Array String := #[]
  if !home.isEmpty then
    remaps := remaps.push s!"--remap-path-prefix={home}=/home"
  if !cargoHome.isEmpty then
    remaps := remaps.push s!"--remap-path-prefix={cargoHome}=/cargo-home"
  if !sysroot.isEmpty then
    remaps := remaps.push s!"--remap-path-prefix={sysroot}=/rustc-sysroot"
  pure (String.intercalate " " remaps.toList)

private def buildWasm (projectDir : FilePath) (crates : Array Crate) : IO Unit := do
  IO.println "==> cargo build-wasm (workspace)"
  let rustDir := projectDir / "rust"
  let rustflags ← reproducibleRustflags rustDir
  runOrDie "cargo" #["build-wasm"]
    (cwd := some rustDir)
    (env := #[("RUSTFLAGS", some rustflags)])
  let buildRoot := projectDir / "rust" / "build"
  let cargoTarget := projectDir / "rust" / "target" / "wasm32-unknown-unknown" / "release"
  for c in crates do
    let outDir := buildRoot / c.name
    IO.FS.createDirAll outDir
    let src := cargoTarget / s!"{c.name}.wasm"
    unless ← System.FilePath.pathExists src do
      die s!"expected {src} after cargo build-wasm but it is missing"
    let wasmDst := outDir / "program.wasm"
    let tmpWasm := outDir / "program.wasm.tmp"
    runOrDie "wasm-tools"
      #["strip", "-o", tmpWasm.toString, src.toString]
    let bytes ← IO.FS.readBinFile tmpWasm
    let needWrite ← do
      if ← System.FilePath.pathExists wasmDst then
        let cur ← IO.FS.readBinFile wasmDst
        pure (cur.toList != bytes.toList)
      else pure true
    if needWrite then IO.FS.writeBinFile wasmDst bytes
    IO.FS.removeFile tmpWasm
    let watText ← captureStdout "wasm-tools" #["print", wasmDst.toString]
    let watFile := outDir / "program.wat"
    let writeWat ← do
      if needWrite then pure true
      else if ¬ (← System.FilePath.pathExists watFile) then pure true
      else pure false
    if writeWat then IO.FS.writeFile watFile watText

private def emitOneCrate (projectDir : FilePath) (c : Crate) (forceEmit : Bool) : IO Unit := do
  let buildDir := projectDir / "rust" / "build" / c.name
  let wasmDst := buildDir / "program.wasm"
  let watFile := buildDir / "program.wat"
  let programLean := c.leanDir / "Program.lean"
  unless ← System.FilePath.pathExists watFile do
    die s!"{c.name}: {watFile} not found — run `verifier build {c.name}` first"
  let stale := forceEmit ∨ (← isNewer wasmDst programLean)
  if stale then
    let watText ← IO.FS.readFile watFile
    match Wasm.Decoder.Wat.decode watText with
    | .error e => die s!"{c.name}: wat decoder rejected the module: {e}"
    | .ok m    =>
      emitProgramFile c m
      IO.println s!"    emitted {programLean}"
  else
    IO.println s!"    {programLean} is up to date"
  scaffoldModuleFiles c

private def emitPrograms (projectDir : FilePath) (crates : Array Crate) (forceEmit : Bool) : IO Unit := do
  for c in crates do
    emitOneCrate projectDir c forceEmit

/-- Lake targets for `prove`. Each crate's generated `Program` is always built —
    it is machine-emitted and must compile. A crate's hand-written `Spec` is built
    only when it is wired into `lean/Project.lean`; a `Spec` the manifest
    intentionally leaves out (e.g. a known-broken proof) is skipped. This way
    `prove` mirrors exactly what the project declares to be in scope rather than
    assuming every crate has a buildable `Spec`. -/
private def proveTargets (projectDir : FilePath) (crates : Array Crate) : IO (Array String) := do
  let projectLean := projectDir / "lean" / "Project.lean"
  let manifest ←
    if ← System.FilePath.pathExists projectLean then IO.FS.readFile projectLean
    else pure ""
  let mut targets : Array String := #[]
  for c in crates do
    let pascal := snakeToPascal c.name
    targets := targets.push s!"Project.{pascal}.Program"
    if fileContains manifest s!"import Project.{pascal}.Spec" then
      targets := targets.push s!"Project.{pascal}.Spec"
  pure targets

private def lakeBuildCount (leanDir : FilePath) (targets : Array String := #[]) : IO (Bool × Nat) := do
  let label :=
    if targets.isEmpty then "Project (default)"
    else String.intercalate ", " targets.toList
  IO.println s!"==> lake build {label} ({leanDir})"
  let args := if targets.isEmpty then #["build"] else #["build"] ++ targets
  let out ← IO.Process.output { cmd := "lake", args := args, cwd := some leanDir }
  IO.print out.stdout
  IO.eprint out.stderr
  let combined := out.stdout ++ "\n" ++ out.stderr
  let sorries := (combined.splitOn "declaration uses 'sorry'").length - 1
  pure (out.exitCode = 0, sorries)

private def cmdProveAt (projectDir : FilePath) (crates : Array Crate) : IO Bool := do
  let leanDir := projectDir / "lean"
  let targets ← proveTargets projectDir crates
  let (ok, sorries) ← lakeBuildCount leanDir targets
  IO.println ""
  IO.println s!"==> {crates.size} crate(s), {if ok then "lake build OK" else "lake build FAILED"}, {sorries} sorry warning(s)"
  pure ok

private def cmdBuild (names : List String) : IO Unit := do
  let projectDir ← projectDirFromCwd
  let crates ← discoverSelected projectDir names
  printCrateBanner crates
  buildWasm projectDir crates

private def cmdEmit (names : List String) (forceEmit : Bool) : IO Unit := do
  let projectDir ← projectDirFromCwd
  let crates ← discoverSelected projectDir names
  printCrateBanner crates
  emitPrograms projectDir crates forceEmit

private def cmdProve (names : List String) : IO Unit := do
  let projectDir ← projectDirFromCwd
  let crates ← discoverSelected projectDir names
  printCrateBanner crates
  unless ← cmdProveAt projectDir crates do IO.Process.exit 1

private def cmdCheckIn (projectDir : FilePath) (names : List String)
    (forceEmit : Bool) (noProve : Bool) : IO Bool := do
  let crates ← discoverSelected projectDir names
  printCrateBanner crates
  buildWasm projectDir crates
  emitPrograms projectDir crates forceEmit
  if noProve then
    IO.println ""
    IO.println s!"==> {crates.size} crate(s) built and emitted; skipping `lake build` (--no-prove)"
    pure true
  else
    cmdProveAt projectDir crates

private def cmdCheck (names : List String) (forceEmit : Bool) (noProve : Bool) : IO Unit := do
  let projectDir ← projectDirFromCwd
  unless ← cmdCheckIn projectDir names forceEmit noProve do IO.Process.exit 1

-- ----------------------------------------------------------------------------
-- `init` (`new` alias)
-- ----------------------------------------------------------------------------

private def cmdInit (projectPathIn : String) : IO Unit := do
  let projectDir ← absNormalize ⟨projectPathIn⟩
  if ← System.FilePath.pathExists projectDir then
    let entries ← (projectDir.readDir : IO _)
    unless entries.isEmpty do
      die s!"{projectDir} already exists and is not empty"
  let projectTemplate := (← locateTemplateRoot) / "project"
  IO.println s!"==> scaffolding {projectTemplate} → {projectDir}"
  copyTree projectTemplate projectDir id
  let leanDir := projectDir / "lean"
  IO.println "==> lake update"
  runOrDie "lake" #["update"] (cwd := some leanDir)
  IO.println "==> lake exe cache get"
  runOrDie "lake" #["exe", "cache", "get"] (cwd := some leanDir)
  IO.println "==> lake build (verifying the bundled example)"
  let (ok, _) ← lakeBuildCount leanDir
  unless ok do die "initial lake build failed"
  IO.println s!"==> done. Project ready at {projectDir}"
  IO.println s!"==>   next: verifier build && verifier emit  (then edit Spec.lean, then: verifier prove)"

-- ----------------------------------------------------------------------------
-- CLI plumbing
-- ----------------------------------------------------------------------------

open Cli

def runInit (p : Parsed) : IO UInt32 := do
  cmdInit (p.positionalArg! "projectPath" |>.as! String)
  pure 0

def runNew (p : Parsed) : IO UInt32 := runInit p

def runDel (p : Parsed) : IO UInt32 := do
  cmdDel (p.positionalArg! "crate" |>.as! String)
  pure 0

def runBuild (p : Parsed) : IO UInt32 := do
  cmdBuild (p.variableArgs.map (·.as! String) |>.toList)
  pure 0

def runEmit (p : Parsed) : IO UInt32 := do
  cmdEmit (p.variableArgs.map (·.as! String) |>.toList) (p.hasFlag "force-emit")
  pure 0

def runProve (p : Parsed) : IO UInt32 := do
  cmdProve (p.variableArgs.map (·.as! String) |>.toList)
  pure 0

def runCheck (p : Parsed) : IO UInt32 := do
  cmdCheck (p.variableArgs.map (·.as! String) |>.toList)
    (p.hasFlag "force-emit") (p.hasFlag "no-prove")
  pure 0

private def locateReportDir : IO FilePath := do
  let app ← IO.appPath
  let some verifierRoot := app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | die s!"could not locate verifier root from {app}"
  let reportDir := verifierRoot / "report"
  unless ← System.FilePath.pathExists (reportDir / "package.json") do
    die s!"bundled report project not found at {reportDir} (resolved from {app})"
  absNormalize reportDir

def runReport (p : Parsed) : IO UInt32 := do
  let projectDir ← projectDirFromCwd
  let extractedFlag : String := if p.hasFlag "extracted" then
    p.flag! "extracted" |>.as! String
  else
    "extracted"
  let outFlag : String := if p.hasFlag "out" then
    p.flag! "out" |>.as! String
  else
    "out"
  let extractedDir ← absNormalize ⟨extractedFlag⟩
  let outDir ← absNormalize ⟨outFlag⟩
  let reportDir ← locateReportDir
  IO.println s!"==> verifier extract → {extractedDir}"
  Verifier.Extract.run projectDir extractedDir (p.variableArgs.map (·.as! String) |>.toList)
  let nodeModules := reportDir / "node_modules"
  unless ← System.FilePath.pathExists nodeModules do
    IO.println s!"==> npm install ({reportDir})"
    runOrDie "npm" #["install", "--silent"] (cwd := some reportDir)
  IO.println s!"==> build report ({reportDir}) → {outDir}"
  runOrDie "npm"
    #["run", "build-report", "--", extractedDir.toString, outDir.toString]
    (cwd := some reportDir)
  IO.println s!"==> report ready at {outDir / "index.html"}"
  pure 0

def runExtract (p : Parsed) : IO UInt32 := do
  let projectDir ← projectDirFromCwd
  let outFlag : String := if p.hasFlag "out" then
    p.flag! "out" |>.as! String
  else
    "extracted"
  let outDir ← absNormalize ⟨outFlag⟩
  Verifier.Extract.run projectDir outDir (p.variableArgs.map (·.as! String) |>.toList)
  pure 0

def initCmd : Cmd := `[Cli|
  init VIA runInit;
  "Scaffold a new verification project from the bundled template."

  ARGS:
    projectPath : String; "Directory to create (must not already exist or be empty)."
]

def newCmd : Cmd := `[Cli|
  «new» VIA runNew;
  "Alias for `init`."

  ARGS:
    projectPath : String; "Directory to create (must not already exist or be empty)."
]

def delCmd : Cmd := `[Cli|
  del VIA runDel;
  "Remove a crate from the current project (source, lean module, build artefacts, Cargo.toml, Project.lean)."

  ARGS:
    crate : String; "Crate name in snake_case."
]

def buildCmd : Cmd := `[Cli|
  build VIA runBuild;
  "Build wasm/wat for selected crates (omit names for all)."

  ARGS:
    ...crates : String; "Crate names (snake_case); default: all workspace crates."
]

def emitCmd : Cmd := `[Cli|
  emit VIA runEmit;
  "Transpile program.wat → Program.lean and scaffold Spec.lean for selected crates. [--force-emit]"

  FLAGS:
    "force-emit"; "Re-emit even if wasm is older than Program.lean."

  ARGS:
    ...crates : String; "Crate names; default: all."
]

def proveCmd : Cmd := `[Cli|
  prove VIA runProve;
  "Run `lake build` on selected crates' Lean modules (omit names for all)."

  ARGS:
    ...crates : String; "Crate names; default: all."
]

def checkCmd : Cmd := `[Cli|
  «check» VIA runCheck;
  "build → emit → prove for selected crates (omit names for all). [--force-emit] [--no-prove]"

  FLAGS:
    "force-emit"; "Re-emit Program.lean even if wasm is unchanged."
    "no-prove";   "Build wasm and emit only; skip `lake build`."

  ARGS:
    ...crates : String; "Crate names; default: all."
]

def reportCmd : Cmd := `[Cli|
  «report» VIA runReport;
  "Run `verifier extract` then build the static HTML report. [--extracted DIR] [--out DIR]"

  FLAGS:
    "extracted"  : String; "Directory for extract JSON (default: ./extracted)."
    "out"        : String; "Directory for the built site (default: ./out)."

  ARGS:
    ...crates : String; "Optional crate filter for extract."
]

def extractCmd : Cmd := `[Cli|
  «extract» VIA runExtract;
  "Emit one JSON artifact per crate at <DIR>/<crate>.json. [--out DIR]"

  FLAGS:
    "out" : String; "Output directory (default: ./extracted)."

  ARGS:
    ...crates : String; "Crate names; default: all."
]

def mainCmd : Cmd := `[Cli|
  verifier NOOP; ["0.1.0"]
  "Rust → wasm → Lean verification driver."

  SUBCOMMANDS:
    initCmd;
    newCmd;
    delCmd;
    buildCmd;
    emitCmd;
    proveCmd;
    checkCmd;
    extractCmd;
    reportCmd

  EXTENSIONS:
    author "Cajal-Technologies"
]

def main (args : List String) : IO UInt32 :=
  mainCmd.validate args

end Verifier

def main := Verifier.main
