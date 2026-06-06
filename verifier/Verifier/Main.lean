import Verifier.Emit
import Verifier.Path
import Verifier.Extract
import Interpreter.Wasm.Decoder.Wat
import Cli

/-!
# `verifier` CLI

Run from the project root (directory with `rust/` and `lean/`).

Subcommands: init, add, del, build, emit, prove, check, extract, report.
Omit crate names for all workspace crates. `foo_bar` maps to `Project.FooBar`.
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

/-- `true` iff `path` is a placeholder stub written by `verifier add` (always needs re-emit). -/
private def isPlaceholder (path : FilePath) : IO Bool := do
  if ¬ (← System.FilePath.pathExists path) then return false
  let content ← IO.FS.readFile path
  return content.startsWith "/-\n  Placeholder"

-- ----------------------------------------------------------------------------
-- Template loading
-- ----------------------------------------------------------------------------

/-- Locate `verifier/template/` relative to the running binary.
    Binary lives at `<verifier-root>/.lake/build/bin/verifier`. -/
private def locateTemplateRoot : IO FilePath := do
  let app ← IO.appPath
  let some verifierRoot := app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | die s!"cannot locate template root (binary path: {app})"
  let root := verifierRoot / "template"
  unless ← System.FilePath.pathExists (root / "lean" / "Project.lean") do
    die s!"template not found at {root}"
  pure root

-- The lean files created per crate by `verifier add` (besides Program.lean and Spec.lean).
-- Each name requires a matching template at verifier/template/crate/lean_<Name>.lean.
-- To add or remove a file: edit this list and add/remove the template file.
private def crateModuleFiles : List String := ["Proof"]

private def templateRelPaths : List String :=
  let isEvenLean := (["Program", "Spec"] ++ crateModuleFiles).map
    fun f => s!"lean/Project/IsEven/{f}.lean"
  [ "rust/Cargo.toml", "rust/.cargo/config.toml", "rust/.gitignore", "rust/justfile",
    "rust/is_even/Cargo.toml", "rust/is_even/src/lib.rs", "rust/is_even/src/exports.rs",
    "lean/lean-toolchain", "lean/lakefile.toml", "lean/.gitignore", "lean/Project.lean"
  ] ++ isEvenLean

private def loadTemplateFiles : IO (List (String × String)) := do
  let root ← locateTemplateRoot
  templateRelPaths.mapM fun (rel : String) => do
    let path := root / rel
    unless ← System.FilePath.pathExists path do
      die s!"template file missing: {path}"
    pure (rel, ← IO.FS.readFile path)

private def scaffoldedLakefile : String :=
  "name = \"Project\"\n\
   version = \"0.1.0\"\n\
   defaultTargets = [\"Project\"]\n\
   \n\
   [[require]]\n\
   name = \"CodeLib\"\n\
   git = \"https://github.com/cajal-technologies/talos.git\"\n\
   subDir = \"codelib\"\n\
   rev = \"main\"\n\
   \n\
   [[lean_lib]]\n\
   name = \"Project\"\n"

-- ----------------------------------------------------------------------------
-- Single-crate scaffold (`add`)
-- ----------------------------------------------------------------------------

private def withCrateName (s : String) (crate : String) : String :=
  s.replace "CRATE_NAME" crate

private def readCrateTemplate (rel : String) : IO String := do
  let root ← locateTemplateRoot
  IO.FS.readFile (root / "crate" / rel)

private def leanProgramStub (pascal : String) : String :=
  "/-\n  Placeholder until `verifier emit`. Replaced by auto-generated output.\n-/\n\n" ++
  "import CodeLib\n\n" ++
  s!"namespace Project.{pascal}\n\nopen Wasm\n\n" ++
  "def «module» : Wasm.Module :=\n{\n  funcs := [],\n  exports := [],\n  memory := none,\n  globals := []\n}\n\n" ++
  s!"end Project.{pascal}\n"

private def leanSpecStub (crate pascal : String) : String :=
  s!"import Project.{pascal}.Program\n\nnamespace Project.{pascal}.Spec\n\nopen Wasm\n\n" ++
  "/-- TODO: refine after `verifier emit`.\n\nInformal spec:\n" ++
  s!"Describe the wasm export `{crate}` here. -/\n" ++
  s!"@[spec_of \"rust-exported\" \"{crate}::{crate}\"]\ndef {pascal}Spec : Prop :=\n  True\n\n" ++
  s!"end Project.{pascal}.Spec\n"

private def withPascal (s : String) (pascal : String) : String :=
  s.replace "PASCAL" pascal

private def addWorkspaceMember (cargoToml : FilePath) (crate : String) : IO Unit := do
  let txt ← IO.FS.readFile cargoToml
  if fileContains txt crate then return
  let needle := "members = ["
  unless fileContains txt needle do
    die s!"{cargoToml}: could not find `[workspace] members = [`"
  IO.FS.writeFile cargoToml (txt.replace needle (needle ++ "\n  \"" ++ crate ++ "\","))

private def addProjectImports (projectLean : FilePath) (pascal : String) : IO Unit := do
  let specLine := s!"import Project.{pascal}.Spec"
  let txt ← IO.FS.readFile projectLean
  if fileContains txt specLine then return
  IO.FS.writeFile projectLean (txt.trimAsciiEnd.toString ++ "\n" ++ specLine ++ "\n")

private def removeWorkspaceMember (cargoToml : FilePath) (crate : String) : IO Unit := do
  unless ← System.FilePath.pathExists cargoToml do return
  let txt ← IO.FS.readFile cargoToml
  let entry := s!"\"{crate}\""
  unless fileContains txt entry do return
  -- Handle every format our addWorkspaceMember (or manual edits) can produce.
  let cleaned :=
    txt
    |>.replace (s!"\n  {entry},") ""   -- form written by addWorkspaceMember
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

private def cmdAdd (crate : String) : IO Unit := do
  unless isValidCrateName crate do
    die s!"invalid crate name `{crate}` (use snake_case: letters, digits, underscores)"
  let projectDir ← projectDirFromCwd
  let pascal := snakeToPascal crate
  let rustCrate := projectDir / "rust" / crate
  if ← System.FilePath.pathExists rustCrate then die s!"{rustCrate} already exists"
  let leanMod := projectDir / "lean" / "Project" / pascal
  if ← System.FilePath.pathExists leanMod then die s!"{leanMod} already exists"
  IO.println s!"==> adding crate `{crate}` → Project.{pascal}"
  let cargoToml ← readCrateTemplate "rust_Cargo.toml"
  let libRs ← readCrateTemplate "rust_lib.rs"
  let exportsRs ← readCrateTemplate "rust_exports.rs"
  writeFile (rustCrate / "Cargo.toml") (withCrateName cargoToml crate)
  writeFile (rustCrate / "src/lib.rs") (withCrateName libRs crate)
  writeFile (rustCrate / "src/exports.rs") (withCrateName exportsRs crate)
  addWorkspaceMember (projectDir / "rust/Cargo.toml") crate
  writeFile (leanMod / "Program.lean") (leanProgramStub pascal)
  writeFile (leanMod / "Spec.lean") (leanSpecStub crate pascal)
  for name in crateModuleFiles do
    let content ← readCrateTemplate s!"lean_{name}.lean"
    writeFile (leanMod / s!"{name}.lean") (withPascal content pascal)
  addProjectImports (projectDir / "lean/Project.lean") pascal
  IO.println s!"==> done. Next: verifier build {crate} && verifier emit {crate}"

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

/-- One rust crate in the workspace, paired with its lean module dir. -/
structure Crate where
  name    : String
  rustDir : FilePath
  leanDir : FilePath

private def discoverCrates (projectDir : FilePath) : IO (Array Crate) := do
  let rustRoot := projectDir / "rust"
  let leanRoot := projectDir / "lean" / "Project"
  unless ← System.FilePath.pathExists rustRoot do
    die s!"{rustRoot} not found — are you in a verifier project root?"
  unless ← System.FilePath.pathExists leanRoot do
    die s!"{leanRoot} not found — are you in a verifier project root?"
  let entries ← rustRoot.readDir
  let mut acc : Array Crate := #[]
  for entry in entries do
    let p := entry.path
    if ¬ (← p.isDir) then continue
    let cargoToml := p / "Cargo.toml"
    unless ← System.FilePath.pathExists cargoToml do continue
    let name := entry.fileName
    let mod := snakeToPascal name
    let leanDir := leanRoot / mod
    unless ← System.FilePath.pathExists leanDir do
      die s!"crate `{name}` has no matching lean module at {leanDir}\n(expected {name} → {mod})"
    acc := acc.push { name, rustDir := p, leanDir }
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
  let wasmDst := projectDir / "rust" / "build" / c.name / "program.wasm"
  let programLean := c.leanDir / "Program.lean"
  let stale := forceEmit ∨ (← isPlaceholder programLean) ∨ (← isNewer wasmDst programLean)
  if stale then
    let watText ← IO.FS.readFile (projectDir / "rust" / "build" / c.name / "program.wat")
    match Wasm.Decoder.Wat.decode watText with
    | .error e => die s!"{c.name}: wat decoder rejected the module: {e}"
    | .ok m    =>
      emitProgramFile c m
      IO.println s!"    emitted {programLean}"
  else
    IO.println s!"    {programLean} is up to date"

private def emitPrograms (projectDir : FilePath) (crates : Array Crate) (forceEmit : Bool) : IO Unit := do
  for c in crates do
    emitOneCrate projectDir c forceEmit

/-- Lake targets for `prove`: generated program + hand-written specs (matches `programs/`). -/
private def proveTargets (crates : Array Crate) : Array String :=
  crates.foldl (init := #[]) fun acc c =>
    let pascal := c.leanDir.fileName.getD ""
    acc.push s!"Project.{pascal}.Program" |>.push s!"Project.{pascal}.Spec"

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
  let targets := proveTargets crates
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
  IO.FS.createDirAll projectDir
  IO.println s!"==> scaffolding template into {projectDir}"
  let templateFiles ← loadTemplateFiles
  for (rel, content) in templateFiles do
    let content := if rel = "lean/lakefile.toml" then scaffoldedLakefile else content
    writeFile (projectDir / rel) content
  IO.println "==> cargo check"
  runOrDie "cargo" #["check"] (cwd := some (projectDir / "rust"))
  let leanDir := projectDir / "lean"
  IO.println "==> lake update"
  runOrDie "lake" #["update"] (cwd := some leanDir)
  IO.println "==> lake exe cache get"
  runOrDie "lake" #["exe", "cache", "get"] (cwd := some leanDir)
  IO.println "==> lake build (verifying template proofs)"
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

def runAdd (p : Parsed) : IO UInt32 := do
  cmdAdd (p.positionalArg! "crate" |>.as! String)
  pure 0

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

def addCmd : Cmd := `[Cli|
  add VIA runAdd;
  "Add one crate to the current project (run from project root)."

  ARGS:
    crate : String; "Crate name in snake_case (e.g. my_crate)."
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
  "Transpile program.wat → Program.lean for selected crates. [--force-emit]"

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
    addCmd;
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
