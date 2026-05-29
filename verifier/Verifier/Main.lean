import Verifier.Emit
import Verifier.Path
import Verifier.Extract
import Interpreter.Wasm.Decoder.Wat
import Cli

/-!
# `verifier` CLI

```
verifier new   <project-path>
verifier check [--force-emit]
```

`new`   — scaffolds a fixed-shape project at `<project-path>` from the
          baked-in template (a rust cargo workspace + a lean project).
`check` — must be run from the project root. Builds every crate in the
          rust workspace to `rust/build/<crate>/program.{wasm,wat}`,
          re-emits `lean/Project/<Crate>/Program.lean` when the wasm
          changed (or `--force-emit`), then runs `lake build`.

The mapping between rust crates and lean modules is by convention:
crate `foo_bar` ↔ lean module `Project.FooBar` (snake_case →
PascalCase). No `verifier.toml` or `origin.toml` needed.
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

private def runChecked (cmd : String) (args : Array String)
    (cwd : Option FilePath := none) : IO Bool := do
  let child ← IO.Process.spawn {
    cmd := cmd, args := args, cwd := cwd,
    stdin := .inherit, stdout := .inherit, stderr := .inherit
  }
  pure ((← child.wait) = 0)

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

/-- `true` iff `a` is newer than `b`, or `b` does not exist. -/
private def isNewer (a b : FilePath) : IO Bool := do
  if ¬ (← System.FilePath.pathExists b) then return true
  let ma ← a.metadata
  let mb ← b.metadata
  return ma.modified > mb.modified

-- ----------------------------------------------------------------------------
-- Embedded template
-- ----------------------------------------------------------------------------

/-- Files of the bundled template, as `(relative path, contents)` pairs.
The files themselves live under `verifier/template/` and are inlined at
compile time via `include_str`. -/
private def templateFiles : List (String × String) := [
  ("rust/Cargo.toml",
    include_str "../template/rust/Cargo.toml"),
  ("rust/.cargo/config.toml",
    include_str "../template/rust/.cargo/config.toml"),
  ("rust/.gitignore",
    include_str "../template/rust/.gitignore"),
  ("rust/justfile",
    include_str "../template/rust/justfile"),
  ("rust/is_even/Cargo.toml",
    include_str "../template/rust/is_even/Cargo.toml"),
  ("rust/is_even/src/lib.rs",
    include_str "../template/rust/is_even/src/lib.rs"),
  ("rust/is_even/src/exports.rs",
    include_str "../template/rust/is_even/src/exports.rs"),
  ("rust/is_odd/Cargo.toml",
    include_str "../template/rust/is_odd/Cargo.toml"),
  ("rust/is_odd/src/lib.rs",
    include_str "../template/rust/is_odd/src/lib.rs"),
  ("rust/is_odd/src/exports.rs",
    include_str "../template/rust/is_odd/src/exports.rs"),
  ("lean/lean-toolchain",
    include_str "../template/lean/lean-toolchain"),
  ("lean/lakefile.toml",
    include_str "../template/lean/lakefile.toml"),
  ("lean/.gitignore",
    include_str "../template/lean/.gitignore"),
  ("lean/Project.lean",
    include_str "../template/lean/Project.lean"),
  ("lean/Project/IsEven/Program.lean",
    include_str "../template/lean/Project/IsEven/Program.lean"),
  ("lean/Project/IsEven/Spec.lean",
    include_str "../template/lean/Project/IsEven/Spec.lean"),
  ("lean/Project/IsEven/Proof.lean",
    include_str "../template/lean/Project/IsEven/Proof.lean"),
  ("lean/Project/IsEven/Run.lean",
    include_str "../template/lean/Project/IsEven/Run.lean"),
  ("lean/Project/IsOdd/Program.lean",
    include_str "../template/lean/Project/IsOdd/Program.lean"),
  ("lean/Project/IsOdd/Spec.lean",
    include_str "../template/lean/Project/IsOdd/Spec.lean"),
  ("lean/Project/IsOdd/Proof.lean",
    include_str "../template/lean/Project/IsOdd/Proof.lean"),
  ("lean/Project/IsOdd/Run.lean",
    include_str "../template/lean/Project/IsOdd/Run.lean")
]

-- ----------------------------------------------------------------------------
-- `check`
-- ----------------------------------------------------------------------------

/-- One rust crate in the workspace, paired with its lean module dir. -/
structure Crate where
  /-- Crate name on disk (snake_case). -/
  name      : String
  /-- Absolute path to the crate directory. -/
  rustDir   : FilePath
  /-- Absolute path to the matching lean module directory. -/
  leanDir   : FilePath

/-- Discover crates by listing subdirectories of `rust/` that contain a
`Cargo.toml`. Faster and simpler than parsing `[workspace].members`. -/
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

private def emitProgramFile (c : Crate) (m : Wasm.Module) : IO Unit := do
  IO.FS.createDirAll c.leanDir
  let modName := s!"Project.{snakeToPascal c.name}"
  let body :=
    String.intercalate "\n" [
      "/-",
      "  AUTO-GENERATED by `lake exe verifier check`. Do not edit by hand.",
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

/-- Compute `RUSTFLAGS` with `--remap-path-prefix` entries that strip
machine-specific absolute paths (rustc sysroot, CARGO_HOME, $HOME) from
the produced wasm. Without this, panic location strings embedded in the
binary differ between CI runners and developer machines, even when the
rustc version is pinned. -/
private def reproducibleRustflags (rustDir : FilePath) : IO String := do
  -- rustc's sysroot is resolved from the workspace dir so we pick up
  -- the `rust-toolchain.toml`-pinned version rather than the global
  -- default.
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
  -- Order matters: rustc applies remaps in declaration order and uses
  -- the **last** matching prefix, so list from least- to most-specific.
  -- That way `$HOME/.cargo/...` gets `/cargo-home/...` (specific) rather
  -- than `/home/.cargo/...` (general), and a path inside the sysroot
  -- gets `/rustc-sysroot/...` rather than `/home/...`.
  let mut remaps : Array String := #[]
  if !home.isEmpty then
    remaps := remaps.push s!"--remap-path-prefix={home}=/home"
  if !cargoHome.isEmpty then
    remaps := remaps.push s!"--remap-path-prefix={cargoHome}=/cargo-home"
  if !sysroot.isEmpty then
    remaps := remaps.push s!"--remap-path-prefix={sysroot}=/rustc-sysroot"
  pure (String.intercalate " " remaps.toList)

private def buildAndEmit
    (projectDir : FilePath) (crates : Array Crate) (forceEmit : Bool) : IO Unit := do
  -- Build all crates in one cargo invocation (faster, shares the target/).
  IO.println "==> cargo build-wasm (workspace)"
  let rustDir := projectDir / "rust"
  let rustflags ← reproducibleRustflags rustDir
  runOrDie "cargo" #["build-wasm"]
    (cwd := some rustDir)
    (env := #[("RUSTFLAGS", some rustflags)])
  -- Per-crate: copy wasm, dump wat, decode + emit when stale.
  let buildRoot := projectDir / "rust" / "build"
  let cargoTarget := projectDir / "rust" / "target" / "wasm32-unknown-unknown" / "release"
  for c in crates do
    let outDir := buildRoot / c.name
    IO.FS.createDirAll outDir
    let src := cargoTarget / s!"{c.name}.wasm"
    unless ← System.FilePath.pathExists src do
      die s!"expected {src} after cargo build-wasm but it is missing"
    let wasmDst := outDir / "program.wasm"
    -- Strip non-essential custom sections (notably `producers` and
    -- `target_features`) so the committed wasm is reproducible across
    -- rustc versions. `wasm-tools strip` keeps `name`/`component-type`/
    -- `dylink.0` by default — adequate for our reasoning needs. We
    -- strip to a tmp path first so the existing committed wasm is only
    -- overwritten when the stripped bytes actually changed (this keeps
    -- mtimes tracking real updates).
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
    let programLean := c.leanDir / "Program.lean"
    let stale := forceEmit ∨ (← isNewer wasmDst programLean)
    if stale then
      match Wasm.Decoder.Wat.decode watText with
      | .error e => die s!"{c.name}: wat decoder rejected the module: {e}"
      | .ok m    =>
        emitProgramFile c m
        IO.println s!"    emitted {programLean}"
    else
      IO.println s!"    {programLean} is up to date"

/-- `lake build`, counting `sorry` warnings. -/
private def lakeBuildCount (leanDir : FilePath) : IO (Bool × Nat) := do
  IO.println s!"==> lake build ({leanDir})"
  let out ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := some leanDir
  }
  IO.print out.stdout
  IO.eprint out.stderr
  let combined := out.stdout ++ "\n" ++ out.stderr
  let sorries := (combined.splitOn "declaration uses 'sorry'").length - 1
  pure (out.exitCode = 0, sorries)

private def checkAt (projectDir : FilePath) (forceEmit : Bool) (noBuild : Bool) : IO Bool := do
  let crates ← discoverCrates projectDir
  if crates.isEmpty then
    die s!"{projectDir}/rust has no crate subdirectories"
  IO.println s!"==> {crates.size} crate(s): {String.intercalate ", " (crates.toList.map (·.name))}"
  buildAndEmit projectDir crates forceEmit
  if noBuild then
    IO.println ""
    IO.println s!"==> {crates.size} crate(s) emitted ({String.intercalate ", " (crates.toList.map (·.name))}); skipping `lake build` (--no-build)"
    pure true
  else
    let (ok, sorries) ← lakeBuildCount (projectDir / "lean")
    IO.println ""
    IO.println s!"==> {crates.size} crate(s), {if ok then "lake build OK" else "lake build FAILED"}, {sorries} sorry warning(s)"
    pure ok

private def cmdCheck (forceEmit : Bool) (noBuild : Bool) : IO Unit := do
  let projectDir ← absNormalize (← IO.currentDir)
  unless ← checkAt projectDir forceEmit noBuild do IO.Process.exit 1

-- ----------------------------------------------------------------------------
-- `new`
-- ----------------------------------------------------------------------------

private def cmdNew (projectPathIn : String) : IO Unit := do
  let projectDir ← absNormalize ⟨projectPathIn⟩
  if ← System.FilePath.pathExists projectDir then
    let entries ← (projectDir.readDir : IO _)
    unless entries.isEmpty do
      die s!"{projectDir} already exists and is not empty"
  IO.FS.createDirAll projectDir
  IO.println s!"==> scaffolding template into {projectDir}"
  for (rel, content) in templateFiles do
    writeFile (projectDir / rel) content
  IO.println "==> cargo check"
  runOrDie "cargo" #["check"] (cwd := some (projectDir / "rust"))
  -- Fetch lean deps (CodeLib pulls in mathlib) and prime the mathlib
  -- olean cache before building. Doing this here, instead of relying on
  -- the implicit fetch inside `lake build`, lets us pick up cached
  -- mathlib oleans and skip a multi-minute recompile.
  let leanDir := projectDir / "lean"
  IO.println "==> lake update"
  runOrDie "lake" #["update"] (cwd := some leanDir)
  IO.println "==> lake exe cache get"
  runOrDie "lake" #["exe", "cache", "get"] (cwd := some leanDir)
  -- Hand off to the full check pipeline: it builds wasm, emits the real
  -- Program.lean for every crate, then runs `lake build`. The bundled
  -- Proof.lean files reference `func0` etc., so we can't skip emit
  -- before building.
  IO.println "==> running initial `verifier check`"
  unless ← checkAt projectDir false false do
    die "initial `verifier check` failed"
  IO.println s!"==> done. Project ready at {projectDir}"

-- ----------------------------------------------------------------------------
-- CLI plumbing
-- ----------------------------------------------------------------------------

open Cli

def runNew (p : Parsed) : IO UInt32 := do
  let path := p.positionalArg! "projectPath" |>.as! String
  cmdNew path
  pure 0

def runCheck (p : Parsed) : IO UInt32 := do
  cmdCheck (p.hasFlag "force-emit") (p.hasFlag "no-build")
  pure 0

/-- Locate the bundled `report/` Astro project relative to the verifier
binary. The binary lives at `<verifier-root>/.lake/build/bin/verifier`,
and the report project at `<verifier-root>/report/`. -/
private def locateReportDir : IO FilePath := do
  let app ← IO.appPath
  -- app = <verifier-root>/.lake/build/bin/verifier
  --       parents:        bin/  build/  .lake/  <verifier-root>
  let some verifierRoot := app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | die s!"could not locate verifier root from {app}"
  let reportDir := verifierRoot / "report"
  unless ← System.FilePath.pathExists (reportDir / "package.json") do
    die s!"bundled report project not found at {reportDir} (resolved from {app})"
  absNormalize reportDir

def runReport (p : Parsed) : IO UInt32 := do
  let projectDir ← absNormalize (← IO.currentDir)
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
  -- Phase 1: extract.
  IO.println s!"==> verifier extract → {extractedDir}"
  Verifier.Extract.run projectDir extractedDir
  -- Phase 2: build the Astro static site.
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
  let projectDir ← absNormalize (← IO.currentDir)
  let outFlag : String := if p.hasFlag "out" then
    p.flag! "out" |>.as! String
  else
    "extracted"
  let outDir ← absNormalize ⟨outFlag⟩
  Verifier.Extract.run projectDir outDir
  pure 0

def newCmd : Cmd := `[Cli|
  «new» VIA runNew;
  "Scaffold a new verification project from the bundled template."

  ARGS:
    projectPath : String; "Directory to create (must not already exist or be empty)."
]

def checkCmd : Cmd := `[Cli|
  «check» VIA runCheck;
  "Build wasm + re-emit Program.lean + run `lake build`. Must be run from the project root."

  FLAGS:
    "force-emit"; "Re-emit Program.lean even if the wasm hasn't changed."
    "no-build";   "Build wasm + emit Program.lean only; skip the final `lake build`."
]

def reportCmd : Cmd := `[Cli|
  «report» VIA runReport;
  "Run `verifier extract` then build the static HTML report. Must be run from the project root."

  FLAGS:
    "extracted"  : String; "Directory for `extract` JSON artifacts (default: ./extracted)."
    "out"        : String; "Directory for the built static site (default: ./out)."
]

def extractCmd : Cmd := `[Cli|
  «extract» VIA runExtract;
  "Emit one JSON artifact per crate at <DIR>/<crate>.json (default DIR=./extracted/). Must be run from the project root."

  FLAGS:
    "out" : String; "Output directory (default: ./extracted)."
]

def mainCmd : Cmd := `[Cli|
  verifier NOOP; ["0.1.0"]
  "Rust → wasm → Lean verification driver."

  SUBCOMMANDS:
    newCmd;
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
