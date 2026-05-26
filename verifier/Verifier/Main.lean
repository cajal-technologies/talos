import Verifier.Emit
import Verifier.Config
import Verifier.Discovery
import Verifier.Extract
import Verifier.RustExtract
import Verifier.Report

/-!
# `verifier` CLI entry point

```
verifier new    <rust-path> <lean-path> <subfolder>
verifier check  [path] [--no-build]
verifier report [--out <dir>]
```

* `new` — scaffold metadata (`verifier.toml`, `origin.toml`), an empty
  lean subfolder with `Spec.lean` / `Proofs.lean`, and a fresh lean
  project if needed. Idempotent on a matching pair.
* `check` — with a path, operate on that one project; with no path,
  recursively discover every `verifier.toml` under the current
  directory and operate on all of them. Builds wasm, emits
  `Program.lean`, runs `lake build` once per lean project. Errors are
  accumulated and reported at the end.
* `report` — discovers all, runs the full pipeline, writes an HTML
  report directory. **Not yet implemented** in this version.
-/

open System (FilePath)

namespace Verifier

-- ----------------------------------------------------------------------------
-- String helpers (List Char-flavoured, stable across toolchain churn)
-- ----------------------------------------------------------------------------

private def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

private def strTrim (s : String) : String :=
  let cs := s.toList.dropWhile isSpace
  String.ofList (cs.reverse.dropWhile isSpace).reverse

private def strTakeWhile (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.takeWhile p)

private def strDropWhile (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.dropWhile p)

private def strDrop (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

private def strCapitalise (s : String) : String :=
  match s.toList with
  | []      => s
  | c :: cs => String.ofList (c.toUpper :: cs)

-- ----------------------------------------------------------------------------
-- CLI plumbing
-- ----------------------------------------------------------------------------

private def usage : String :=
  "Usage:\n" ++
  "  lake exe verifier new        <rust-path> <lean-path> <subfolder>\n" ++
  "                               [--codelib <path>] [--codelib-rev <rev>]\n" ++
  "  lake exe verifier check      [path] [--no-build]\n" ++
  "  lake exe verifier report     [--out <dir>] [--no-build]\n\n" ++
  "Scaffolding defaults to CodeLib from github.com/cajal-technologies/talos\n" ++
  "(subDir=codelib, rev=main). Override with --codelib-rev <rev>, or use a\n" ++
  "local checkout via --codelib <path> or the TALOS_CODELIB env var."

private def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

private def warn (msg : String) : IO Unit :=
  IO.eprintln s!"warning: {msg}"

-- ----------------------------------------------------------------------------
-- Path utilities
-- ----------------------------------------------------------------------------

private def normalize (p : FilePath) : FilePath :=
  let parts := p.components
  let rev := parts.foldl (init := ([] : List String)) fun acc c =>
    match c, acc with
    | ".", _              => acc
    | "..", h :: t        => if h ≠ ".." && h ≠ "" then t else c :: acc
    | _, _                => c :: acc
  ⟨System.FilePath.pathSeparator.toString.intercalate rev.reverse⟩

private def relativeTo («from» «to» : FilePath) : FilePath :=
  let f := «from».components.filter (· ≠ "")
  let t := «to».components.filter (· ≠ "")
  let rec strip : List String → List String → List String × List String
    | a :: as, b :: bs => if a = b then strip as bs else (a :: as, b :: bs)
    | xs,      ys      => (xs, ys)
  let (upFrom, downTo) := strip f t
  let parts := upFrom.map (fun _ => "..") ++ downTo
  if parts.isEmpty then ⟨"."⟩
  else ⟨System.FilePath.pathSeparator.toString.intercalate parts⟩

private def absNormalize (p : FilePath) : IO FilePath := do
  let abs ← if p.isAbsolute then pure p else
    let cwd ← IO.currentDir
    pure (cwd / p)
  pure (normalize abs)

private def writeFile (p : FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile p content

-- ----------------------------------------------------------------------------
-- Subprocess helpers
-- ----------------------------------------------------------------------------

private structure RunOpts where
  cmd     : String
  args    : Array String
  cwd     : Option FilePath := none
  inherit : Bool := true

private def runOrDie (o : RunOpts) : IO Unit := do
  let stdin  : IO.Process.Stdio := if o.inherit then .inherit else .null
  let stdout : IO.Process.Stdio := if o.inherit then .inherit else .piped
  let stderr : IO.Process.Stdio := if o.inherit then .inherit else .piped
  let child ← IO.Process.spawn {
    cmd := o.cmd, args := o.args, cwd := o.cwd,
    stdin := stdin, stdout := stdout, stderr := stderr
  }
  let code ← child.wait
  if code ≠ 0 then
    die s!"`{o.cmd} {String.intercalate " " o.args.toList}` failed with exit code {code}"

/-- Run a command, returning whether it succeeded; never aborts. -/
private def runChecked (o : RunOpts) : IO Bool := do
  let child ← IO.Process.spawn {
    cmd := o.cmd, args := o.args, cwd := o.cwd,
    stdin := .inherit, stdout := .inherit, stderr := .inherit
  }
  let code ← child.wait
  pure (code = 0)

private def captureStdout (cmd : String) (args : Array String)
    (cwd : Option FilePath := none) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd }
  if out.exitCode ≠ 0 then
    die s!"`{cmd}` failed with exit code {out.exitCode}:\n{out.stderr}"
  pure out.stdout

-- ----------------------------------------------------------------------------
-- Cargo
-- ----------------------------------------------------------------------------

/-- Extract the `[package].name` field from a Cargo.toml. -/
private def cargoCrateName (cargoToml : FilePath) : IO String := do
  let txt ← IO.FS.readFile cargoToml
  let lines := txt.splitOn "\n"
  let mut inPkg := false
  for raw in lines do
    let line := strTrim raw
    if line.startsWith "[" then
      inPkg := (line = "[package]")
      continue
    if inPkg && line.startsWith "name" && line.contains '=' then
      let after := strTrim (strDrop (strDropWhile line (· ≠ '=')) 1)
      if after.startsWith "\"" then
        let body := strDrop after 1
        return strTakeWhile body (· ≠ '"')
  die s!"could not parse `[package].name` from {cargoToml}"

-- ----------------------------------------------------------------------------
-- Resolved project view
-- ----------------------------------------------------------------------------

/-- A resolved (rust, lean) project pair. -/
structure Pair where
  /-- Absolute, normalised path to the rust crate directory (contains
  `Cargo.toml` and `verifier.toml`). -/
  rustDir            : FilePath
  /-- Absolute, normalised path to the lean project root (contains
  `lakefile.toml`). -/
  leanDir            : FilePath
  /-- Verification subfolder *string* — relative to `leanDir`, may
  contain `/`. -/
  verificationFolder : String
  /-- Build configuration from `verifier.toml`. -/
  build              : BuildConfig

def Pair.subfolderDir (p : Pair) : FilePath := p.leanDir / p.verificationFolder

def subfolderToModule (sub : String) : String :=
  let parts := (sub.splitOn "/").filter (·.length > 0)
  String.intercalate "." parts

/-- Where the scaffolded lakefile points to find CodeLib. -/
inductive CodelibSource
  /-- A local checkout (absolute path). Lakefile gets `path = "..."`. -/
  | localDir : FilePath → CodelibSource
  /-- A git remote. Lakefile gets `git = "..."`, `subDir = "..."`, `rev = "..."`. -/
  | git : (url subDir rev : String) → CodelibSource
  deriving Inhabited

/-- Default git source for CodeLib: the `codelib/` subdirectory of the
public Talos repo. -/
def defaultCodelibGit : CodelibSource :=
  .git "https://github.com/cajal-technologies/talos" "codelib" "main"

/-- Resolve which CodeLib the scaffolded project should depend on.

The default is the public GitHub remote — projects scaffolded by
`verifier new` are self-contained and don't need a Talos checkout on
the user's machine. Opt into a local checkout with:

1. `--codelib <path>` CLI flag.
2. `TALOS_CODELIB` environment variable.

Both require the path to contain a `lean-toolchain`. `--codelib-rev`
overrides the pinned git rev (default `main`). -/
private def resolveCodelibSource
    (override : Option String) (gitRev : Option String) : IO CodelibSource := do
  let tryDir (d : FilePath) : IO (Option FilePath) := do
    if ← System.FilePath.pathExists (d / "lean-toolchain") then
      pure (some (← absNormalize d))
    else pure none
  if let some d := override then
    match ← tryDir ⟨d⟩ with
    | some r => return .localDir r
    | none   => die s!"--codelib {d}: no `lean-toolchain` here"
  if let some env ← IO.getEnv "TALOS_CODELIB" then
    match ← tryDir ⟨env⟩ with
    | some r => return .localDir r
    | none   => die s!"TALOS_CODELIB={env}: no `lean-toolchain` here"
  match defaultCodelibGit with
  | .git url sub _   => return .git url sub (gitRev.getD "main")
  | .localDir _      => unreachable!

/-- Read CodeLib's `lean-toolchain`. For a local source we just read
the file. For a git source we shell out to `curl` against
`raw.githubusercontent.com`. -/
private def codelibLeanToolchain : CodelibSource → IO String
  | .localDir d => IO.FS.readFile (d / "lean-toolchain")
  | .git url sub rev => do
    -- Convert `https://github.com/USER/REPO` into the raw form.
    let ghPrefix := "https://github.com/"
    unless url.startsWith ghPrefix do
      die s!"don't know how to fetch lean-toolchain from non-GitHub URL: {url}"
    let slug := (url.drop ghPrefix.length).toString
    let rawUrl := s!"https://raw.githubusercontent.com/{slug}/{rev}/{sub}/lean-toolchain"
    let out ← IO.Process.output { cmd := "curl", args := #["-sfL", rawUrl] }
    if out.exitCode ≠ 0 then
      die s!"curl failed fetching {rawUrl}: {out.stderr}"
    pure out.stdout

private def resolvePairFromRust (rustDir : FilePath) : IO Pair := do
  let v ← Toml.readVerifier (rustDir / "verifier.toml")
  let leanDir ← absNormalize (rustDir / v.leanProject)
  pure {
    rustDir := rustDir, leanDir := leanDir,
    verificationFolder := v.verificationFolder,
    build := v.build
  }

private def resolvePairFromSubfolder (subDir : FilePath) : IO Pair := do
  let o ← Toml.readOrigin (subDir / "origin.toml")
  let mut leanRoot : Option FilePath := none
  let mut cur : FilePath := subDir
  for _ in [:32] do
    if ← System.FilePath.pathExists (cur / "lakefile.toml") then
      leanRoot := some cur
      break
    match cur.parent with
    | some p => cur := p
    | none   => break
  let some leanDir := leanRoot
    | die s!"{subDir}: could not find an ancestor `lakefile.toml`"
  let rustDir ← absNormalize (subDir / o.rustProject)
  let leanDirAbs ← absNormalize leanDir
  let subAbs ← absNormalize subDir
  let verificationFolder := (relativeTo leanDirAbs subAbs).toString
  -- We need the build config; read it from the rust-side verifier.toml.
  let v ← Toml.readVerifier (rustDir / "verifier.toml")
  pure {
    rustDir := rustDir, leanDir := leanDirAbs,
    verificationFolder := verificationFolder,
    build := v.build
  }

/-- Resolve whichever marker the user pointed at. -/
private def resolvePair (path : FilePath) : IO Pair := do
  let abs ← absNormalize path
  if ← System.FilePath.pathExists (abs / "verifier.toml") then
    resolvePairFromRust abs
  else if ← System.FilePath.pathExists (abs / "origin.toml") then
    resolvePairFromSubfolder abs
  else
    die s!"{path}: no `verifier.toml` or `origin.toml` here — run `verifier new` first"

-- ----------------------------------------------------------------------------
-- Lean project scaffolding
-- ----------------------------------------------------------------------------

private def libName (leanDir : FilePath) : IO String := do
  let lake ← IO.FS.readFile (leanDir / "lakefile.toml")
  for raw in lake.splitOn "\n" do
    let line := strTrim raw
    if line.startsWith "name" && line.contains '=' then
      let after := strTrim (strDrop (strDropWhile line (· ≠ '=')) 1)
      if after.startsWith "\"" then
        return strTakeWhile (strDrop after 1) (· ≠ '"')
  die s!"{leanDir}/lakefile.toml: missing top-level `name = \"…\"`"

private def leanLibName (leanDir : FilePath) : IO String := do
  let lake ← IO.FS.readFile (leanDir / "lakefile.toml")
  let lines := lake.splitOn "\n"
  let mut inLib := false
  for raw in lines do
    let line := strTrim raw
    if line = "[[lean_lib]]" then inLib := true; continue
    if line.startsWith "[" then inLib := false; continue
    if inLib && line.startsWith "name" && line.contains '=' then
      let after := strTrim (strDrop (strDropWhile line (· ≠ '=')) 1)
      if after.startsWith "\"" then
        return strTakeWhile (strDrop after 1) (· ≠ '"')
  libName leanDir

private def appendImportLine (rootFile : FilePath) (importLine : String) : IO Unit := do
  let existing ← if ← System.FilePath.pathExists rootFile then IO.FS.readFile rootFile else pure ""
  let lines := existing.splitOn "\n"
  if lines.contains importLine then
    return ()
  let trailing := if existing.isEmpty || existing.endsWith "\n" then "" else "\n"
  IO.FS.writeFile rootFile (existing ++ trailing ++ importLine ++ "\n")

private def scaffoldLeanProject (leanDir : FilePath) (src : CodelibSource) : IO Unit := do
  let toolchain ← codelibLeanToolchain src
  let pkgName :=
    match leanDir.fileName with
    | some s => if s.isEmpty then "Verification" else strCapitalise s
    | none   => "Verification"
  let requireBody := match src with
    | .localDir d   => [s!"path = \"{relativeTo leanDir d}\""]
    | .git url sub rev =>
      [ s!"git = \"{url}\"",
        s!"subDir = \"{sub}\"",
        s!"rev = \"{rev}\"" ]
  IO.FS.createDirAll leanDir
  writeFile (leanDir / "lean-toolchain") toolchain
  writeFile (leanDir / "lakefile.toml") <| String.intercalate "\n" <|
    [ s!"name = \"{pkgName}\"",
      "version = \"0.1.0\"",
      s!"defaultTargets = [\"{pkgName}\"]",
      "",
      "[[require]]",
      "name = \"CodeLib\"" ]
    ++ requireBody
    ++ [ "",
         "[[lean_lib]]",
         s!"name = \"{pkgName}\"",
         "" ]
  writeFile (leanDir / s!"{pkgName}.lean") s!"import {pkgName}.Basic\n"
  writeFile (leanDir / pkgName / "Basic.lean") "import CodeLib\n"

-- ----------------------------------------------------------------------------
-- `new`
-- ----------------------------------------------------------------------------

private def specStub (subfolder : String) : String :=
  let mod := subfolderToModule subfolder
  String.intercalate "\n" [
    s!"import {mod}.Program",
    "",
    "/-!",
    "Write your specification *statements* here as `def MyProp : Prop`",
    "definitions. Keep proofs in the sibling `Proofs.lean`.",
    "-/",
    "",
    s!"namespace {mod}.Spec",
    "",
    "open Wasm",
    "",
    "-- /-- Informal: TODO. -/",
    "-- def MyExample : Prop :=",
    "--   ∀ (initial : Store), TerminatesWith «module» 0 initial [] (fun _ _ => True)",
    "",
    s!"end {mod}.Spec",
    ""
  ]

private def proofsStub (subfolder : String) : String :=
  let mod := subfolderToModule subfolder
  String.intercalate "\n" [
    s!"import {mod}.Spec",
    "",
    "/-!",
    "Proofs of the statements declared in `Spec.lean`.",
    "-/",
    "",
    s!"namespace {mod}.Proofs",
    "",
    s!"open {mod}.Spec",
    "",
    "-- theorem my_example : MyExample := by sorry",
    "",
    s!"end {mod}.Proofs",
    ""
  ]

private def codelibDescribe : CodelibSource → String
  | .localDir d => s!"local path {d}"
  | .git url sub rev => s!"git {url} (subDir={sub}, rev={rev})"

private def cmdNew (rustPathIn leanPathIn subfolder : String)
    (codelibOverride codelibRev : Option String) : IO Unit := do
  let rustDir ← absNormalize rustPathIn
  let leanDir ← absNormalize leanPathIn
  let cargoToml := rustDir / "Cargo.toml"
  unless ← System.FilePath.pathExists cargoToml do
    die s!"{rustDir}: no Cargo.toml here (verifier does not scaffold rust crates)"
  -- 1. Lean project: scaffold if missing.
  let codelib ← resolveCodelibSource codelibOverride codelibRev
  if ¬ (← System.FilePath.pathExists (leanDir / "lakefile.toml")) then
    IO.println s!"==> scaffolding lean project at {leanDir} (codelib: {codelibDescribe codelib})"
    scaffoldLeanProject leanDir codelib
  else
    let expected ← codelibLeanToolchain codelib
    let actual ← IO.FS.readFile (leanDir / "lean-toolchain")
    if strTrim expected ≠ strTrim actual then
      die s!"{leanDir}/lean-toolchain disagrees with codelib ({codelibDescribe codelib}):\n  expected: {strTrim expected}\n  actual:   {strTrim actual}"
  -- The verification folder must live under `<libName>/...` so Lake's
  -- module resolver can find it; if the user passed a bare path (e.g.
  -- `Foo`), prepend the lib name to give us `<Lib>/Foo`.
  let lib ← leanLibName leanDir
  let vFolder :=
    if subfolder = lib || subfolder.startsWith (lib ++ "/") then subfolder
    else lib ++ "/" ++ subfolder
  -- 2. Subfolder + origin.toml + Spec.lean + Proofs.lean.
  let subDir := leanDir / vFolder
  IO.FS.createDirAll subDir
  let originPath := subDir / "origin.toml"
  let rustRel := (relativeTo subDir rustDir).toString
  if ← System.FilePath.pathExists originPath then
    let existing ← Toml.readOrigin originPath
    if existing.rustProject ≠ rustRel then
      die s!"{originPath} already exists and points elsewhere (got `{existing.rustProject}`, want `{rustRel}`)"
  else
    writeFile originPath (Toml.renderOrigin { rustProject := rustRel })
  let specPath := subDir / "Spec.lean"
  unless ← System.FilePath.pathExists specPath do
    writeFile specPath (specStub vFolder)
  let proofsPath := subDir / "Proofs.lean"
  unless ← System.FilePath.pathExists proofsPath do
    writeFile proofsPath (proofsStub vFolder)
  -- 3. verifier.toml on the rust side.
  let verifierPath := rustDir / "verifier.toml"
  let leanRel := (relativeTo rustDir leanDir).toString
  if ← System.FilePath.pathExists verifierPath then
    let existing ← Toml.readVerifier verifierPath
    if existing.leanProject ≠ leanRel || existing.verificationFolder ≠ vFolder then
      die s!"{verifierPath} already exists and points elsewhere (got `{existing.leanProject}` / `{existing.verificationFolder}`, want `{leanRel}` / `{vFolder}`)"
  else
    writeFile verifierPath <| Toml.renderVerifier
      { leanProject := leanRel, verificationFolder := vFolder, build := {} }
  -- 4. Wire `import {Mod}.Proofs` into the lean library root.
  let rootFile := leanDir / s!"{lib}.lean"
  appendImportLine rootFile s!"import {subfolderToModule vFolder}.Proofs"
  IO.println s!"==> verifier new wrote {verifierPath}, {originPath}, {specPath}, {proofsPath}"

-- ----------------------------------------------------------------------------
-- `check`
-- ----------------------------------------------------------------------------

private def emitProgramFile
    (pair : Pair) (m : Wasm.Module) (watText : String) : IO Unit := do
  let sub := pair.subfolderDir
  IO.FS.createDirAll sub
  let modName := subfolderToModule pair.verificationFolder
  let bodiesBlock := Emit.funcBodies m
  let moduleExpr := Emit.module m
  let watRelPath := pair.verificationFolder ++ "/module.wat"
  let driftBlock := Emit.driftCheck watRelPath watText.hash
  let lines := [
    "/-",
    "  AUTO-GENERATED by `lake exe verifier check`.",
    "  Do not edit by hand. Edit Spec.lean (sibling) for proofs.",
    "  The sibling `module.wat` is the source of truth; the drift check at",
    "  the bottom of this file errors at elaboration time if it has changed",
    "  without a corresponding re-emit.",
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
    bodiesBlock,
    "",
    "def «module» : Wasm.Module :=",
    moduleExpr,
    "",
    driftBlock,
    "",
    s!"end {modName}",
    ""
  ]
  writeFile (sub / "Program.lean") (String.intercalate "\n" lines)

/-- Build wasm, emit `module.wat` + `Program.lean` for one pair. Does
NOT run `lake build` — that is grouped at the `checkMany` level. -/
private def buildAndEmit (pair : Pair) : IO Unit := do
  let cargoToml := pair.rustDir / "Cargo.toml"
  unless ← System.FilePath.pathExists cargoToml do
    throw <| IO.userError s!"{pair.rustDir}: no Cargo.toml here (origin.toml/verifier.toml is stale)"
  let crate ← cargoCrateName cargoToml
  IO.println s!"==> {pair.rustDir} → {pair.leanDir}/{pair.verificationFolder} (crate `{crate}`)"
  -- 1. Wasm build (custom command or default).
  let cmdString := pair.build.effectiveCommand
  match splitCommand cmdString with
  | none => throw <| IO.userError s!"{pair.rustDir}: empty build_command"
  | some (prog, args) =>
    runOrDie { cmd := prog, args := args, cwd := some pair.rustDir }
  -- 2. Locate the wasm artifact.
  let artTemplate := pair.build.effectiveArtifact
  let artRel : FilePath := ⟨substituteCrate artTemplate crate⟩
  let wasmFile :=
    if artRel.isAbsolute then artRel else pair.rustDir / artRel
  unless ← System.FilePath.pathExists wasmFile do
    throw <| IO.userError s!"expected wasm artifact at {wasmFile} but it is missing"
  -- 3. Strip + print to wat.
  let sub := pair.subfolderDir
  IO.FS.createDirAll sub
  let strippedWasm := sub / ".module.stripped.wasm"
  runOrDie {
    cmd := "wasm-tools",
    args := #["strip", "--all", wasmFile.toString, "-o", strippedWasm.toString]
  }
  let watText ← captureStdout "wasm-tools" #["print", strippedWasm.toString]
  writeFile (sub / "module.wat") watText
  IO.FS.removeFile strippedWasm
  -- 4. Decode + emit.
  match Wasm.Decoder.Wat.decode watText with
  | .error e => throw <| IO.userError s!"wat decoder rejected the generated module: {e}"
  | .ok m    => emitProgramFile pair m watText

/-- Wrap the extractor's raw `{"namespace", "specs", "proofs"}` JSON
with project-level metadata. -/
private def wrapSidecar (pair : Pair) (crate : String) (buildOk : Bool)
    (extractorJson rustExportsJson : String) : String :=
  let extractor := extractorJson.trimAscii.toString
  let inner :=
    if extractor.isEmpty then "{\"namespace\":\"\",\"specs\":[],\"proofs\":[]}"
    else extractor
  -- Surface project metadata as a top-level object, then merge the
  -- extractor body via a `"lean"` key (keeps both layers easy to grep).
  let okStr := if buildOk then "true" else "false"
  let lbrace := "{"
  let rbrace := "}"
  String.intercalate "\n" [
    lbrace,
    "  \"project\": " ++ lbrace,
    s!"    \"rustDir\":   \"{pair.rustDir}\",",
    s!"    \"leanDir\":   \"{pair.leanDir}\",",
    s!"    \"subfolder\": \"{pair.verificationFolder}\",",
    s!"    \"crate\":     \"{crate}\"",
    "  " ++ rbrace ++ ",",
    s!"  \"buildOk\": {okStr},",
    s!"  \"rustExports\": {rustExportsJson},",
    s!"  \"lean\": {inner}",
    rbrace
  ]

/-- Run the per-project extractors (Lean + Rust), write the JSON
sidecar, and return the project data for downstream consumers (the
report). -/
private def extractOne (pair : Pair) (crate : String) (buildOk : Bool) :
    IO Report.ProjectData := do
  let modName := subfolderToModule pair.verificationFolder
  let leanJson : String ←
    if buildOk then
      try
        let out ← IO.Process.output {
          cmd := "lake", args := #["exe", "_verifier_extract", modName],
          cwd := some pair.leanDir
        }
        if out.exitCode = 0 then pure out.stdout
        else do
          IO.eprintln s!"extractor failed for {modName} (exit {out.exitCode}):\n{out.stderr}"
          pure ""
      catch e => do
        IO.eprintln s!"extractor exception for {modName}: {e}"; pure ""
    else
      pure ""
  let exports : Array RustExtract.Export ←
    try RustExtract.scanProject pair.rustDir
    catch e => do
      IO.eprintln s!"rust scanner failed for {pair.rustDir}: {e}"; pure #[]
  let rustJson := RustExtract.emitExports pair.rustDir exports
  let json := wrapSidecar pair crate buildOk leanJson rustJson
  writeFile (pair.subfolderDir / ".verifier-extract.json") json
  pure {
    rustDir := pair.rustDir,
    leanDir := pair.leanDir,
    subfolder := pair.verificationFolder,
    crate := crate,
    buildOk := buildOk,
    rustExports := exports,
    leanJson := leanJson
  }

/-- Run `check` over many pairs. Errors are collected per pair; one
`lake build` is invoked per unique lean project after every per-pair
emit has been attempted. Returns a (allOk, projectData) pair. -/
private def checkMany (pairs : Array Pair) (skipBuild : Bool) :
    IO (Bool × Array Report.ProjectData) := do
  let mut emitErrors : Array (FilePath × String) := #[]
  for pair in pairs do
    try
      buildAndEmit pair
    catch e =>
      IO.eprintln s!"error in {pair.rustDir}: {e}"
      emitErrors := emitErrors.push (pair.rustDir, toString e)
  -- Per-leanDir bookkeeping: install the extractor source + lakefile
  -- stanza, then run `lake build` once.
  let mut seen : Array FilePath := #[]
  let mut buildOkOf : Array (FilePath × Bool) := #[]
  let mut buildErrors : Array (FilePath × String) := #[]
  unless skipBuild do
    for pair in pairs do
      if seen.contains pair.leanDir then continue
      seen := seen.push pair.leanDir
      try
        let lib ← leanLibName pair.leanDir
        Extract.installExtractor pair.leanDir lib
      catch e =>
        IO.eprintln s!"warning: could not install extractor in {pair.leanDir}: {e}"
      IO.println s!"==> lake build ({pair.leanDir})"
      let ok ← runChecked { cmd := "lake", args := #["build"], cwd := some pair.leanDir }
      buildOkOf := buildOkOf.push (pair.leanDir, ok)
      unless ok do
        buildErrors := buildErrors.push (pair.leanDir, "lake build failed")
  -- Per-pair extraction.
  let mut extractErrors : Array (FilePath × String) := #[]
  let mut data : Array Report.ProjectData := #[]
  for pair in pairs do
    let cargoToml := pair.rustDir / "Cargo.toml"
    let crate ← try cargoCrateName cargoToml catch _ => pure "?"
    let buildOk :=
      if skipBuild then false
      else (buildOkOf.find? (·.1 = pair.leanDir)).map (·.2) |>.getD false
    try
      let d ← extractOne pair crate buildOk
      data := data.push d
    catch e =>
      extractErrors := extractErrors.push (pair.rustDir, toString e)
  -- Summary.
  IO.println ""
  IO.println s!"==> {pairs.size} project(s), {emitErrors.size} emit error(s), {buildErrors.size} build error(s), {extractErrors.size} extract error(s)"
  for (d, e) in emitErrors do
    IO.eprintln s!"  emit fail: {d}: {e}"
  for (d, e) in buildErrors do
    IO.eprintln s!"  build fail: {d}: {e}"
  for (d, e) in extractErrors do
    IO.eprintln s!"  extract fail: {d}: {e}"
  pure (emitErrors.isEmpty ∧ buildErrors.isEmpty ∧ extractErrors.isEmpty, data)

private def cmdCheck (pathOpt : Option String) (skipBuild : Bool) : IO Unit := do
  let pairs : Array Pair ← match pathOpt with
    | some p =>
      let pair ← resolvePair p
      pure #[pair]
    | none =>
      let cwd ← IO.currentDir
      IO.println s!"==> discovering verifier.toml under {cwd}"
      let rustDirs ← Discovery.discoverProjects cwd
      if rustDirs.isEmpty then
        die s!"no `verifier.toml` files found under {cwd}\n(hint: run `verifier new` to bootstrap one)"
      let mut acc : Array Pair := #[]
      for d in rustDirs do
        let pair ← resolvePairFromRust (← absNormalize d)
        acc := acc.push pair
      pure acc
  let (ok, _) ← checkMany pairs skipBuild
  unless ok do IO.Process.exit 1

-- ----------------------------------------------------------------------------
-- `report`
-- ----------------------------------------------------------------------------

/-- Discover, run the full check pipeline, then write the HTML report
to `outDir` (default `./verifier-report/`). With `skipBuild`, omits
`lake build` and the Lean-side extraction (still renders the rust side
and source-browser pages). -/
private def cmdReport (outDir : Option String) (skipBuild : Bool) : IO Unit := do
  let cwd ← IO.currentDir
  IO.println s!"==> discovering verifier.toml under {cwd}"
  let rustDirs ← Discovery.discoverProjects cwd
  if rustDirs.isEmpty then
    die s!"no `verifier.toml` files found under {cwd}\n(hint: run `verifier new` to bootstrap one)"
  let mut pairs : Array Pair := #[]
  for d in rustDirs do
    let pair ← resolvePairFromRust (← absNormalize d)
    pairs := pairs.push pair
  let (_, data) ← checkMany pairs skipBuild
  let out : FilePath := ⟨outDir.getD "verifier-report"⟩
  let outAbs ← absNormalize out
  IO.println s!"==> writing report to {outAbs}"
  Report.writeReport outAbs data
  IO.println s!"==> open {outAbs}/index.html"

-- ----------------------------------------------------------------------------
-- main
-- ----------------------------------------------------------------------------

/-- Parse `--no-build` from a flat argument list, returning the remaining
non-flag positional args and whether the flag was present. -/
private def parseCheckArgs (args : List String) : Option String × Bool :=
  let (flags, pos) := args.partition (·.startsWith "--")
  let skipBuild := flags.contains "--no-build"
  match pos with
  | []     => (none, skipBuild)
  | [p]    => (some p, skipBuild)
  | _      => (none, skipBuild)  -- multiple positionals -> caller will reject

private def parseReportArgs (args : List String) : Option String × Bool :=
  let rec findOut : List String → Option String
    | "--out" :: v :: _ => some v
    | _ :: rest         => findOut rest
    | []                => none
  (findOut args, args.contains "--no-build")

/-- Pull out `--<flag> <value>` from a string list, returning the value
(if present) and the args with that pair removed. -/
private def stripFlagValue (flag : String) :
    List String → Option String × List String
  | f :: v :: rest =>
    if f = flag then (some v, rest)
    else
      let (got, rest') := stripFlagValue flag (v :: rest)
      (got, f :: rest')
  | rest => (none, rest)

def main (args : List String) : IO UInt32 := do
  let (codelib,    args) := stripFlagValue "--codelib"     args
  let (codelibRev, args) := stripFlagValue "--codelib-rev" args
  match args with
  | "new"   :: rust :: lean :: sub :: [] =>
    cmdNew rust lean sub codelib codelibRev; pure 0
  | "check" :: rest =>
    let (path, skipBuild) := parseCheckArgs rest
    -- Reject if more than one positional was supplied.
    let positionalCount := (rest.filter (¬ ·.startsWith "--")).length
    if positionalCount > 1 then
      IO.eprintln usage; pure 1
    else
      cmdCheck path skipBuild; pure 0
  | "report" :: rest =>
    let (outDir, skipBuild) := parseReportArgs rest
    cmdReport outDir skipBuild; pure 0
  | _ =>
    IO.eprintln usage; pure 1

end Verifier

def main := Verifier.main
