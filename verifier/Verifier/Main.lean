import Verifier.Emit
import Verifier.Toml

/-!
# `verifier` CLI entry point

See `tasks/02-verifier.md` for the full spec. Two subcommands:

* `verifier new <rust-path> <lean-path> <subfolder>` — scaffold metadata
  files (`verifier.toml`, `origin.toml`), the lean subfolder, an empty
  `Spec.lean`, and (if missing) a fresh lean project. Idempotent on a
  matching pair.
* `verifier check <path>` — given either a rust project (with
  `verifier.toml`) or a verification subfolder (with `origin.toml`),
  run the full pipeline: cargo build → wasm-tools print → Wat.decode →
  emit `Program.lean` → `lake build`.
-/

open System (FilePath)

namespace Verifier

/-- Whitespace predicate used by our `List Char`-flavoured trim. -/
private def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- `String.trim` returns a `String.Slice` in current Lean and the rest of
the slice API is in flux; we stay on `List Char` to keep this code stable. -/
private def strTrim (s : String) : String :=
  let cs := s.toList.dropWhile isSpace
  String.ofList (cs.reverse.dropWhile isSpace).reverse

/-- Take chars while `p` holds. -/
private def strTakeWhile (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.takeWhile p)

/-- Drop chars while `p` holds. -/
private def strDropWhile (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.dropWhile p)

/-- Drop the first `n` characters. -/
private def strDrop (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

/-- Capitalise the first character. -/
private def strCapitalise (s : String) : String :=
  match s.toList with
  | []      => s
  | c :: cs => String.ofList (c.toUpper :: cs)

private def usage : String :=
  "Usage:\n" ++
  "  lake exe verifier new        <rust-path> <lean-path> <subfolder>\n" ++
  "  lake exe verifier check      <path>\n" ++
  "  lake exe verifier check      --no-build <path>   (skip `lake build`)"

private def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

-- ----------------------------------------------------------------------------
-- Path utilities
-- ----------------------------------------------------------------------------

/-- Normalize a `System.FilePath`: drop `.` components and collapse `a/../`.
    Does not touch the filesystem. -/
private def normalize (p : FilePath) : FilePath :=
  let parts := p.components
  let rev := parts.foldl (init := ([] : List String)) fun acc c =>
    match c, acc with
    | ".", _              => acc
    | "..", h :: t        => if h ≠ ".." && h ≠ "" then t else c :: acc
    | _, _                => c :: acc
  ⟨System.FilePath.pathSeparator.toString.intercalate rev.reverse⟩

/-- Compute a relative path from `from` to `to`, both interpreted as
    directories. Both inputs should be absolute and already normalised. -/
private def relativeTo («from» «to» : FilePath) : FilePath :=
  let f := «from».components.filter (· ≠ "")
  let t := «to».components.filter (· ≠ "")
  let rec strip : List String → List String → List String × List String
    | a :: as, b :: bs => if a = b then strip as bs else (a :: as, b :: bs)
    | xs,      ys      => (xs, ys)
  let (upFrom, downTo) := strip f t
  let parts := upFrom.map (fun _ => "..") ++ downTo
  if parts.isEmpty then ⟨"."⟩ else ⟨System.FilePath.pathSeparator.toString.intercalate parts⟩

/-- Absolute, normalised form of a user-supplied path. The path may not
    exist on disk yet; this only canonicalises lexically against `cwd`. -/
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

private def run (o : RunOpts) : IO Unit := do
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

private def captureStdout (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode ≠ 0 then
    die s!"`{cmd}` failed with exit code {out.exitCode}:\n{out.stderr}"
  pure out.stdout

-- ----------------------------------------------------------------------------
-- Cargo / wasm-tools
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
-- TOML round-trip helpers for our two schemas
-- ----------------------------------------------------------------------------

structure VerifierToml where
  leanProject        : String
  verificationFolder : String

structure OriginToml where
  rustProject : String

private def readToml (p : FilePath) : IO Toml.Table := do
  let txt ← IO.FS.readFile p
  match Toml.parse txt with
  | .ok t   => pure t
  | .error e => die s!"{p}: {e}"

private def readVerifierToml (p : FilePath) : IO VerifierToml := do
  let t ← readToml p
  match Toml.require t "lean_project" p.toString,
        Toml.require t "verification_folder" p.toString with
  | .ok lp, .ok vf => pure { leanProject := lp, verificationFolder := vf }
  | .error e, _   => die e
  | _, .error e   => die e

private def readOriginToml (p : FilePath) : IO OriginToml := do
  let t ← readToml p
  match Toml.require t "rust_project" p.toString with
  | .ok rp => pure { rustProject := rp }
  | .error e => die e

private def writeVerifierToml (p : FilePath) (v : VerifierToml) : IO Unit :=
  writeFile p <| Toml.render [
    ("lean_project", v.leanProject),
    ("verification_folder", v.verificationFolder)
  ]

private def writeOriginToml (p : FilePath) (o : OriginToml) : IO Unit :=
  writeFile p <| Toml.render [("rust_project", o.rustProject)]

-- ----------------------------------------------------------------------------
-- Resolved pair view
-- ----------------------------------------------------------------------------

structure Pair where
  rustDir            : FilePath
  leanDir            : FilePath
  verificationFolder : String   -- subfolder *string* (so we can also derive module names)
  deriving Inhabited

private def subfolderDir (p : Pair) : FilePath := p.leanDir / p.verificationFolder

private def subfolderToModule (sub : String) : String :=
  let parts := (sub.splitOn "/").filter (·.length > 0)
  String.intercalate "." parts

private def codelibLeanToolchain : IO String := do
  -- Look for the lean-toolchain relative to the invocation directory (repo root).
  let candidates : List FilePath :=
    [ "codelib/lean-toolchain", "../codelib/lean-toolchain",
      "interpreter/lean-toolchain", "../interpreter/lean-toolchain" ]
  for c in candidates do
    if ← System.FilePath.pathExists c then
      return (← IO.FS.readFile c)
  die "could not locate lean-toolchain (looked in codelib/ and interpreter/)"

private def resolvePairFromRust (rustDir : FilePath) : IO Pair := do
  let v ← readVerifierToml (rustDir / "verifier.toml")
  let leanDir ← absNormalize (rustDir / v.leanProject)
  pure {
    rustDir := rustDir, leanDir := leanDir,
    verificationFolder := v.verificationFolder
  }

private def resolvePairFromSubfolder (subDir : FilePath) : IO Pair := do
  let o ← readOriginToml (subDir / "origin.toml")
  -- Compute the lean project root: walk up from `subDir` until we hit a
  -- `lakefile.toml`. (The subfolder path inside the lean project may be
  -- nested arbitrarily deep.)
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
  pure {
    rustDir := rustDir, leanDir := leanDirAbs,
    verificationFolder := verificationFolder
  }

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

/-- The first `[[lean_lib]] name` field, if any. Falls back to package name. -/
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

private def scaffoldLeanProject (leanDir : FilePath) (codelibDir : FilePath) : IO Unit := do
  let toolchain ← codelibLeanToolchain
  let pkgName :=
    match leanDir.fileName with
    | some s => if s.isEmpty then "Verification" else strCapitalise s
    | none   => "Verification"
  let relCodelib := relativeTo leanDir codelibDir
  IO.FS.createDirAll leanDir
  writeFile (leanDir / "lean-toolchain") toolchain
  writeFile (leanDir / "lakefile.toml") <| String.intercalate "\n" [
    s!"name = \"{pkgName}\"",
    "version = \"0.1.0\"",
    s!"defaultTargets = [\"{pkgName}\"]",
    "",
    "[[require]]",
    "name = \"CodeLib\"",
    s!"path = \"{relCodelib}\"",
    "",
    "[[lean_lib]]",
    s!"name = \"{pkgName}\"",
    ""
  ]
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
    "/-! Write your specification here. -/",
    ""
  ]

private def codelibSourceDir : IO FilePath := do
  -- Look for the `codelib/` directory relative to the invocation directory.
  -- Users invoke from the repo root; the canonical layout is codelib/ next to verifier/.
  let candidates : List FilePath := ["codelib", "../codelib", "./"]
  for c in candidates do
    if ← System.FilePath.pathExists (c / "lean-toolchain") then
      return (← absNormalize c)
  die "could not locate `codelib/` next to invocation directory"

private def cmdNew (rustPathIn leanPathIn subfolder : String) : IO Unit := do
  let rustDir ← absNormalize rustPathIn
  let leanDir ← absNormalize leanPathIn
  let cargoToml := rustDir / "Cargo.toml"
  unless ← System.FilePath.pathExists cargoToml do
    die s!"{rustDir}: no Cargo.toml here (verifier does not scaffold rust crates)"
  -- 1. Lean project: scaffold if missing.
  let codelib ← codelibSourceDir
  if ¬ (← System.FilePath.pathExists (leanDir / "lakefile.toml")) then
    IO.println s!"==> scaffolding lean project at {leanDir}"
    scaffoldLeanProject leanDir codelib
  else
    -- Toolchain match check.
    let expected ← codelibLeanToolchain
    let actual ← IO.FS.readFile (leanDir / "lean-toolchain")
    if strTrim expected ≠ strTrim actual then
      die s!"{leanDir}/lean-toolchain disagrees with {codelib}/lean-toolchain:\n  expected: {strTrim expected}\n  actual:   {strTrim actual}"
  -- 2. Subfolder + origin.toml + Spec.lean.
  let subDir := leanDir / subfolder
  IO.FS.createDirAll subDir
  let originPath := subDir / "origin.toml"
  let rustRel := (relativeTo subDir rustDir).toString
  if ← System.FilePath.pathExists originPath then
    let existing ← readOriginToml originPath
    if existing.rustProject ≠ rustRel then
      die s!"{originPath} already exists and points elsewhere (got `{existing.rustProject}`, want `{rustRel}`)"
  else
    writeOriginToml originPath { rustProject := rustRel }
  let specPath := subDir / "Spec.lean"
  unless ← System.FilePath.pathExists specPath do
    writeFile specPath (specStub subfolder)
  -- 3. verifier.toml on the rust side.
  let verifierPath := rustDir / "verifier.toml"
  let leanRel := (relativeTo rustDir leanDir).toString
  if ← System.FilePath.pathExists verifierPath then
    let existing ← readVerifierToml verifierPath
    if existing.leanProject ≠ leanRel || existing.verificationFolder ≠ subfolder then
      die s!"{verifierPath} already exists and points elsewhere (got `{existing.leanProject}` / `{existing.verificationFolder}`, want `{leanRel}` / `{subfolder}`)"
  else
    writeVerifierToml verifierPath
      { leanProject := leanRel, verificationFolder := subfolder }
  -- 4. Wire import line into the lean library root.
  let lib ← leanLibName leanDir
  let rootFile := leanDir / s!"{lib}.lean"
  appendImportLine rootFile s!"import {subfolderToModule subfolder}.Spec"
  IO.println s!"==> verifier new wrote {verifierPath}, {originPath}, {specPath}"

-- ----------------------------------------------------------------------------
-- `check`
-- ----------------------------------------------------------------------------

private def emitProgramFile
    (pair : Pair) (m : Wasm.Module) (watText : String) : IO Unit := do
  let sub := subfolderDir pair
  IO.FS.createDirAll sub
  let modName := subfolderToModule pair.verificationFolder
  let bodiesBlock := Emit.funcBodies m
  let moduleExpr := Emit.module m
  -- Relative path used by the drift check at elaboration time. `lake build`
  -- runs with the lake-package root as cwd, so we anchor to that.
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

private def cmdCheck (path : String) (skipBuild : Bool := false) : IO Unit := do
  let pair ← resolvePair path
  let cargoToml := pair.rustDir / "Cargo.toml"
  unless ← System.FilePath.pathExists cargoToml do
    die s!"{pair.rustDir}: no Cargo.toml here (origin.toml/verifier.toml is stale)"
  let crate ← cargoCrateName cargoToml
  IO.println s!"==> check {pair.rustDir} -> {pair.leanDir}/{pair.verificationFolder} (crate `{crate}`)"
  -- 1. cargo build to wasm
  run {
    cmd := "cargo",
    args := #["build", "--release", "--target", "wasm32-unknown-unknown",
              "--manifest-path", cargoToml.toString]
  }
  -- The artifact lives at <rust>/target/wasm32-unknown-unknown/release/<crate>.wasm
  -- but crate name on disk uses `-` ↔ `_` swap.
  let crateFs := crate.map (fun c => if c = '-' then '_' else c)
  let wasmFile := pair.rustDir / "target" / "wasm32-unknown-unknown" / "release" / s!"{crateFs}.wasm"
  unless ← System.FilePath.pathExists wasmFile do
    die s!"expected wasm artifact at {wasmFile} but it is missing"
  -- 2. wasm-tools strip → wasm-tools print. The strip removes custom
  --    sections like `producers` that the Lean wat decoder does not parse.
  let sub := subfolderDir pair
  IO.FS.createDirAll sub
  let strippedWasm := sub / ".module.stripped.wasm"
  run {
    cmd := "wasm-tools",
    args := #["strip", "--all", wasmFile.toString, "-o", strippedWasm.toString]
  }
  let watText ← captureStdout "wasm-tools" #["print", strippedWasm.toString]
  -- 3. write module.wat
  writeFile (sub / "module.wat") watText
  IO.FS.removeFile strippedWasm
  -- 4. decode in-process
  match Wasm.Decoder.Wat.decode watText with
  | .error e => die s!"wat decoder rejected the generated module: {e}"
  | .ok m =>
    -- 5. emit Program.lean
    emitProgramFile pair m watText
    -- 6. lake build on the lean project (skipped if --no-build)
    unless skipBuild do
      IO.println s!"==> lake build ({pair.leanDir})"
      run { cmd := "lake", args := #["build"], cwd := some pair.leanDir }

-- ----------------------------------------------------------------------------
-- main
-- ----------------------------------------------------------------------------

def main (args : List String) : IO UInt32 := do
  match args with
  | "new"   :: rust :: lean :: sub :: [] => cmdNew rust lean sub; pure 0
  | "check" :: "--no-build" :: path :: [] => cmdCheck path (skipBuild := true); pure 0
  | "check" :: path :: [] => cmdCheck path; pure 0
  | _ =>
    IO.eprintln usage
    pure 1

end Verifier

def main := Verifier.main
