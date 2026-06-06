import Verifier.Extract.Schema
import Verifier.Extract.Git
import Verifier.Extract.Source
import Verifier.Extract.Rust
import Verifier.Extract.Program
import Verifier.Extract.Lean

/-!
# `verifier extract` orchestrator

Discovers crates (filesystem-based, matching `verifier check`), builds
one `Artifact` per crate, writes it pretty-printed to `<DIR>/<crate>.json`.

Specs and verifications are populated by `Extract.Lean.scanCrate`
scanning every `.lean` file under the crate's `lean/Project/<Crate>/`
directory for the `@[spec_of …]` / `@[proves …]` attributes that
`codelib/CodeLib/Attrs.lean` registers.
-/

namespace Verifier.Extract

open System (FilePath)
open Lean (Json)

private def snakeToPascal (s : String) : String :=
  String.intercalate "" <| (s.splitOn "_").map fun part =>
    match part.toList with
    | []      => ""
    | c :: cs => String.ofList (c.toUpper :: cs)

/-- Information collected per discovered crate, before extraction. -/
private structure CrateInfo where
  name    : String
  rustDir : FilePath       -- absolute
  leanDir : FilePath       -- absolute
  rustRel : String         -- repo-root relative POSIX
  leanRel : String         -- repo-root relative POSIX
  hasLean : Bool


private def selectByNames (all : Array CrateInfo) (names : List String) : IO (Array CrateInfo) := do
  if names.isEmpty then return all
  let mut out : Array CrateInfo := #[]
  for n in names do
    match all.find? (·.name == n) with
    | some c => out := out.push c
    | none   =>
      throw <| IO.userError
        s!"crate `{n}` not found (available: {String.intercalate ", " (all.toList.map (·.name))})"
  pure out

private def discoverCrates (projectDir : FilePath) : IO (Array CrateInfo) := do
  let rustRoot := projectDir / "rust"
  let leanRoot := projectDir / "lean" / "Project"
  unless ← System.FilePath.pathExists rustRoot do
    throw (IO.userError s!"{rustRoot} not found — are you in a verifier project root?")
  let entries ← rustRoot.readDir
  let mut acc : Array CrateInfo := #[]
  for entry in entries do
    let p := entry.path
    if ¬ (← p.isDir) then continue
    let cargoToml := p / "Cargo.toml"
    unless ← System.FilePath.pathExists cargoToml do continue
    let name := entry.fileName
    let mod := snakeToPascal name
    let leanDir := leanRoot / mod
    let hasLean ← System.FilePath.pathExists leanDir
    acc := acc.push {
      name, rustDir := p, leanDir,
      rustRel := s!"rust/{name}",
      leanRel := s!"lean/Project/{mod}",
      hasLean
    }
  pure acc

private def readRustcEdition (rustDir : FilePath) : IO (Option String) := do
  let cargo := rustDir / "Cargo.toml"
  unless ← System.FilePath.pathExists cargo do return none
  let text ← IO.FS.readFile cargo
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "edition" then
      -- edition = "2024"
      match t.splitOn "\"" with
      | [_, ed, _] => return some ed
      | _          => return none
  return none

private def readLeanToolchain (projectDir : FilePath) : IO String := do
  let p := projectDir / "lean" / "lean-toolchain"
  if ← System.FilePath.pathExists p then
    pure (← IO.FS.readFile p).trimAscii.toString
  else pure ""

private def nowIso : IO String := do
  -- ISO-8601 UTC via shelling out — date's local Lean equivalents are limited.
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  pure out.stdout.trimAsciiEnd.toString

private def findProgramLean (sources : List SourceFile) : Option (String × String) :=
  sources.findSome? fun f =>
    if f.filepath.endsWith "/Program.lean" then some (f.filepath, f.body) else none

private def findExportsRs (sources : List SourceFile) : Option (String × String) :=
  sources.findSome? fun f =>
    if f.filepath.endsWith "/exports.rs" then some (f.filepath, f.body) else none

/-- Build an Artifact for one crate. -/
private def buildArtifact
    (projectDir : FilePath) (repoCommit : String) (lean : String)
    (now : String) (info : CrateInfo) : IO Artifact := do
  let mut diags : Array Diagnostic := #[]
  -- P1: missing lean dir
  if ¬ info.hasLean then
    diags := diags.push {
      severity := .error,
      kind := "missing_lean_dir_for_crate",
      location := { file := info.rustRel, span := { start := ⟨1,1⟩, «end» := ⟨1,1⟩ } },
      message := s!"crate `{info.name}` has no matching lean directory at `{info.leanRel}`"
    }
  -- SourceFiles
  let sources ← Source.gather projectDir info.rustRel info.leanRel
  -- Exports
  let exported := match findExportsRs sources with
    | some (path, body) => Rust.scan path body info.name
    | none => []
  -- Program
  let program := match findProgramLean sources with
    | some (path, body) => Program.find path body
    | none              => none
  -- Specs + verifications (P4/P5)
  let exportNames := exported.map (·.name)
  let leanFindings := LeanScan.scanCrate sources info.leanRel info.name exportNames
  diags := diags ++ leanFindings.diagnostics
  -- rustc edition
  let rustc ← readRustcEdition info.rustDir
  pure {
    schemaVersion    := schemaVersion,
    extractorVersion := extractorVersion,
    extractedAt      := now,
    repoCommit       := repoCommit,
    toolchains       := { rustc := rustc, lean := lean },
    project          := { «crate» := info.name, rust := info.rustRel, lean := info.leanRel },
    code             := sources,
    exported         := exported,
    program          := program,
    specs            := leanFindings.specs.toList,
    verifications    := leanFindings.verifications.toList,
    diagnostics      := diags.toList
  }

/-- Entry point used by the CLI. -/
def run (projectDir : FilePath) (outDir : FilePath) (crateNames : List String := []) : IO Unit := do
  let all ← discoverCrates projectDir
  let crates ← selectByNames all crateNames
  if crates.isEmpty then
    throw (IO.userError s!"{projectDir}/rust has no crate subdirectories")
  let repoCommit ← Git.repoCommit projectDir
  let lean ← readLeanToolchain projectDir
  let now ← nowIso
  IO.FS.createDirAll outDir
  IO.println s!"==> {crates.size} crate(s): {String.intercalate ", " (crates.toList.map (·.name))}"
  for info in crates do
    let art ← buildArtifact projectDir repoCommit lean now info
    let json := Artifact.toJson art
    let path := outDir / s!"{info.name}.json"
    IO.FS.writeFile path (Json.pretty json)
    IO.println s!"    wrote {path}"

end Verifier.Extract
