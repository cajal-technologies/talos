import Verifier.Extract2.Schema
import Verifier.Extract2.Git
import Verifier.Extract2.Source
import Verifier.Extract2.Rust
import Verifier.Extract2.Program

/-!
# `verifier extract` orchestrator

Discovers crates (filesystem-based, matching `verifier check`), builds
one `Artifact` per crate, writes it pretty-printed to `<DIR>/<crate>.json`.

`specs` and `verifications` are emitted as `[]` for now — the
`@[spec_of]` / `@[proves]` attributes (P4, P5, P7 in EXTRACT.md) don't
exist yet. A diagnostic flags the prerequisite gap.
-/

namespace Verifier.Extract2

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
  -- P4/P5/P7 prerequisite gap diagnostic — emitted once per crate while
  -- the attribute infrastructure does not yet exist in codelib.
  diags := diags.push {
    severity := .info,
    kind     := "prereq_attributes_missing",
    location := { file := info.leanRel, span := { start := ⟨1,1⟩, «end» := ⟨1,1⟩ } },
    message  := "specs/verifications discovery requires `@[spec_of]` and `@[proves]` (see EXTRACT.md §P4/P5/P7); none recorded"
  }
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
    specs            := [],
    verifications    := [],
    diagnostics      := diags.toList
  }

/-- Entry point used by the CLI. -/
def run (projectDir : FilePath) (outDir : FilePath) : IO Unit := do
  let crates ← discoverCrates projectDir
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

end Verifier.Extract2
