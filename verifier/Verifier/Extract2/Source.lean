import Verifier.Extract2.Schema
import Verifier.Extract2.Git

/-!
# `SourceFile` gathering

Enumerate tracked files under a directory via `git ls-files`, apply the
exclusion list from EXTRACT.md, and produce `SourceFile` records.
-/

namespace Verifier.Extract2.Source

open System (FilePath)

/-- Classify a file by extension / basename for the `language` enum. -/
def classify (relPath : String) : String :=
  let base := (relPath.splitOn "/").getLastD ""
  if base = "lean-toolchain" then "toolchain"
  else if relPath.endsWith ".rs" then "rust"
  else if relPath.endsWith ".lean" then "lean"
  else if relPath.endsWith ".toml" then "toml"
  else if relPath.endsWith ".wat" then "wat"
  else "other"

/-- True when the path should be excluded per EXTRACT.md's rules. -/
def isExcluded (relPath : String) : Bool :=
  let segs := relPath.splitOn "/"
  let base := segs.getLastD ""
  if base = "Cargo.lock" ∨ base = "lake-manifest.json" then true
  else segs.any fun s => s = ".lake" ∨ s = "lake-packages" ∨ s = "target"

/-- Whether a path under `rust/build/<crate>/` should be kept (only `.wat`). -/
def isBuildArtifact (relPath : String) : Bool :=
  let segs := (relPath.splitOn "/").toArray
  segs.size ≥ 3 ∧ segs[0]! = "rust" ∧ segs[1]! = "build"

def buildArtifactKept (relPath : String) : Bool :=
  relPath.endsWith ".wat"

/-- Build a `SourceFile` record for one repo-relative path. -/
def mkSourceFile (repoRoot : FilePath) (relPath : String) : IO SourceFile := do
  let abs := repoRoot / relPath
  let body ← try IO.FS.readFile abs catch _ => pure ""
  let lineCount := body.splitOn "\n" |>.length
  let sha ← Git.sha256File abs
  let blob ← Git.blobSha repoRoot relPath
  let last ← Git.lastCommit repoRoot relPath
  return {
    filepath   := relPath,
    body       := body,
    language   := classify relPath,
    sha256     := sha,
    gitBlob    := blob,
    lastCommit := last,
    lineCount  := lineCount
  }

/-- Gather all `SourceFile`s for the union of two directories
(`crate's rust dir` and `crate's lean dir`), filtered per EXTRACT.md.
Paths returned are repo-root-relative. -/
def gather (repoRoot : FilePath) (rustRel leanRel : String) : IO (List SourceFile) := do
  let rustFiles ← Git.lsFiles repoRoot rustRel
  let leanFiles ← Git.lsFiles repoRoot leanRel
  let all := rustFiles ++ leanFiles
  let kept := all.filter fun p =>
    ¬ isExcluded p ∧ (¬ isBuildArtifact p ∨ buildArtifactKept p)
  let mut acc : Array SourceFile := #[]
  for p in kept do
    acc := acc.push (← mkSourceFile repoRoot p)
  return acc.toList

end Verifier.Extract2.Source
