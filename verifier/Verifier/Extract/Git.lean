/-!
# Git + checksum helpers for `verifier extract`

Thin wrappers around `git` and `shasum` (which is present on macOS and
typical Linux). All helpers are best-effort — if `git` can't answer a
question (e.g. the file isn't tracked, the repo is missing), they
return an empty string rather than failing extraction.
-/

namespace Verifier.Extract2.Git

open System (FilePath)

/-- Run `git` with the given args at `cwd`, returning `(exitCode, stdout)`.
stderr is captured and discarded. -/
def run (cwd : FilePath) (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output {
    cmd := "git", args := args, cwd := some cwd
  }
  pure (out.exitCode, out.stdout.trimAsciiEnd.toString)

/-- Run a command and return only stdout (empty on failure). -/
private def runOk (cwd : FilePath) (args : Array String) : IO String := do
  let (code, out) ← run cwd args
  pure (if code = 0 then out else "")

/-- `HEAD` sha. Empty if not a repo. -/
def headSha (cwd : FilePath) : IO String :=
  runOk cwd #["rev-parse", "HEAD"]

/-- `true` iff the working tree differs from HEAD. -/
def isDirty (cwd : FilePath) : IO Bool := do
  let (code, out) ← run cwd #["status", "--porcelain"]
  pure (code = 0 ∧ ¬ out.isEmpty)

/-- repo_commit field: `HEAD` sha with `-dirty` suffix if working tree differs. -/
def repoCommit (cwd : FilePath) : IO String := do
  let h ← headSha cwd
  if h.isEmpty then return ""
  if ← isDirty cwd then return h ++ "-dirty" else return h

/-- List all files tracked by git under `relDir` (path relative to `cwd`).
Returns repo-root-relative POSIX paths. Empty on error. -/
def lsFiles (cwd : FilePath) (relDir : String) : IO (Array String) := do
  let (code, out) ← run cwd #["ls-files", "--", relDir]
  if code ≠ 0 then return #[]
  return (out.splitOn "\n").filter (·.length > 0) |>.toArray

/-- Blob sha of `relPath` in HEAD. Empty if untracked. -/
def blobSha (cwd : FilePath) (relPath : String) : IO String := do
  let (code, out) ← run cwd #["ls-tree", "HEAD", relPath]
  if code ≠ 0 ∨ out.isEmpty then return ""
  -- format: <mode> <type> <sha>\t<path>
  let parts := (out.splitOn "\t").headD "" |>.splitOn " "
  match parts with
  | [_, _, sha] => return sha
  | _           => return ""

/-- Last commit that touched `relPath`. Empty if no history. -/
def lastCommit (cwd : FilePath) (relPath : String) : IO String :=
  runOk cwd #["log", "-1", "--format=%H", "--", relPath]

/-- sha256 hex of a file's bytes via `shasum -a 256`. Empty on failure. -/
def sha256File (path : FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "shasum", args := #["-a", "256", path.toString] }
  if out.exitCode ≠ 0 then return ""
  -- format: "<hex>  <path>\n"
  let line := out.stdout.trimAsciiEnd.toString
  return (line.splitOn " ").headD ""

end Verifier.Extract2.Git
