/-!
# Project discovery

Walk the filesystem from a starting directory looking for `verifier.toml`
files (rust projects to verify) or `origin.toml` files (lean verification
subfolders). Pruning is conservative: skip well-known build/cache
directories so a top-level scan stays fast. Hidden directories
(`.something`) are also pruned.
-/

namespace Verifier.Discovery

open System (FilePath)

/-- Directory names to prune during discovery. -/
def prunedDirs : List String :=
  ["target", "node_modules", ".lake", ".git", ".cache",
   "build", "dist", "out", ".direnv"]

private partial def discoverWith (marker : String) (root : FilePath)
    : IO (Array FilePath) := do
  let mut out : Array FilePath := #[]
  let mut stack : Array FilePath := #[root]
  while !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    if ← System.FilePath.pathExists (cur / marker) then
      out := out.push cur
    let entries ← try cur.readDir catch _ => pure #[]
    for entry in entries do
      let name := entry.fileName
      if prunedDirs.contains name then continue
      if name.startsWith "." then continue
      let p := entry.path
      let isDir ← try p.isDir catch _ => pure false
      if isDir then
        stack := stack.push p
  pure out

/-- Every directory under `root` that contains a `verifier.toml`. -/
def discoverProjects (root : FilePath) : IO (Array FilePath) :=
  discoverWith "verifier.toml" root

/-- Every directory under `root` that contains an `origin.toml`. -/
def discoverOrigins (root : FilePath) : IO (Array FilePath) :=
  discoverWith "origin.toml" root

end Verifier.Discovery
