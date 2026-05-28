import Verifier.Extract2.Schema

/-!
# `Program.lean` module decl locator

Find `def «module» : Wasm.Module := …` in a generated `Program.lean`
and return a `Program` record. The file is machine-emitted with a
known shape (see `Verifier/Emit.lean`), so a small line scan suffices.
-/

namespace Verifier.Extract2.Program

open System (FilePath)

private def leftTrim (s : String) : String :=
  s.toList.dropWhile (fun c => c = ' ' ∨ c = '\t') |> String.ofList

private partial def findNamespace (lines : Array String) (idx : Nat) : String :=
  if h : idx < lines.size then
    let line := lines[idx]
    let t := leftTrim line
    if t.startsWith "namespace " then
      (t.drop "namespace ".length).trimAsciiEnd.toString
    else findNamespace lines (idx + 1)
  else ""

/-- 0-indexed line where `def «module»` (or `def \"module\"`) begins. -/
private partial def findModuleDeclLine (lines : Array String) (idx : Nat) : Option Nat :=
  if h : idx < lines.size then
    let t := leftTrim lines[idx]
    if t.startsWith "def «module»" ∨ t.startsWith "def module " ∨ t.startsWith "def module:" then
      some idx
    else findModuleDeclLine lines (idx + 1)
  else none

/-- 0-indexed line where the decl ends. Heuristic: scan forward until a
blank line followed by either `end ` or EOF. -/
private partial def findEnd (lines : Array String) (idx : Nat) : Nat :=
  if h : idx < lines.size then
    let t := leftTrim lines[idx]
    if t.startsWith "end " ∨ t = "" ∧ idx + 1 < lines.size ∧ (leftTrim lines[idx + 1]!).startsWith "end " then
      if idx = 0 then 0 else idx - 1
    else findEnd lines (idx + 1)
  else lines.size - 1

/-- Build the `Program` record. Returns `none` if no module decl found. -/
def find (relPath : String) (body : String) : Option Program := Id.run do
  let lines := (body.splitOn "\n").toArray
  match findModuleDeclLine lines 0 with
  | none      => none
  | some sIdx =>
    let ns := findNamespace lines 0
    let eIdx := findEnd lines sIdx
    let endLine := if h : eIdx < lines.size then lines[eIdx] else ""
    let span : Span := {
      start := { line := sIdx + 1, column := 1 },
      «end» := { line := eIdx + 1, column := endLine.length + 1 }
    }
    let bodySlice := String.intercalate "\n"
      ((lines.toList.drop sIdx).take (eIdx + 1 - sIdx))
    let modName := if ns.isEmpty then "module" else s!"{ns}.module"
    some { module := modName, location := { file := relPath, span := span }, body := bodySlice }

end Verifier.Extract2.Program
