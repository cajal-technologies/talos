import Verifier.Extract2.Schema

/-!
# Rust `exports.rs` scanner

Walks lines of `src/exports.rs` looking for items of the form

```
#[unsafe(no_mangle)]            -- attributes (0+)
pub extern "C" fn name(args) -> ret {
    ...
}
```

For each, emits an `ExportedFunction`. This is a deliberately simple
line scanner — we own `exports.rs` by convention, so its shape is
predictable. Functions outside that file are not picked up (and emit
`export_outside_exports_rs` from the orchestrator).

Out of scope: macros that synthesize fns, multi-line signatures with
nested generics that span weird brace nesting, items with attributes
spread across complex token trees. The convention forbids these.
-/

namespace Verifier.Extract2.Rust

open System (FilePath)

/-- Does `line` (already trimmed-left) contain `fn ` outside a string? -/
private def hasFnKeyword (line : String) : Bool :=
  let chars := line.toList
  let rec go : List Char → Bool
    | 'f' :: 'n' :: c :: _ => c = ' ' ∨ c = '(' ∨ c = '<'
    | _ :: rest            => go rest
    | []                   => false
  go chars

/-- True if the trimmed line is a `#[unsafe(no_mangle)] pub extern "C" fn …`
candidate. We just check for the substring `fn `; the surrounding scan
gates on it being preceded by `extern "C"`. -/
private def isFnLine (trimmed : String) : Bool :=
  trimmed.startsWith "fn " ∨ trimmed.startsWith "pub fn " ∨
    trimmed.startsWith "pub extern " ∨ trimmed.startsWith "extern "

private def leftTrim (s : String) : String :=
  s.toList.dropWhile (fun c => c = ' ' ∨ c = '\t') |> String.ofList

private def isIdent (c : Char) : Bool := c.isAlphanum ∨ c = '_'

private def scanFnName : List Char → Option String
  | 'f' :: 'n' :: ' ' :: rest =>
    let name := rest.takeWhile isIdent
    if name.isEmpty then none else some (String.ofList name)
  | _ :: rest => scanFnName rest
  | []        => none

/-- Parse the identifier after the literal `fn ` token in `line`. -/
private def parseFnName? (line : String) : Option String :=
  scanFnName line.toList

/-- Strip leading `/// ` (one space) or `///` from a doc line. -/
private def stripDocPrefix (s : String) : String :=
  let t := leftTrim s
  if t.startsWith "/// " then (t.drop 4).toString
  else if t.startsWith "///" then (t.drop 3).toString
  else t

/-- Lines that are attribute lines (start with `#[`). -/
private def isAttrLine (trimmed : String) : Bool :=
  trimmed.startsWith "#["

/-- Lines that are doc-comment lines (`///`). -/
private def isDocLine (trimmed : String) : Bool :=
  trimmed.startsWith "///"

/-- Find the closing `}` of the function body starting at line `startIdx`
(0-indexed). Counts brace depth (string/char literal aware enough for our
needs — `exports.rs` bodies are tiny). Returns the 0-indexed line of the
closing brace. -/
private def findEndLine (lines : Array String) (startIdx : Nat) : Nat := Id.run do
  let mut depth : Int := 0
  let mut seenOpen := false
  let mut i := startIdx
  while i < lines.size do
    let line := lines[i]!
    for c in line.toList do
      if c = '{' then
        depth := depth + 1
        seenOpen := true
      else if c = '}' then
        depth := depth - 1
    if seenOpen ∧ depth ≤ 0 then return i
    i := i + 1
  lines.size - 1

/-- Scan `body` (the contents of `exports.rs`) and emit one
`ExportedFunction` per `fn` item. -/
def scan (relPath : String) (body : String) (crate : String) : List ExportedFunction := Id.run do
  let lines := (body.splitOn "\n").toArray
  let mut out : Array ExportedFunction := #[]
  let mut i := 0
  while i < lines.size do
    let trimmed := leftTrim lines[i]!
    let hasFn := hasFnKeyword trimmed
    if hasFn ∧ isFnLine trimmed then
      -- Walk back over contiguous attribute / doc-comment lines.
      let mut start := i
      let mut docLines : Array String := #[]
      let mut j : Int := (i : Int) - 1
      while j ≥ 0 do
        let t := leftTrim lines[j.toNat]!
        if isAttrLine t ∨ isDocLine t then
          start := j.toNat
          if isDocLine t then
            docLines := docLines.push (stripDocPrefix t)
          j := j - 1
        else
          j := -1
      -- doc lines were collected in reverse order
      let docstring := String.intercalate "\n" docLines.reverse.toList
      -- Find the end of the body.
      let endIdx := findEndLine lines i
      -- Build the signature slice: from `fn` on line i through whatever
      -- precedes the `{` on the line where the body opens.
      let fnLine := lines[i]!
      match parseFnName? fnLine with
      | none => i := i + 1
      | some name =>
        let pre   := (fnLine.splitOn "fn ").headD ""
        let after := (fnLine.drop pre.length).toString
        let sig   := (after.splitOn "{").headD after |>.trimAsciiEnd.toString
        let span : Span := {
          start := { line := start + 1, column := 1 },
          «end» := { line := endIdx + 1, column := (lines[endIdx]!.length + 1) }
        }
        out := out.push {
          name      := name,
          «crate»   := crate,
          signature := sig,
          docstring := docstring,
          location  := { file := relPath, span := span }
        }
        i := endIdx + 1
    else
      i := i + 1
  return out.toList

end Verifier.Extract2.Rust
