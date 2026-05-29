import Verifier.Extract.Schema

/-!
# Lean `Spec.lean` / `Proof.lean` scanner

Discovers `@[spec_of …] def Name : Prop := …` (formal specs) and
`@[proves Spec.Name] theorem … := …` (verifications) inside the
crate's Lean directory. Mirrors the file-scanner style of `Rust.lean`
— no Lean elaboration, just line walking with enough state to track
the current namespace, buffered docstrings, and buffered attributes.

Conventions assumed (see `verifier/EXTRACT.md`):

* The `/-- … -/` doc block immediately precedes the attribute block,
  which immediately precedes the `def` / `theorem`.
* Each `@[…]` attribute lives on its own line; `@[a, b]` combined
  attributes are not parsed (split them up).
* `namespace` / `end` use matched dotted names (`namespace A.B` …
  `end A.B`).

Out of scope: nested doc blocks, attribute payloads spanning multiple
lines, declarations whose `def`/`theorem` keyword does not appear at
the start of a (left-trimmed) line.
-/

namespace Verifier.Extract.LeanScan

open System (FilePath)

private def leftTrim (s : String) : String :=
  s.toList.dropWhile (fun c => c = ' ' ∨ c = '\t') |> String.ofList

private def dropPrefix (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

private def isIdentChar (c : Char) : Bool := c.isAlphanum ∨ c = '_' ∨ c = '.' ∨ c = '\''

private def takeIdent (cs : List Char) : String × List Char :=
  let name := cs.takeWhile isIdentChar
  let rest := cs.dropWhile isIdentChar
  (String.ofList name, rest)

private def dropWS (cs : List Char) : List Char :=
  cs.dropWhile (fun c => c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r')

/-- Read a quoted `"…"` string literal. Backslash escapes are passed
through verbatim (we just unescape `\"` and `\\`). -/
private partial def takeStr : List Char → Option (String × List Char)
  | '"' :: rest =>
    let rec loop (acc : List Char) : List Char → Option (String × List Char)
      | '\\' :: c :: rest => loop (c :: acc) rest
      | '"' :: rest       => some (String.ofList acc.reverse, rest)
      | c :: rest         => loop (c :: acc) rest
      | []                => none
    loop [] rest
  | _ => none

/-- Recognised forms of `@[spec_of …]` and `@[proves …]` on a single
attribute line. -/
inductive ParsedAttr
  | specOf (kind : String) (target : String)
  | proves (qname : String)
  | malformedSpecOf
  | malformedProves
  deriving Inhabited, Repr

/-- Parse a single `@[…]` attribute body. Returns `none` if it isn't
one of our two attributes. -/
private def parseAttrBody (body : String) : Option ParsedAttr :=
  let cs := dropWS body.toList
  let (head, rest) := takeIdent cs
  if head = "spec_of" then
    let rest := dropWS rest
    match takeStr rest with
    | some (kind, rest) =>
      let rest := dropWS rest
      match takeStr rest with
      | some (target, _) => some (.specOf kind target)
      | none             => some .malformedSpecOf
    | none => some .malformedSpecOf
  else if head = "proves" then
    let rest := dropWS rest
    let (name, _) := takeIdent rest
    if name.isEmpty then some .malformedProves
    else some (.proves name)
  else
    none

/-- Split an attribute-block body on top-level commas — i.e. commas
that lie outside any `"…"` string literal. Used to turn
`spec_of "a" "b", spec_of "c" "d"` into two attribute segments. -/
private def splitTopLevelCommas (body : String) : List String := Id.run do
  let mut segments : Array String := #[]
  let mut acc : Array Char := #[]
  let mut inStr := false
  let mut esc := false
  for c in body.toList do
    if esc then
      acc := acc.push c
      esc := false
    else if inStr then
      if c = '\\' then esc := true
      else if c = '"' then inStr := false
      acc := acc.push c
    else if c = '"' then
      inStr := true
      acc := acc.push c
    else if c = ',' then
      segments := segments.push (String.ofList acc.toList)
      acc := #[]
    else
      acc := acc.push c
  segments := segments.push (String.ofList acc.toList)
  return segments.toList

/-- If `line` is a single-line attribute block of the form `@[ … ]`,
return its body. `none` if it isn't or if the block opens but doesn't
close on the same line — the caller handles multi-line blocks. -/
private def takeAttrLine (line : String) : Option String :=
  let t := (leftTrim line).trimAsciiEnd.toString
  if ¬ t.startsWith "@[" then none
  else if ¬ t.endsWith "]" then none
  else
    let dropped := dropPrefix t 2
    some (String.ofList dropped.toList.dropLast)

/-- Does `trimmed` open an `@[` block (whether single- or multi-line)? -/
private def opensAttrBlock (line : String) : Bool :=
  (leftTrim line).startsWith "@["

/-- A `namespace X.Y` line opens namespace `X.Y` and returns it. -/
private def takeNamespace (line : String) : Option String :=
  let t := leftTrim line
  if t.startsWith "namespace " then
    let rest := (dropPrefix t "namespace ".length).trimAscii.toString
    if rest.isEmpty then none else some rest
  else none

/-- An `end X.Y` line closes namespace `X.Y`. -/
private def takeEnd (line : String) : Option Unit :=
  let t := leftTrim line
  if t.startsWith "end " then some () else none

/-- Recognise a `def` declaration line. -/
private def takeDef (line : String) : Option String :=
  let t := leftTrim line
  if t.startsWith "def " then
    let rest := dropWS (dropPrefix t 4).toList
    let (name, _) := takeIdent rest
    if name.isEmpty then none else some name
  else none

/-- Recognise a `theorem` declaration line. -/
private def takeTheorem (line : String) : Option String :=
  let t := leftTrim line
  if t.startsWith "theorem " then
    let rest := dropWS (dropPrefix t 8).toList
    let (name, _) := takeIdent rest
    if name.isEmpty then none else some name
  else none

/-- Extract the `Informal spec:` block from a raw docstring (P6).
Returns `(prose, informal?)`. -/
private def splitInformal (raw : String) : String × Option String := Id.run do
  let lines := raw.splitOn "\n"
  let mut prose : Array String := #[]
  let mut informal : Array String := #[]
  let mut inInformal := false
  for line in lines do
    if (¬ inInformal) ∧ (line.trimAsciiEnd.toString = "Informal spec:") then
      inInformal := true
    else if inInformal then
      informal := informal.push line
    else
      prose := prose.push line
  let proseStr := String.intercalate "\n" prose.toList
  let infOpt :=
    if inInformal then some (String.intercalate "\n" informal.toList) else none
  return (proseStr, infOpt)

/-- Qualified name from a namespace stack and a local identifier. -/
private def qualify (nsStack : List String) (localName : String) : String :=
  let ns := String.intercalate "." nsStack.reverse
  if ns.isEmpty then localName else s!"{ns}.{localName}"

/-- Whether `target` (as written in a `@[spec_of rust-exported …]`)
matches one of the crate's exports. Schema: `crate::fn`. Returns
`(isSameCrate, isResolved)`. -/
private def classifyRustExportedTarget
    (target : String) (thisCrate : String) (exportNames : List String) :
    Bool × Bool :=
  match target.splitOn "::" with
  | [c, f] =>
    let sameCrate := c = thisCrate
    let resolved := sameCrate ∧ exportNames.contains f
    (sameCrate, resolved)
  | _ => (false, false)

private def kindOfString : String → Option RefKind
  | "rust-exported" => some .rustExported
  | "rust-internal" => some .rustInternal
  | "lean"          => some .leanSym
  | _               => none

/-- Per-file mutable accumulator. -/
private structure FileState where
  nsStack       : List String  := []
  docStart      : Option Nat   := none           -- 0-indexed line where `/--` opened
  docLines      : Array String := #[]            -- collected raw lines inside `/-- … -/`
  inDoc         : Bool         := false
  pendingDoc    : Option (Nat × String) := none  -- (startLine, raw) ready to attach
  attrs         : Array ParsedAttr := #[]
  attrStart     : Option Nat   := none           -- first attribute / doc line
  inAttrBlock   : Bool         := false          -- inside a multi-line `@[ … ]`
  attrBuf       : Array String := #[]            -- accumulated lines of the open block

private def resetAttachables (st : FileState) : FileState :=
  { st with pendingDoc := none, attrs := #[], attrStart := none,
            inAttrBlock := false, attrBuf := #[] }

/-- Output of scanning a single Lean source file. -/
structure FileFindings where
  specs         : Array FormalSpec
  verifications : Array Verification
  diagnostics   : Array Diagnostic
  deriving Inhabited

/-- Scan one Lean source file. -/
def scanFile
    (relPath : String) (body : String)
    (thisCrate : String) (exportNames : List String) :
    FileFindings := Id.run do
  let lines := (body.splitOn "\n").toArray
  let mut st : FileState := {}
  let mut specs : Array FormalSpec := #[]
  let mut verifs : Array Verification := #[]
  let mut diags : Array Diagnostic := #[]
  let mkLoc (s e : Nat) (endCol : Nat) : Location :=
    { file := relPath,
      span := { start := { line := s + 1, column := 1 },
                «end» := { line := e + 1, column := endCol + 1 } } }
  let mut i : Nat := 0
  while hI : i < lines.size do
    let line := lines[i]
    let trimmed := leftTrim line
    -- 1. Namespace bookkeeping.
    if let some ns := takeNamespace line then
      st := { resetAttachables st with nsStack := ns :: st.nsStack }
      i := i + 1
      continue
    if (takeEnd line).isSome then
      st := { resetAttachables st with nsStack := st.nsStack.tail }
      i := i + 1
      continue
    -- 2. `/-- … -/` doc blocks (possibly multi-line).
    if st.inDoc then
      match line.splitOn "-/" with
      | first :: _ :: _ =>
        let acc := (st.docLines.push first).toList
        let raw := String.intercalate "\n" acc
        let start := st.docStart.getD i
        st := { nsStack := st.nsStack,
                docStart := none, docLines := #[], inDoc := false,
                pendingDoc := some (start, raw),
                attrs := #[], attrStart := some start }
      | _ =>
        st := { st with docLines := st.docLines.push line }
      i := i + 1
      continue
    else if trimmed.startsWith "/--" then
      let afterOpen := dropPrefix trimmed 3
      match afterOpen.splitOn "-/" with
      | inner :: _ :: _ =>
        st := { st with pendingDoc := some (i, inner),
                        attrStart := some i, attrs := #[] }
      | _ =>
        st := { st with inDoc := true, docStart := some i,
                        docLines := #[afterOpen] }
      i := i + 1
      continue
    -- 3. Attribute blocks (single-line, multi-line, comma-separated).
    --    A block opens with `@[`; its body is everything between `@[`
    --    and the matching top-level `]`. Once collected, we split on
    --    top-level commas and parse each segment as one attribute.
    let mut handledAttr := false
    let processBlockBody := fun (body : String) (start : Nat) => Id.run do
      let mut attrs := st.attrs
      let mut localDiags : Array Diagnostic := #[]
      for seg in splitTopLevelCommas body do
        match parseAttrBody seg with
        | none => pure ()
        | some parsed =>
          attrs := attrs.push parsed
          match parsed with
          | .malformedSpecOf =>
            localDiags := localDiags.push {
              severity := .warn, kind := "malformed_spec_of_attribute",
              location := mkLoc start i line.length,
              message  := s!"could not parse `@[spec_of …]` near line {start + 1}"
            }
          | .malformedProves =>
            localDiags := localDiags.push {
              severity := .warn, kind := "malformed_proves_attribute",
              location := mkLoc start i line.length,
              message  := s!"could not parse `@[proves …]` near line {start + 1}"
            }
          | _ => pure ()
      return (attrs, localDiags)
    if st.inAttrBlock then
      -- Continuation line of a multi-line `@[ … ]`.
      let buf := st.attrBuf.push line
      let joined := String.intercalate "\n" buf.toList
      -- Look for a closing `]` somewhere on this line (top-level).
      if line.toList.contains ']' then
        -- Strip trailing `…]` and parse the body.
        let trimmed := joined.trimAsciiEnd.toString
        if trimmed.endsWith "]" then
          let body := String.ofList (dropPrefix trimmed 2).toList.dropLast
          let start := st.attrStart.getD i
          let (newAttrs, newDiags) := processBlockBody body start
          st := { st with attrs := newAttrs, inAttrBlock := false,
                          attrBuf := #[], attrStart := some start }
          diags := diags ++ newDiags
        else
          -- closing `]` mid-line — uncommon; fall back to reset.
          st := { st with inAttrBlock := false, attrBuf := #[] }
      else
        st := { st with attrBuf := buf }
      handledAttr := true
    else if opensAttrBlock line then
      match takeAttrLine line with
      | some body =>
        let start := st.attrStart.getD i
        let (newAttrs, newDiags) := processBlockBody body start
        st := { st with attrs := newAttrs, attrStart := some start }
        diags := diags ++ newDiags
      | none =>
        -- Multi-line block opens here.
        let start := st.attrStart.getD i
        st := { st with inAttrBlock := true, attrBuf := #[line],
                        attrStart := some start }
      handledAttr := true
    if handledAttr then
      i := i + 1
      continue
    -- 4. `def NAME`. Emit FormalSpec iff at least one `@[spec_of …]`.
    if let some name := takeDef line then
      let hasSpecOf := st.attrs.any (fun a =>
        match a with | .specOf _ _ | .malformedSpecOf => true | _ => false)
      if hasSpecOf then
        let qname := qualify st.nsStack name
        let rawDoc := (st.pendingDoc.map (·.2)).getD ""
        let (prose, informal) := splitInformal rawDoc
        let mut refs : Array Reference := #[]
        for a in st.attrs do
          match a with
          | .specOf kindStr target =>
            match kindOfString kindStr with
            | none =>
              diags := diags.push {
                severity := .warn, kind := "malformed_spec_of_attribute",
                location := mkLoc i i line.length,
                message  :=
                  s!"unknown kind `{kindStr}` in `@[spec_of …]` for `{qname}`"
              }
            | some kind =>
              let (sameCrate, resolved) :=
                match kind with
                | .rustExported =>
                  classifyRustExportedTarget target thisCrate exportNames
                | _ => (false, false)
              refs := refs.push { kind, target, resolved }
              if (match kind with | .rustExported => true | _ => false) then
                if ¬ sameCrate then
                  diags := diags.push {
                    severity := .info, kind := "cross_crate_reference",
                    location := mkLoc i i line.length,
                    message  :=
                      s!"`@[spec_of rust-exported \"{target}\"]` on `{qname}` names a different crate's export"
                  }
                else if ¬ resolved then
                  diags := diags.push {
                    severity := .warn, kind := "unresolved_spec_of_target",
                    location := mkLoc i i line.length,
                    message  :=
                      s!"`{target}` does not resolve to any export of crate `{thisCrate}`"
                  }
          | _ => pure ()
        let startLine := st.attrStart.getD i
        let loc := mkLoc startLine i line.length
        if rawDoc.isEmpty then
          diags := diags.push {
            severity := .info, kind := "missing_docstring",
            location := loc,
            message  := s!"spec `{qname}` has no `/-- … -/` docstring"
          }
        else if informal.isNone then
          diags := diags.push {
            severity := .info, kind := "missing_informal_spec",
            location := loc,
            message  := s!"spec `{qname}` has no `Informal spec:` block"
          }
        let statementSlice := (dropPrefix (leftTrim line) 4)
        specs := specs.push {
          name      := qname,
          statement := statementSlice,
          docstring := { raw := rawDoc, prose := prose },
          informal  := informal,
          refs      := refs.toList,
          location  := loc
        }
      st := resetAttachables st
      i := i + 1
      continue
    -- 5. `theorem NAME`. Emit Verification iff a `@[proves …]` was seen.
    if let some name := takeTheorem line then
      let provesTarget : Option String := st.attrs.findSome? fun a =>
        match a with | .proves q => some q | _ => none
      match provesTarget with
      | some target =>
        let qname := qualify st.nsStack name
        let startLine := st.attrStart.getD i
        let loc := mkLoc startLine i line.length
        -- Walk forward to find the end of the proof body. Body ends at the
        -- last non-blank line before the next declaration boundary
        -- (`def `, `theorem `, `namespace `, `end `, top-level doc `/--`,
        -- or top-level attr `@[`). Stops at EOF.
        let bodyStart : Nat := i
        let mut j : Nat := i + 1
        let mut lastNonBlank : Nat := i
        while hJ : j < lines.size do
          let ln := lines[j]
          let tl := leftTrim ln
          let isBoundary :=
            tl.startsWith "def " ∨ tl.startsWith "theorem " ∨
            tl.startsWith "namespace " ∨ tl.startsWith "end " ∨
            tl.startsWith "/--" ∨ tl.startsWith "@["
          if isBoundary then
            break
          if ¬ tl.isEmpty then
            lastNonBlank := j
          j := j + 1
        let endLen := (lines[lastNonBlank]?).getD "" |>.length
        let bodySpan : Span :=
          { start := { line := bodyStart + 1, column := 1 },
            «end» := { line := lastNonBlank + 1, column := endLen + 1 } }
        verifs := verifs.push {
          name := qname, proves := target, resolved := false,
          location := loc, bodySpan := some bodySpan
        }
      | none => pure ()
      st := resetAttachables st
      i := i + 1
      continue
    -- 6. Any other non-blank line clears pending doc / attrs.
    if ¬ trimmed.isEmpty then
      st := resetAttachables st
    i := i + 1
  return { specs := specs, verifications := verifs, diagnostics := diags }

/-- Scan all Lean source files belonging to the crate. Resolves
verifications' `proves` targets against the union of specs discovered
across the crate, and emits `unresolved_proves_target` and
`unproven_spec` diagnostics as needed. -/
def scanCrate
    (sources : List SourceFile) (crateLeanRel : String)
    (thisCrate : String) (exportNames : List String) :
    FileFindings := Id.run do
  let mut specs : Array FormalSpec := #[]
  let mut verifs : Array Verification := #[]
  let mut diags : Array Diagnostic := #[]
  for f in sources do
    if f.language ≠ "lean" then continue
    let under :=
      f.filepath.startsWith (crateLeanRel ++ "/") ∨ f.filepath = crateLeanRel
    if ¬ under then continue
    let r := scanFile f.filepath f.body thisCrate exportNames
    specs := specs ++ r.specs
    verifs := verifs ++ r.verifications
    diags := diags ++ r.diagnostics
  let specNames := specs.map (·.name)
  let mut resolved : Array Verification := #[]
  for v in verifs do
    let ok := specNames.contains v.proves
    resolved := resolved.push { v with resolved := ok }
    if ¬ ok then
      diags := diags.push {
        severity := .warn, kind := "unresolved_proves_target",
        location := v.location,
        message  :=
          s!"`@[proves {v.proves}]` on `{v.name}` does not match any spec in this crate"
      }
  let provenTargets := (resolved.filter (·.resolved)).map (·.proves)
  for s in specs do
    if ¬ provenTargets.contains s.name then
      diags := diags.push {
        severity := .info, kind := "unproven_spec",
        location := s.location,
        message  := s!"spec `{s.name}` has no matching `@[proves]` theorem"
      }
  return { specs := specs, verifications := resolved, diagnostics := diags }

end Verifier.Extract.LeanScan
