/-!
# Phase 3 — Rust source extraction (line scanner)

The original plan was to drive `lean4-tree-sitter`, but its v0.1.0 only
ships Java/Python/Kotlin grammars (no Rust); adding a Rust `GrammarSpec`
would be a multi-day side quest. We fall back to a deliberately small
line-based scanner that recognises only the surface idiom we actually
care about: `pub fn` / `pub extern "C" fn` items preceded by `///`
doc lines.

This handles the common case ("`pub fn name(args) -> ret`" on a single
line, optionally with `extern "C"`, optionally with leading
`#[no_mangle]` attributes), is robust enough for the existing
`programs/rust/**` projects, and ships without external native deps.
Fancy Rust (generics with nested `>`, multi-line signatures, macros
generating exports) is out of scope; the report will simply miss those.
-/

namespace Verifier.RustExtract

open System (FilePath)

/-- One extracted export. -/
structure Export where
  /-- Item name (the identifier after `fn`). -/
  name      : String
  /-- Verbatim signature line(s), trimmed. -/
  signature : String
  /-- Concatenated `///` doc lines (without the leading slashes), or
  empty if none. -/
  doc       : String
  /-- Source file (absolute path). -/
  file      : FilePath
  /-- 1-indexed line of the `pub fn …` line. -/
  line      : Nat
  deriving Inhabited, Repr

/-- Whitespace predicate. -/
private def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- Trim leading + trailing ASCII whitespace. -/
private def trim (s : String) : String :=
  let cs := s.toList.dropWhile isWs
  String.ofList (cs.reverse.dropWhile isWs).reverse

/-- Strip an exact leading prefix. -/
private def stripPrefix? (s p : String) : Option String :=
  if s.startsWith p then some (s.drop p.length).toString else none

/-- Is this trimmed line a Rust attribute (`#[…]` or `#![…]`)? -/
private def isAttr (line : String) : Bool :=
  line.startsWith "#[" || line.startsWith "#!["

/-- Pull the function name out of a signature line that has already
been determined to begin with `pub fn` (or `pub extern \"…\" fn`). -/
private def extractName? (sig : String) : Option String :=
  -- find " fn " and read the identifier that follows
  let cs := sig.toList
  -- look for a substring " fn " then read identifier chars
  let rec scan : List Char → Option (List Char)
    | ' ' :: 'f' :: 'n' :: ' ' :: rest => some rest
    | _ :: rest => scan rest
    | []        => none
  match scan cs with
  | none => none
  | some after =>
    let after := after.dropWhile isWs
    let ident := after.takeWhile (fun c => c.isAlphanum || c = '_')
    if ident.isEmpty then none else some (String.ofList ident)

/-- Identify a `pub fn …` line. Returns the (trimmed) line if it is one,
together with the extracted function name. We also accept `pub extern
"…" fn` and tolerate `unsafe`/`async`/`const` modifiers between `pub`
and `fn`. -/
private def matchPubFn? (rawLine : String) : Option String :=
  let line := trim rawLine
  if line.startsWith "pub fn " then extractName? line
  else if line.startsWith "pub extern " || line.startsWith "pub unsafe "
          || line.startsWith "pub async " || line.startsWith "pub const " then
    extractName? line
  else none

/-- Walk lines of a single source file, collecting exports. -/
def scanSource (file : FilePath) (text : String) : Array Export := Id.run do
  let lines := text.splitOn "\n"
  let mut out : Array Export := #[]
  let mut docBuf : Array String := #[]
  -- Lines are 0-indexed here; we expose 1-indexed positions.
  let mut idx : Nat := 0
  for raw in lines do
    let line := trim raw
    if line.isEmpty then
      -- Blank lines do NOT clear the doc buffer (rust convention allows
      -- a blank between `#[attr]` and `pub fn`, but doc comments must
      -- be contiguous; still, a blank between two pub items happens).
      idx := idx + 1
      continue
    -- Doc comments accumulate.
    if let some body := stripPrefix? line "///" then
      docBuf := docBuf.push (trim body)
    else if let some body := stripPrefix? line "//!" then
      docBuf := docBuf.push (trim body)
    else if isAttr line then
      -- Attributes are transparent: keep the doc buffer.
      pure ()
    else if let some name := matchPubFn? line then
      let doc := String.intercalate "\n" docBuf.toList
      -- Strip everything from the opening `{` (body start) onward.
      let sig :=
        match (line.toList.takeWhile (· ≠ '{')) with
        | [] => line
        | cs => trim (String.ofList cs)
      out := out.push {
        name := name, signature := sig, doc := doc,
        file := file, line := idx + 1
      }
      docBuf := #[]
    else if line.startsWith "//" then
      -- Plain `//` comment: clear the buffer (it's not a doc comment).
      docBuf := #[]
    else
      -- Any other code line clears the doc buffer.
      docBuf := #[]
    idx := idx + 1
  pure out

/-- Recursively collect every `.rs` file under `root`, pruning the
usual cargo/build dirs. -/
partial def listRustFiles (root : FilePath) : IO (Array FilePath) := do
  let pruned : List String := ["target", ".git", "node_modules"]
  let mut out : Array FilePath := #[]
  let mut stack : Array FilePath := #[root]
  while !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    let entries ← try cur.readDir catch _ => pure #[]
    for entry in entries do
      let name := entry.fileName
      if pruned.contains name then continue
      if name.startsWith "." then continue
      let p := entry.path
      let isDir ← try p.isDir catch _ => pure false
      if isDir then
        stack := stack.push p
      else if name.endsWith ".rs" then
        out := out.push p
  pure out

/-- Scan every `.rs` file under `rustDir` and concatenate the results. -/
def scanProject (rustDir : FilePath) : IO (Array Export) := do
  let files ← listRustFiles rustDir
  let mut out : Array Export := #[]
  for f in files do
    let text ← try IO.FS.readFile f catch _ => pure ""
    out := out ++ scanSource f text
  pure out

-- ----------------------------------------------------------------------------
-- JSON rendering
-- ----------------------------------------------------------------------------

private def escapeJsonString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'   => acc ++ "\\\""
    | '\\'  => acc ++ "\\\\"
    | '\n'  => acc ++ "\\n"
    | '\r'  => acc ++ "\\r"
    | '\t'  => acc ++ "\\t"
    | c     =>
      if c.toNat < 0x20 then acc ++ "\\u00" ++ (toString c.toNat)
      else acc.push c

private def jstr (s : String) : String := "\"" ++ escapeJsonString s ++ "\""

/-- Render one export as a JSON object. -/
def emitExport (rootDir : FilePath) (e : Export) : String :=
  -- Make file paths relative to the rust project root for stable output.
  let rel : String :=
    let r := rootDir.toString
    let f := e.file.toString
    if f.startsWith r then (f.drop (r.length + 1)).toString else f
  "{\"name\":" ++ jstr e.name
    ++ ",\"signature\":" ++ jstr e.signature
    ++ ",\"doc\":" ++ jstr e.doc
    ++ ",\"file\":" ++ jstr rel
    ++ ",\"line\":" ++ toString e.line
    ++ "}"

/-- Render all exports as a JSON array string. -/
def emitExports (rootDir : FilePath) (es : Array Export) : String :=
  "[" ++ String.intercalate "," (es.toList.map (emitExport rootDir)) ++ "]"

end Verifier.RustExtract
