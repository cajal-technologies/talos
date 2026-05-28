import Verifier.Config
import Verifier.RustExtract

/-!
# Phase 4 — HTML report

`verifier report` writes a directory of static HTML that lets the user
browse every discovered project: rust exports, lean specs + proofs,
coverage, and the source files (rust + lean) navigable side-by-side.

Syntax highlighting is delegated to highlight.js loaded from a CDN —
the plan was to vendor a CodeMirror 6 bundle, but that requires an
external `npm`/`esbuild` step we can't run from inside Lean. The page
structure is forward-compatible with swapping in a bundled viewer later.

We deliberately keep this dependency-free at the Lean level: no JSON
parser, no template engine. The report consumes an in-memory
`ProjectData` array built by the check pipeline, and emits strings.
-/

namespace Verifier.Report

open System (FilePath)

/-- Everything we know about a single project, gathered by the check
pipeline before the report is rendered. -/
structure ProjectData where
  rustDir       : FilePath
  leanDir       : FilePath
  /-- Subfolder string inside the lean project, e.g. `"Programs/Crates/Itoa"`. -/
  subfolder     : String
  crate         : String
  buildOk       : Bool
  rustExports   : Array RustExtract.Export
  /-- Raw lean extractor JSON body (the `{"namespace", "specs", "proofs"}`
  string written into the sidecar). We don't parse it server-side — the
  per-project page embeds it as JSON in a `<script>` tag and a small
  vanilla-JS shim renders specs + proofs. -/
  leanJson      : String

/-- A safe filesystem slug for `subfolder` — `/` becomes `__`. -/
def projectSlug (p : ProjectData) : String :=
  p.subfolder.replace "/" "__"

-- ----------------------------------------------------------------------------
-- HTML helpers
-- ----------------------------------------------------------------------------

private def escapeHtml (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | '\'' => acc ++ "&#39;"
    | c   => acc.push c

private def escapeJsString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"'  => acc ++ "\\\""
    | '<'  => acc ++ "\\u003c"
    | '>'  => acc ++ "\\u003e"
    | '&'  => acc ++ "\\u0026"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | c    =>
      if c.toNat < 0x20 then acc ++ "\\u00" ++ String.ofList (Nat.toDigits 16 c.toNat)
      else acc.push c

-- ----------------------------------------------------------------------------
-- Assets (single bundled CSS string)
-- ----------------------------------------------------------------------------

private def stylesheet : String := "
* { box-sizing: border-box; }
body { font: 14px/1.45 -apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif; margin: 0; color: #1a1a1a; background: #fafafa; }
header { background: #1a1a1a; color: #fff; padding: 14px 24px; }
header h1 { margin: 0; font-size: 18px; font-weight: 600; }
header a { color: #9cf; text-decoration: none; }
header a:hover { text-decoration: underline; }
main { padding: 24px; max-width: 1200px; margin: 0 auto; }
h2 { font-size: 16px; margin: 24px 0 8px; padding-bottom: 4px; border-bottom: 1px solid #ddd; }
h3 { font-size: 14px; margin: 16px 0 8px; }
.project-card { background: #fff; border: 1px solid #ddd; border-radius: 6px; padding: 14px 18px; margin: 8px 0; }
.project-card a.title { font-weight: 600; color: #06c; text-decoration: none; font-size: 15px; }
.project-card a.title:hover { text-decoration: underline; }
.meta { color: #777; font-size: 12px; margin-top: 4px; }
.badge { display: inline-block; padding: 1px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }
.badge.ok { background: #e7f5ec; color: #1a7434; }
.badge.fail { background: #fbeae7; color: #b3271e; }
.badge.warn { background: #fff7e0; color: #8a6700; }
.export, .spec, .proof { background: #fff; border: 1px solid #e0e0e0; border-radius: 4px; padding: 10px 14px; margin: 6px 0; }
.export .name, .spec .name, .proof .name { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-weight: 600; font-size: 13px; }
.export .sig, .spec .stmt, .proof .stmt { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 12px; color: #444; background: #f5f5f5; padding: 6px 8px; border-radius: 3px; margin-top: 4px; overflow-x: auto; white-space: pre; }
.export .doc, .spec .doc, .proof .doc { color: #555; font-size: 13px; margin-top: 6px; }
.export .loc, .spec .loc, .proof .loc { font-size: 11px; color: #888; margin-top: 4px; }
.export .loc a, .spec .loc a, .proof .loc a { color: #06c; text-decoration: none; }
.export .loc a:hover, .spec .loc a:hover, .proof .loc a:hover { text-decoration: underline; }
pre.source { font: 12px/1.5 ui-monospace, SFMono-Regular, Menlo, monospace; background: #fff; border: 1px solid #ddd; padding: 12px; overflow-x: auto; counter-reset: line; }
pre.source code { display: block; }
.linenums { color: #aaa; user-select: none; text-align: right; padding-right: 12px; border-right: 1px solid #eee; min-width: 3em; display: inline-block; }
.coverage-table { width: 100%; border-collapse: collapse; }
.coverage-table th, .coverage-table td { padding: 6px 10px; border-bottom: 1px solid #eee; text-align: left; font-size: 12px; }
.coverage-table th { background: #f5f5f5; }
"

/-- The `<script>` shim that renders the per-project view from the
embedded JSON. -/
private def viewerScript : String := "
function renderProject(data) {
  const r = data.rustExports || [];
  const lean = data.lean || { specs: [], proofs: [] };
  const specs = lean.specs || [];
  const proofs = lean.proofs || [];

  const fmt = s => (s || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

  // Build a quick proof index by spec name.
  const proofsBySpec = {};
  proofs.forEach(p => {
    if (p.proves) (proofsBySpec[p.proves] = proofsBySpec[p.proves] || []).push(p);
  });

  // Rust exports.
  const re = document.getElementById('rust-exports');
  re.innerHTML = r.length === 0 ? '<p class=meta>No rust exports detected.</p>' :
    r.map(e => `
      <div class=export>
        <div class=name>${fmt(e.name)}</div>
        <div class=sig>${fmt(e.signature)}</div>
        ${e.doc ? `<div class=doc>${fmt(e.doc)}</div>` : ''}
        <div class=loc>${fmt(e.file)}:${e.line}</div>
      </div>`).join('');

  // Specs (with proofs nested).
  const se = document.getElementById('specs');
  se.innerHTML = specs.length === 0 ? '<p class=meta>No `def X : Prop` specs found.</p>' :
    specs.map(s => {
      const ps = proofsBySpec[s.name] || [];
      const proofBlock = ps.length === 0 ? '<div class=meta>No proof linked.</div>' :
        ps.map(p => `<div class=proof><span class='badge ok'>proved</span> <span class=name>${fmt(p.name)}</span></div>`).join('');
      return `
        <div class=spec>
          <div class=name>${fmt(s.name)}</div>
          <div class=stmt>${fmt(s.statement)}</div>
          ${s.doc ? `<div class=doc>${fmt(s.doc)}</div>` : ''}
          <div style='margin-top:8px'>${proofBlock}</div>
        </div>`;
    }).join('');

  // Standalone proofs (theorems with no def-spec).
  const stand = proofs.filter(p => !p.proves);
  const pe = document.getElementById('standalone-proofs');
  pe.innerHTML = stand.length === 0 ? '<p class=meta>None.</p>' :
    stand.map(p => `
      <div class=proof>
        <div class=name>${fmt(p.name)}</div>
        <div class=stmt>${fmt(p.type)}</div>
        ${p.doc ? `<div class=doc>${fmt(p.doc)}</div>` : ''}
      </div>`).join('');
}
"

-- ----------------------------------------------------------------------------
-- Per-source-file pages
-- ----------------------------------------------------------------------------

/-- Render a source file as a syntax-highlighted HTML page. `depth` is
the number of `../` segments needed to climb back to the report root
(so we can build correct relative links). -/
def renderSourcePage (depth : Nat) (langClass : String) (title : String)
    (content : String) : String :=
  let up := String.intercalate "" (List.replicate depth "../")
  String.intercalate "\n" [
    "<!doctype html>",
    "<html lang=en>",
    "<head>",
    "<meta charset=utf-8>",
    s!"<title>{escapeHtml title}</title>",
    s!"<link rel=stylesheet href='{up}assets/site.css'>",
    "<link rel=stylesheet href='https://cdn.jsdelivr.net/gh/highlightjs/cdn-release@11.10.0/build/styles/github.min.css'>",
    "<script src='https://cdn.jsdelivr.net/gh/highlightjs/cdn-release@11.10.0/build/highlight.min.js'></script>",
    "</head>",
    "<body>",
    "<header><h1><a href='" ++ up ++ "index.html'>← back</a> &nbsp;" ++ escapeHtml title ++ "</h1></header>",
    "<main>",
    s!"<pre class=source><code class='language-{langClass}'>{escapeHtml content}</code></pre>",
    "<script>hljs.highlightAll();</script>",
    "</main>",
    "</body></html>"
  ]

/-- Detect a highlight.js language class from a filename. -/
def detectLang (path : FilePath) : String :=
  let s := path.toString
  if s.endsWith ".rs" then "rust"
  else if s.endsWith ".lean" then "haskell" -- closest available; lean isn't a stock hljs lang
  else if s.endsWith ".toml" then "ini"
  else if s.endsWith ".wat" || s.endsWith ".wast" then "lisp"
  else "plaintext"

-- ----------------------------------------------------------------------------
-- Per-project page
-- ----------------------------------------------------------------------------

def renderProjectPage (p : ProjectData) : String :=
  let title := s!"{p.subfolder}"
  let okBadge := if p.buildOk then "<span class='badge ok'>build ok</span>"
                 else "<span class='badge fail'>build failed</span>"
  -- Serialise project data into an embedded JSON blob.
  let dataJson :=
    let rustJson := RustExtract.emitExports p.rustDir p.rustExports
    let leanInner :=
      if p.leanJson.trimAscii.toString.isEmpty
      then "{\"namespace\":\"\",\"specs\":[],\"proofs\":[]}"
      else p.leanJson.trimAscii.toString
    "{\"crate\":\"" ++ escapeJsString p.crate ++ "\""
      ++ ",\"rustExports\":" ++ rustJson
      ++ ",\"lean\":" ++ leanInner
      ++ "}"
  String.intercalate "\n" [
    "<!doctype html>",
    "<html lang=en>",
    "<head>",
    "<meta charset=utf-8>",
    s!"<title>{escapeHtml title}</title>",
    "<link rel=stylesheet href='../assets/site.css'>",
    "</head>",
    "<body>",
    "<header><h1><a href='../index.html'>← projects</a> &nbsp;" ++ escapeHtml title ++ " " ++ okBadge ++ "</h1></header>",
    "<main>",
    s!"<div class=meta>crate: <code>{escapeHtml p.crate}</code> · rust: <code>{escapeHtml p.rustDir.toString}</code></div>",
    "<h2>Rust exports</h2>",
    "<div id=rust-exports></div>",
    "<h2>Specifications</h2>",
    "<div id=specs></div>",
    "<h2>Standalone proofs</h2>",
    "<p class=meta>Theorems whose conclusion does not head-match any `def : Prop` spec.</p>",
    "<div id=standalone-proofs></div>",
    "<script>",
    s!"const DATA = {dataJson};",
    viewerScript,
    "renderProject(DATA);",
    "</script>",
    "</main>",
    "</body></html>"
  ]

-- ----------------------------------------------------------------------------
-- Index page
-- ----------------------------------------------------------------------------

private def coverageStats (p : ProjectData) : Nat × Nat × Nat :=
  -- (rustExports count, … placeholders for now)
  (p.rustExports.size, 0, 0)

def renderIndex (projects : Array ProjectData) : String :=
  let rows := projects.toList.map fun p =>
    let slug := projectSlug p
    let okBadge := if p.buildOk then "<span class='badge ok'>ok</span>"
                   else "<span class='badge fail'>fail</span>"
    let (nExports, _, _) := coverageStats p
    s!"<div class=project-card>\
       <a class=title href='project/{slug}.html'>{escapeHtml p.subfolder}</a> {okBadge}\
       <div class=meta>crate <code>{escapeHtml p.crate}</code> · {nExports} rust export(s)</div>\
       </div>"
  String.intercalate "\n" [
    "<!doctype html>",
    "<html lang=en>",
    "<head>",
    "<meta charset=utf-8>",
    "<title>verifier report</title>",
    "<link rel=stylesheet href='assets/site.css'>",
    "</head>",
    "<body>",
    "<header><h1>verifier report</h1></header>",
    "<main>",
    s!"<p class=meta>{projects.size} project(s) discovered.</p>",
    String.intercalate "\n" rows,
    "</main>",
    "</body></html>"
  ]

-- ----------------------------------------------------------------------------
-- File I/O helpers
-- ----------------------------------------------------------------------------

private def writeFile (p : FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then IO.FS.createDirAll parent
  IO.FS.writeFile p content

/-- Walk source files (rust + lean) for a project and render each as a
syntax-highlighted page under `outDir/source/<slug>/<rel>.html`. -/
def writeSourcePages (outDir : FilePath) (p : ProjectData) : IO Unit := do
  let slug := projectSlug p
  let sourceRoot := outDir / "source" / slug
  -- Rust files.
  let rustFiles ← RustExtract.listRustFiles p.rustDir
  for f in rustFiles do
    let text ← try IO.FS.readFile f catch _ => pure ""
    let relStr := (f.toString.drop (p.rustDir.toString.length + 1)).toString
    -- depth from this page to report root: source/<slug>/rust/<rel> → count
    -- of `/` in (slug + rust + rel) gives total path segments after root.
    let segs := (relStr.splitOn "/").length + 2  -- +2 for "source/<slug>"
    let html := renderSourcePage segs (detectLang f) ("rust:" ++ relStr) text
    writeFile (sourceRoot / "rust" / (relStr ++ ".html")) html
  -- Lean files in the subfolder.
  let subDir := p.leanDir / p.subfolder
  let leanFiles ← do
    let mut out : Array FilePath := #[]
    let entries ← try subDir.readDir catch _ => pure #[]
    for entry in entries do
      let name := entry.fileName
      if name.endsWith ".lean" then out := out.push entry.path
    pure out
  for f in leanFiles do
    let text ← try IO.FS.readFile f catch _ => pure ""
    let rel := f.fileName.getD "file.lean"
    -- Lean files all sit directly in source/<slug>/lean/ → depth 3.
    let html := renderSourcePage 3 (detectLang f) ("lean:" ++ rel) text
    writeFile (sourceRoot / "lean" / (rel ++ ".html")) html

/-- Top-level: write index + per-project pages + source pages + CSS. -/
def writeReport (outDir : FilePath) (projects : Array ProjectData) : IO Unit := do
  IO.FS.createDirAll outDir
  writeFile (outDir / "assets" / "site.css") stylesheet
  writeFile (outDir / "index.html") (renderIndex projects)
  for p in projects do
    let slug := projectSlug p
    writeFile (outDir / "project" / (slug ++ ".html")) (renderProjectPage p)
    writeSourcePages outDir p

end Verifier.Report
