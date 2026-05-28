import Lean.Data.Json

/-!
# Extract schema — Lean mirror of `verifier/EXTRACT.md`

Pure data types + `toJson` converters into `Lean.Json`. Field names use
camelCase in Lean; the JSON keys are the snake_case names from
`EXTRACT.md`. Hand-rolled conversion (rather than `ToJson` derivation)
keeps the JSON output stable and easy to scan.
-/

namespace Verifier.Extract2

open Lean (Json)

/-- 1-indexed line + column. -/
structure Position where
  line   : Nat
  column : Nat
  deriving Inhabited, Repr

/-- LSP-style span: `start` inclusive, `end` exclusive. -/
structure Span where
  start    : Position
  «end»    : Position
  deriving Inhabited, Repr

structure Location where
  file : String
  span : Span
  deriving Inhabited, Repr

structure ProjectId where
  crate : String
  rust  : String
  lean  : String
  deriving Inhabited, Repr

structure Toolchains where
  rustc : Option String
  lean  : String
  deriving Inhabited, Repr

structure SourceFile where
  filepath   : String
  body       : String
  language   : String     -- "rust" | "lean" | "toml" | "toolchain" | "wat" | "other"
  sha256     : String
  gitBlob    : String
  lastCommit : String
  lineCount  : Nat
  deriving Inhabited, Repr

structure ExportedFunction where
  name      : String
  «crate»   : String
  signature : String
  docstring : String
  location  : Location
  deriving Inhabited, Repr

structure Program where
  module   : String
  location : Location
  body     : String
  deriving Inhabited, Repr

inductive RefKind
  | rustExported
  | rustInternal
  | leanSym
  deriving Inhabited, Repr

def RefKind.toString : RefKind → String
  | .rustExported => "rust-exported"
  | .rustInternal => "rust-internal"
  | .leanSym      => "lean"

structure Reference where
  kind     : RefKind
  target   : String
  resolved : Bool
  deriving Inhabited, Repr

structure Docstring where
  raw   : String
  prose : String
  deriving Inhabited, Repr

structure FormalSpec where
  name      : String
  statement : String
  docstring : Docstring
  informal  : Option String
  refs      : List Reference
  location  : Location
  deriving Inhabited, Repr

structure Verification where
  name     : String
  proves   : String
  resolved : Bool
  location : Location
  deriving Inhabited, Repr

inductive Severity
  | info
  | warn
  | error
  deriving Inhabited, Repr

def Severity.toString : Severity → String
  | .info  => "info"
  | .warn  => "warn"
  | .error => "error"

structure Diagnostic where
  severity : Severity
  kind     : String
  location : Location
  message  : String
  deriving Inhabited, Repr

structure Artifact where
  schemaVersion    : Nat
  extractorVersion : String
  extractedAt      : String
  repoCommit       : String
  toolchains       : Toolchains
  project          : ProjectId
  code             : List SourceFile
  exported         : List ExportedFunction
  program          : Option Program
  specs            : List FormalSpec
  verifications    : List Verification
  diagnostics      : List Diagnostic
  deriving Inhabited

/-! ## JSON encoding -/

private def jNat (n : Nat) : Json := .num ⟨(n : Int), 0⟩

private def jStr (s : String) : Json := .str s

private def jOptStr : Option String → Json
  | none   => .null
  | some s => .str s

def Position.toJson (p : Position) : Json :=
  .mkObj [("line", jNat p.line), ("column", jNat p.column)]

def Span.toJson (s : Span) : Json :=
  .mkObj [("start", s.start.toJson), ("end", s.end.toJson)]

def Location.toJson (l : Location) : Json :=
  .mkObj [("file", jStr l.file), ("span", l.span.toJson)]

def ProjectId.toJson (p : ProjectId) : Json :=
  .mkObj [("crate", jStr p.crate), ("rust", jStr p.rust), ("lean", jStr p.lean)]

def Toolchains.toJson (t : Toolchains) : Json :=
  .mkObj [("rustc", jOptStr t.rustc), ("lean", jStr t.lean)]

def SourceFile.toJson (f : SourceFile) : Json :=
  .mkObj [
    ("filepath",    jStr f.filepath),
    ("body",        jStr f.body),
    ("language",    jStr f.language),
    ("sha256",      jStr f.sha256),
    ("git_blob",    jStr f.gitBlob),
    ("last_commit", jStr f.lastCommit),
    ("line_count",  jNat f.lineCount)
  ]

def ExportedFunction.toJson (e : ExportedFunction) : Json :=
  .mkObj [
    ("name",      jStr e.name),
    ("crate",     jStr e.crate),
    ("signature", jStr e.signature),
    ("docstring", jStr e.docstring),
    ("location",  e.location.toJson)
  ]

def Program.toJson (p : Program) : Json :=
  .mkObj [
    ("module",   jStr p.module),
    ("location", p.location.toJson),
    ("body",     jStr p.body)
  ]

def Reference.toJson (r : Reference) : Json :=
  .mkObj [
    ("kind",     jStr r.kind.toString),
    ("target",   jStr r.target),
    ("resolved", .bool r.resolved)
  ]

def Docstring.toJson (d : Docstring) : Json :=
  .mkObj [("raw", jStr d.raw), ("prose", jStr d.prose)]

def FormalSpec.toJson (s : FormalSpec) : Json :=
  .mkObj [
    ("name",      jStr s.name),
    ("statement", jStr s.statement),
    ("docstring", s.docstring.toJson),
    ("informal",  jOptStr s.informal),
    ("refs",      .arr (s.refs.map Reference.toJson).toArray),
    ("location",  s.location.toJson)
  ]

def Verification.toJson (v : Verification) : Json :=
  .mkObj [
    ("name",     jStr v.name),
    ("proves",   jStr v.proves),
    ("resolved", .bool v.resolved),
    ("location", v.location.toJson)
  ]

def Diagnostic.toJson (d : Diagnostic) : Json :=
  .mkObj [
    ("severity", jStr d.severity.toString),
    ("kind",     jStr d.kind),
    ("location", d.location.toJson),
    ("message",  jStr d.message)
  ]

def Artifact.toJson (a : Artifact) : Json :=
  .mkObj [
    ("schema_version",    jNat a.schemaVersion),
    ("extractor_version", jStr a.extractorVersion),
    ("extracted_at",      jStr a.extractedAt),
    ("repo_commit",       jStr a.repoCommit),
    ("toolchains",        a.toolchains.toJson),
    ("project",           a.project.toJson),
    ("code",              .arr (a.code.map SourceFile.toJson).toArray),
    ("exported",          .arr (a.exported.map ExportedFunction.toJson).toArray),
    ("program",           a.program.elim .null Program.toJson),
    ("specs",             .arr (a.specs.map FormalSpec.toJson).toArray),
    ("verifications",     .arr (a.verifications.map Verification.toJson).toArray),
    ("diagnostics",       .arr (a.diagnostics.map Diagnostic.toJson).toArray)
  ]

/-- Current artifact schema version. Bump on breaking changes. -/
def schemaVersion : Nat := 1

/-- Current extractor binary semver. -/
def extractorVersion : String := "0.1.0"

end Verifier.Extract2
