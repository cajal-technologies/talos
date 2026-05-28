# `verifier extract` — extraction schema (WHAT)

This document defines **what** `verifier extract` produces. The **how**
(parsers, tree-sitter, Lean elaboration, attribute discovery) is out of
scope.

It assumes the project layout, file-naming, and tooling conventions
documented in [`README.md`](README.md). `extract` is a sibling of
`check`: same project root, same crate ↔ Lean dir mapping, same export
discipline.

---

## Command shape

```
verifier extract [--out DIR]
```

Run from a project root (the directory containing `rust/` and `lean/`),
exactly like `verifier check`. Walks every crate listed in
`rust/Cargo.toml`'s workspace members and emits **one flat JSON file
per crate** at `<DIR>/<crate>.json` (default `DIR = ./extracted/`).
JSON is pretty-printed for diffability.

Workspace-member discovery mirrors whatever `verifier check` already
does — whatever cargo accepts (literal names, glob patterns), extract
accepts.

A crate's identity in the artifact:

```
ProjectId:
  crate:  String   // cargo package name,          e.g. "is_even"
  rust:   String   // project-root-relative path,  e.g. "rust/is_even"
  lean:   String   // project-root-relative path,  e.g. "lean/Project/IsEven"
```

The `crate` ↔ `lean` pairing is by name convention only
(`foo_bar` ↔ `Project/FooBar`). There are no link files
(`verifier.toml` / `origin.toml` — explicitly **not** used).

---

## Prerequisites

`verifier extract` is structural — it walks files and elaborated Lean
declarations and records what it finds. It produces useful output only
when the codebase follows the conventions below. Anything missing is
recorded as a `diagnostic`, not a hard error (with the one exception
noted in P1).

### P1. Project shape (already required by `verifier check`)

The fixed `project/rust/` + `project/lean/` layout from `README.md`,
including:

- `rust/Cargo.toml` declaring a workspace with one member per crate.
- Each Lean directory contains at least `Program.lean` (auto-generated
  by `verifier check`).

For each workspace member, the matching `lean/Project/<Crate>/`
directory **should** exist. If it does not, the extractor emits an
`error`-severity `missing_lean_dir_for_crate` diagnostic and still
produces an artifact with the Rust side populated and empty
`specs`/`verifications`.

### P2. Exports live only in `src/exports.rs`

Every function the extractor lists under `exported` must be defined in
the crate's `src/exports.rs` with `#[unsafe(no_mangle)] pub extern "C"`.

Defining an exported symbol anywhere else (e.g. directly in `lib.rs`)
is not supported — the extractor will not pick it up and emits an
`export_outside_exports_rs` diagnostic if it sees one.

### P3. `Spec.lean` / `Proof.lean` is a *recommended* file split

The conventional shape — `Spec.lean` for `def Name : Prop := …` and
`Proof.lean` for `theorem _ : SpecName := …` — is the recommended
organization (see `README.md`). It is **not** load-bearing for the
extractor: the link between a spec and its proof is the `@[proves]`
attribute (P5), not file location.

A spec or verification may live in any `.lean` file under
`lean/Project/<Crate>/`. Files outside any crate's directory are
ignored.

### P4. The `@[spec_of …]` attribute marks formal specs

A `def Name : Prop := …` (optionally parameterized:
`def Name (x : T) (y : U) : Prop := …`) becomes a `FormalSpec` iff it
carries at least one `@[spec_of kind "qualified::name"]` attribute.
Defs without `@[spec_of]` are ignored — they are not specs, even when
their type is `Prop`.

Kinds:

- `"rust-exported"` — target written as `crate::fn_name`. Resolved by
  the extractor against this artifact's `exported`. A target naming a
  *different* crate's export is recorded with `resolved=false` and
  emits a `cross_crate_reference` info diagnostic; cross-crate
  resolution is a job for a later graph-builder pass.
- `"rust-internal"` — any other Rust path. Opaque to the extractor.
- `"lean"` — any Lean symbol. Opaque to the extractor.

Multiple `@[spec_of]` attributes on one def are allowed and yield
multiple `Reference` entries. A malformed attribute, or a
same-crate `rust-exported` target that doesn't resolve, emits a
diagnostic; the spec is still recorded.

### P5. The `@[proves SpecName]` attribute marks verifications

A `theorem` becomes a `Verification` iff it carries
`@[proves Spec.Namespace.SpecName]`, naming the `FormalSpec` it
discharges. The attribute is the link: the theorem's stated type need
not be syntactically identical to the spec (allows proof via
reformulation). An unresolved `proves` target emits a diagnostic; the
verification is still recorded.

A `Verification` is attributed to crate X iff its declaration lives
under `lean/Project/<X>/`. A `@[proves]` theorem outside any crate
directory is ignored and emits a `proves_outside_crate_dir`
diagnostic.

A `FormalSpec` with zero matching verifications is reported as
`unproven_spec` (info severity — an expected intermediate state).

### P6. Docstring conventions

- Every `FormalSpec` should carry a `/-- … -/` doc block immediately
  preceding the `def`. Only that form is honored — `--` line comments,
  `/-! … -/` module docstrings, and free-floating comments are
  ignored. Missing → `missing_docstring` (info).
- The doc block may contain an `Informal spec:` section:
  - Begins on a line matching `^Informal spec:\s*$`.
  - Extends to end of docstring.
  - Content stored as `informal`; everything else stored as `prose`.
- A spec with no `Informal spec:` block → `missing_informal_spec`
  (info).

### P7. Attribute definitions

The `@[spec_of]` and `@[proves]` attributes must be defined somewhere
in the dependency chain (`interpreter` or `codelib`). They are project
conventions the extractor relies on; their actual definitions are out
of scope for this document.

**Status at time of writing:** P4, P5, and the `@[spec_of]`/`@[proves]`
attribute definitions in P7 are **not yet in place** in the codebase.
Until they land, `verifier extract` produces empty `specs` and
`verifications` lists with diagnostics flagging the gap. P1, P2, P3,
P6 reflect existing or already-recommended state.

---

## Top-level artifact

```
Artifact:
  schema_version:     Int              // bumped on breaking changes
  extractor_version:  String           // semver of the `verifier` binary
  extracted_at:       String           // ISO-8601 UTC
  repo_commit:        String           // git HEAD sha; suffixed "-dirty"
                                       //   if the working tree differs
  toolchains:
    rustc:            String?          // edition from crate's Cargo.toml
    lean:             String           // from `lean/lean-toolchain`
  project:            ProjectId
  code:               List[SourceFile]
  exported:           List[ExportedFunction]
  program:            Program?
  specs:              List[FormalSpec]
  verifications:      List[Verification]
  diagnostics:        List[Diagnostic]
```

Extraction never fails on broken inputs; problems land in `diagnostics`.
Hard failure is reserved for unrecoverable I/O or schema-violating
output.

---

## Common types

### `Location`

```
Location:
  file:  String     // project-root-relative POSIX path
  span:  Span
```

### `Span`

1-indexed line and column. `end` is **exclusive** (points just past
the last character). Matches Lean LSP conventions.

```
Span:
  start: { line: Int, column: Int }
  end:   { line: Int, column: Int }
```

### `SourceFile`

```
SourceFile:
  filepath:    String     // project-root-relative POSIX path
  body:        String     // verbatim file content
  language:    String     // "rust" | "lean" | "toml" | "toolchain" | "wat" | "other"
  sha256:      String     // hex digest of body bytes
  git_blob:    String     // git blob sha (of HEAD blob, even if the
                          //   working tree is modified)
  last_commit: String     // last commit that touched the HEAD blob
                          //   ("" if the file is untracked)
  line_count:  Int
```

**Inclusion rule:** files that are (a) tracked by git, (b) under the
crate's `rust/<crate>/` dir or its matching `lean/Project/<Crate>/`
dir, AND (c) not on the exclusion list below.

**Exclusions:**

- `Cargo.lock` (workspace-level; not per-crate signal).
- `lake-manifest.json`, `lake-packages/`, `.lake/` (Lean build state).
- Anything under `rust/<crate>/target/`.
- Anything under `rust/build/<crate>/` **except** `program.wat`
  (the `.wasm` blob is binary; the `.wat` is included).

`Program.lean` is included verbatim despite being large and
auto-generated — keeping it lets a consumer reconstruct everything
the proofs see without re-running `verifier check`. Cheap for now;
revisit if module sizes explode.

**Languages:**

- `"rust"` — `.rs`
- `"lean"` — `.lean`
- `"toml"` — `.toml`
- `"toolchain"` — `lean-toolchain` (no extension)
- `"wat"` — `.wat`
- `"other"` — anything else (e.g. an `.md` README inside a crate)

---

## Rust side

### `ExportedFunction`

A function exported across the wasm ABI. Source: each
`#[unsafe(no_mangle)] pub extern "C" fn …` in `src/exports.rs`
(per P2). Functions outside that file are ignored (and emit
`export_outside_exports_rs` if they exist).

```
ExportedFunction:
  name:       String      // the symbol exported to wasm
  crate:      String      // cargo package name (matches ProjectId.crate)
  signature:  String      // verbatim slice: `fn` keyword through
                          //   return type, before the body `{`.
                          //   Whitespace preserved.
  docstring:  String      // concatenated `///` lines with leading `///`
                          //   (and one space) stripped; "" if no docs.
  location:   Location    // span covers the full item, including attributes
```

The `signature` slice deliberately omits the
`#[unsafe(no_mangle)] pub extern "C"` prefix because every entry in
`exports.rs` shares it by convention — it carries no per-function
information. Consumers needing the literal source can re-slice via
`location` against the file body in `code`.

---

## Lean side

### `Program`

```
Program:
  module:    String       // fully qualified def name,
                          //   e.g. "Project.IsEven.module"
  location:  Location     // span of the `def «module» : Module` decl
  body:      String       // verbatim source of the module definition
                          //   (the decl body, not the whole file)
```

`body` is kept even though `code` already contains the whole
`Program.lean`. The convenience of having the module decl directly
to hand outweighs the duplication while modules stay tens of KB.

### `FormalSpec`

A `def Name : Prop := …` (optionally parameterized) carrying at least
one `@[spec_of]` attribute, located anywhere under
`lean/Project/<Crate>/`. Per P4.

```
FormalSpec:
  name:       String           // fully qualified, e.g. "Project.IsEven.Spec.IsEvenSpec"
  statement:  String           // verbatim source slice from just after `def`
                               //   through the RHS of `:=` — i.e. binders +
                               //   `: Prop` + RHS. Excludes the `def` keyword
                               //   and trailing whitespace.
  docstring:
    raw:       String          // verbatim content of the `/-- … -/` block,
                               //   "" if none
    prose:     String          // raw with the `Informal spec:` block
                               //   (per P6) removed
  informal:   String?          // contents of the `Informal spec:` block;
                               //   null if absent
  refs:       List[Reference]  // from `@[spec_of …]` attribute(s);
                               //   always non-empty (at least one ref is
                               //   what made this a spec in the first place)
  location:   Location
```

### `Reference`

```
Reference:
  kind:     "rust-exported" | "rust-internal" | "lean"
  target:   String     // raw qualified name as written in the attribute
  resolved: Bool       // true iff kind == "rust-exported" AND target
                       //   names an entry in this artifact's `exported`.
                       //   Always false for "rust-internal", "lean", and
                       //   cross-crate "rust-exported" refs.
```

### `Verification`

A `theorem` carrying `@[proves SpecName]`, located under
`lean/Project/<Crate>/`. Per P5.

```
Verification:
  name:      String     // fully qualified theorem name
  proves:    String     // value of the `@[proves …]` attribute (FormalSpec name)
  resolved:  Bool       // true iff `proves` matches some `specs[].name`
                        //   in this artifact
  location:  Location
```

Multiple verifications may share the same `proves`.

---

## Diagnostics

```
Diagnostic:
  severity:  "info" | "warn" | "error"
  kind:      String           // stable enum
  location:  Location         // always present
  message:   String           // human-readable
```

| kind                              | severity | meaning                                                                     |
| --------------------------------- | -------- | --------------------------------------------------------------------------- |
| `missing_lean_dir_for_crate`      | error    | A workspace member has no matching `lean/Project/<Crate>/` directory.       |
| `missing_rust_crate_for_lean_dir` | warn     | A `lean/Project/<Crate>/` directory has no matching workspace member.       |
| `export_outside_exports_rs`       | warn     | A `#[unsafe(no_mangle)] pub extern "C"` fn was found outside `exports.rs`.  |
| `missing_docstring`               | info     | A `FormalSpec` has no `/-- … -/` block.                                     |
| `prereq_attributes_missing`       | info     | `@[spec_of]` / `@[proves]` infrastructure not yet in codelib (temporary).   |
| `missing_informal_spec`           | info     | A `FormalSpec` docstring has no `Informal spec:` block.                     |
| `unproven_spec`                   | info     | A `FormalSpec` has zero matching `@[proves]` verifications.                 |
| `unresolved_spec_of_target`       | warn     | A same-crate `rust-exported` target doesn't resolve to any export.          |
| `unresolved_proves_target`        | warn     | A `@[proves …]` target doesn't match any `FormalSpec` in this artifact.    |
| `cross_crate_reference`           | info     | A `rust-exported` ref names a different crate's export.                     |
| `malformed_spec_of_attribute`     | warn     | A `@[spec_of …]` attribute could not be parsed.                             |
| `malformed_proves_attribute`      | warn     | A `@[proves …]` attribute could not be parsed.                              |
| `proves_outside_crate_dir`        | warn     | A `@[proves]` theorem lives outside any `lean/Project/<Crate>/` dir.        |

---

## Non-goals

- No fuel, no execution traces, no proof-term bodies — just structural
  symbol metadata.
- Resolution is local to the crate. `rust-internal` and `lean` refs
  stay opaque; cross-crate `rust-exported` refs are recorded but not
  resolved. A later graph-builder pass that consumes these artifacts
  can do project-wide resolution.
- No parsing of free-form prose in docstrings beyond carving out the
  `Informal spec:` block.
