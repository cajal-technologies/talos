# verifier

A small Lean CLI that drives the Rust → wasm → Lean verification loop
for projects in this repo. Given a Rust crate and a sibling Lean
subfolder, it builds the wasm binary, emits a `Program.lean`
translation, runs `lake build`, extracts symbols from both sides, and
(optionally) renders an interactive HTML report.

## Build

```bash
cd verifier
lake build       # produces .lake/build/bin/verifier
```

## Project layout

Each verified item is a pair of directories:

```
project/
  rust/
    foo/
      Cargo.toml
      src/lib.rs
      verifier.toml         ← points at the Lean side
  Project/
    Foo/
      origin.toml           ← points back at the Rust side
      Spec.lean             ← `def MyProp : Prop := …` statements
      Proofs.lean           ← `theorem _ : MyProp := …` proofs
      Program.lean          ← auto-generated, do not edit
      module.wat            ← auto-generated
    Project.lean            ← the umbrella library root
  lakefile.toml             ← one umbrella Lean project per repo
```

`verifier.toml` (minimal):

```toml
lean_project = "../../.."
verification_folder = "Project/Foo"
# Optional:
# build_command  = "cargo build --release --target wasm32-unknown-unknown"
# build_artifact = "target/wasm32-unknown-unknown/release/{crate}.wasm"
```

## Tutorial

### 1. Bootstrap a new project

You wrote a Rust crate at `rust/foo/` and want a Lean verification
subfolder at `Project/Foo`:

```bash
lake exe verifier new rust/foo Project Foo
```

This scaffolds:
- `rust/foo/verifier.toml` pointing at `../../Project` with subfolder `Foo`.
- `Project/Foo/origin.toml` pointing back at `rust/foo`.
- `Project/Foo/Spec.lean` — empty stub with the `def MyProp : Prop` pattern.
- `Project/Foo/Proofs.lean` — empty stub with the `theorem _ : MyProp := …` pattern.
- `import Project.Foo.Proofs` appended to `Project.lean` (creates the file if missing).

If `Project/` doesn't exist yet, `verifier new` also scaffolds the
umbrella Lean project (lakefile.toml, lean-toolchain copied from
`codelib/`, library root file).

### 2. Build + check one project

```bash
lake exe verifier check rust/foo
```

Pipeline:
1. `cargo build --release --target wasm32-unknown-unknown` (or the
   `build_command` from `verifier.toml`).
2. `wasm-tools strip --all` then `wasm-tools print` → `Project/Foo/module.wat`.
3. In-process wat → `Wasm.Module` decoder → write `Project/Foo/Program.lean`.
4. `lake build` on the umbrella project.
5. Run the symbol extractor; write `Project/Foo/.verifier-extract.json`.

Add `--no-build` to skip steps 4–5 when you're iterating on the Rust
side and don't need the Lean parts re-checked.

### 3. Check everything at once

Run with no path argument from anywhere under the repo root:

```bash
lake exe verifier check
```

This walks the cwd looking for every `verifier.toml` (pruning `target/`,
`.lake/`, `.git/`, …), groups the discovered crates by their umbrella
Lean project, and runs the pipeline once per crate with **one**
`lake build` per umbrella. Errors are collected and printed in a
summary at the end — one bad project doesn't stop the others.

### 4. Generate the HTML report

```bash
lake exe verifier report                    # writes ./verifier-report/
lake exe verifier report --out my-report    # custom output dir
lake exe verifier report --no-build         # skip lake build (rust-only view)
```

The report directory is self-contained:

```
verifier-report/
  index.html                                  ← project list
  project/<slug>.html                         ← per-project view
  source/<slug>/{rust,lean}/<rel>.html        ← syntax-highlighted source files
  assets/site.css
```

Per-project pages render rust exports, formal specs (`def X : Prop`),
proofs (linked to specs by head-symbol match), and standalone theorems.
Source pages use highlight.js loaded from a CDN — opening the report
needs internet the first time; cache it after that.

### 5. Writing specs and proofs

`Spec.lean` (statements as `def : Prop`):

```lean
import Project.Foo.Program

namespace Project.Foo.Spec
open Wasm

/-- The exported `foo` function returns its input unchanged. -/
def FooIsIdentity : Prop :=
  ∀ (initial : Store) (n : UInt32),
    TerminatesWith «module» 0 initial [.i32 n] (fun _ rs => rs = [.i32 n])

end Project.Foo.Spec
```

`Proofs.lean` (theorems that close those statements):

```lean
import Project.Foo.Spec

namespace Project.Foo.Proofs
open Project.Foo.Spec

theorem foo_is_identity : FooIsIdentity := by
  intro initial n
  -- … your proof …

end Project.Foo.Proofs
```

The extractor links `foo_is_identity` to `FooIsIdentity` automatically
because the theorem's conclusion (after stripping `∀`-binders) has
head symbol `FooIsIdentity`. The report shows them side-by-side with
a `proved` badge.

Theorems whose conclusion isn't a known `def : Prop` — e.g. the
"theorem-with-inline-Prop" style used by some existing projects — are
still surfaced under **Standalone proofs**, so you don't have to
refactor existing code to see it in the report.

## Commands

```
verifier new    <rust-path> <lean-path> <subfolder> [--codelib <path>]
verifier check  [path] [--no-build]
verifier report [--out <dir>] [--no-build]
```

- `path` for `check` is optional. Without it, every `verifier.toml`
  under cwd is processed.
- `verifier new` is the only command that doesn't require an existing
  `verifier.toml` (it creates the first one).

### CodeLib source (for `new`)

Scaffolding writes a `lakefile.toml` that requires the `CodeLib`
package (the wasm interpreter + `wp` tactic your specs build on).
By default the scaffold points at the public GitHub remote so the
new project is self-contained — no Talos checkout needed on disk:

```toml
[[require]]
name = "CodeLib"
git = "https://github.com/cajal-technologies/talos"
subDir = "codelib"
rev = "main"
```

The matching `lean-toolchain` is fetched live from
`raw.githubusercontent.com` during `verifier new` (one `curl`).

Overrides:

- `--codelib-rev <rev>` — pin a specific commit/tag instead of `main`
  for reproducibility.
- `--codelib <path>` — use a local checkout (writes `path = "..."`
  in the lakefile). Useful when developing Talos itself.
- `TALOS_CODELIB` env var — same as `--codelib`.

`--codelib` and `TALOS_CODELIB` both require the path to contain a
`lean-toolchain` file.

## Sidecar JSON

After every `check`, each project writes
`<lean-subfolder>/.verifier-extract.json` (gitignored). Shape:

```json
{
  "project": { "rustDir": "...", "leanDir": "...", "subfolder": "...", "crate": "..." },
  "buildOk": true,
  "rustExports": [
    { "name": "foo", "signature": "pub extern \"C\" fn foo(...) -> ...",
      "doc": "...", "file": "src/lib.rs", "line": 12 }
  ],
  "lean": {
    "namespace": "Project.Foo",
    "specs":  [{ "name": "...", "statement": "...", "doc": "..." }],
    "proofs": [{ "name": "...", "proves": "...", "type": "...", "doc": "..." }]
  }
}
```

This is the documented integration point for downstream tooling — the
report consumes it, and so can anything else.

## Tooling required

- `cargo` with the `wasm32-unknown-unknown` target installed
  (`rustup target add wasm32-unknown-unknown`)
- [`wasm-tools`](https://github.com/bytecodealliance/wasm-tools)
  (`brew install wasm-tools` or `cargo install wasm-tools`)
- `lake` (comes with the Lean toolchain pinned in `verifier/lean-toolchain`)
