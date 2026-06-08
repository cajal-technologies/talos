# Root of the monorepo.
ROOT := justfile_directory()
set shell := ["bash", "-euo", "pipefail", "-c"]

[private]
default:
    @just --list --unsorted

# Pinned wasm-tools version. Testsuite shells out to `wasm-tools json-from-wast`
# to split .wast files; different versions can produce different decodes —
# bumping this needs a regenerated testsuite_report.txt.
WASM_TOOLS_VERSION := "1.251.0"


# ── Lean package builds ───────────────────────────────────────────────────────

# Build all three packages. Programs depends on CodeLib which depends on Interpreter,
# so a single Lake workspace invocation covers the full chain without rebuilding
# Interpreter twice (which happens when each package is built as a separate root).
# Interpreter executables (runner, testsuite) are built by their own recipes below.
[working-directory("programs/lean")]
build: lake-shared
    lake build

[private]
[working-directory("interpreter")]
lake-shared:
    lake update
    lake exe cache get

# Build the interpreter package (Wasm AST + semantics + WP tactic layer).

[group("build")]
[working-directory("interpreter")]
build-interpreter:
    lake build

# Build the codelib package (lifting lemmas + reasoning helpers).
[group("build")]
[working-directory("codelib")]
build-codelib:
    lake build

# Build the programs package (concrete Rust-to-Wasm proofs). This is the main
# proof target: it depends on codelib which depends on interpreter, so one
# invocation covers the full dependency chain without redundant rebuilds.
[group("build")]
[working-directory("programs/lean")]
build-programs:
    lake build

# Build the verifier tool (scaffolder + WAT emitter + proof checker).
[group("build")]
[working-directory("verifier")]
build-verifier:
    lake build


# ── Rust workspace ────────────────────────────────────────────────────────────


[private]
[working-directory("programs/rust")]
cargo-programs +args:
    cargo {{ args }}

# Build all Rust crates in release mode (produces .wasm output under rust/build/).
[group("rust-programs")]
rust-build: (cargo-programs "build")

# Run all Rust unit tests.
[group("rust-programs")]
rust-test: (cargo-programs "test")

# Run clippy lints across the Rust workspace.
[group("rust-programs")]
rust-lint: (cargo-programs "clippy")

# ── runner ────────────────────────────────────────────────────────────────────

# Build the Wasm runner executable.
[group("runner")]
[working-directory("interpreter")]
runner-build:
    lake build runner

# Smoke-test the runner executable against samples/.
[group("runner")]
[working-directory("scripts")]
runner-smoke:
    ./runner-smoke.sh

# Run the runner executable against samples/.
[group("runner")]
[working-directory("interpreter")]
runner-run +args:
    lake exe runner {{ args }}

# ── testsuite ─────────────────────────────────────────────────────────────────

# Run the WebAssembly spec testsuite (vendor/testsuite/). Optional pattern
# is a case-sensitive substring on the .wast filename stem.
[group("testsuite")]
[working-directory(ROOT)]
testsuite pattern="":
    scripts/testsuite.sh {{ quote(pattern) }}

# Regenerate testsuite_report.txt at the repo root. CI runs the same command
# and fails if the working tree drifts, so contributors whose changes shift
# coverage must commit the updated report.
[group("testsuite")]
[working-directory(ROOT)]
testsuite-report:
    WASM_TOOLS_VERSION={{ quote(WASM_TOOLS_VERSION) }} scripts/testsuite-report.sh

# ── verifier workflow ─────────────────────────────────────────────────────────
# All verifier recipes run from programs/ (project root: rust/ + lean/).
# Omit crate names to operate on all workspace crates.
#
# Step-by-step development cycle:
#   just verifier-init <path>   — scaffold a new project
#   just verifier-build         — compile Rust → wasm/wat
#   just verifier-emit          — transpile wat → Program.lean + scaffold Spec.lean
#   [edit Spec.lean by hand]
#   just verifier-prove         — run lake build to check proofs
#
# Or combined: just verifier-check [--force-emit] [--no-prove] [crate…]

[private]
[working-directory("programs")]
_verifier +args:
    lake -d ../verifier exe verifier {{ args }}

# Scaffold a new verification project at <path> (relative to programs/).
[group("verifier")]
verifier-init path:
    just _verifier init {{ path }}

# Remove a crate from the current project (source, lean module, build artefacts, config references).
[group("verifier")]
verifier-del crate:
    just _verifier del {{ crate }}

# Build wasm/wat for selected crates; omit names to process all.
[group("verifier")]
verifier-build *crates:
    just _verifier build {{ crates }}

# Transpile program.wat → Program.lean and scaffold Spec.lean; omit names for all.
# Flag: --force-emit (re-emit when wasm is unchanged). Example: just verifier-emit --force-emit is_even
[group("verifier")]
verifier-emit *crates:
    just _verifier emit {{ crates }}

# Run lake build on selected crates' Lean modules; omit names for all.
[group("verifier")]
verifier-prove *crates:
    just _verifier prove {{ crates }}

# Full pipeline: build → emit → prove for selected crates; omit names for all.
# Flags: --force-emit, --no-prove. Example: just verifier-check --force-emit is_even
[group("verifier")]
verifier-check *args:
    just _verifier check {{ args }}

# Extract JSON metadata per crate; omit names for all.
# Flags: --out DIR (output directory, default ./extracted).
[group("verifier")]
verifier-extract *crates:
    just _verifier extract {{ crates }}

# Build the static HTML progress report (requires npm in verifier/report/).
# Accepts an optional crate filter and flags: --extracted DIR, --out DIR.
[group("verifier")]
verifier-report *crate:
    just _verifier report {{ crate }}

# ── docs ──────────────────────────────────────────────────────────────────────

# Generate HTML documentation and serve it at http://localhost:8080.
[working-directory("scripts")]
docs:
    ./docs.sh

# ── housekeeping ──────────────────────────────────────────────────────────────

# Remove Lake build artefacts from all Lean packages and Cargo target dir.
[working-directory("scripts")]
clean:
    ./clean.sh

