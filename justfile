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

# Run the verifier check from the programs/ root (builds Rust, re-emits
# Program.lean files if wasm changed, then runs lake build).
[working-directory("verifier")]
verifier-check:
    lake exe verifier check

# Re-emit all Program.lean files unconditionally, then run lake build.
[working-directory("verifier")]
verifier-check-force:
    lake exe verifier check --force-emit

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

