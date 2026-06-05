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
runner-smoke:
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}/interpreter"
    lake build runner

    fail=0

    check() {
        local name="$1"; shift
        local want_exit="$1"; shift
        local want_stream="$1"; shift  # "stdout" or "stderr"
        local want="$1"; shift
        local got got_exit
        if [[ "$want_stream" == stdout ]]; then
            got=$(./.lake/build/bin/runner "$@" 2>/dev/null) && got_exit=0 || got_exit=$?
        else
            got=$(./.lake/build/bin/runner "$@" 2>&1 >/dev/null) && got_exit=0 || got_exit=$?
        fi
        if [[ "$got_exit" != "$want_exit" || "$got" != "$want" ]]; then
            echo "FAIL: $name"
            echo "  cmd:    ./.lake/build/bin/runner $*"
            echo "  expect: exit=$want_exit $want_stream=[$want]"
            echo "  got:    exit=$got_exit $want_stream=[$got]"
            fail=1
        else
            echo "ok: $name"
        fi
    }

    check "sum_to.wat"        0 stdout "55"                          samples/sum_to.wat sum_to 10
    check "factorial.wat"     0 stdout "120"                         samples/factorial.wat fact 5
    check "trap.wat"          1 stderr "trap: integer divide by zero" samples/trap.wat div_by_zero
    check "out-of-fuel"       2 stderr "out of fuel"                  samples/sum_to.wat sum_to 1000000 --fuel 10

    if command -v wasm-tools >/dev/null 2>&1; then
        tmpdir=$(mktemp -d -t runner-smoke.XXXXXX)
        trap 'rm -rf "$tmpdir"' EXIT
        tmp="$tmpdir/sum_to.wasm"
        wasm-tools parse samples/sum_to.wat -o "$tmp"
        check "sum_to.wasm via wasm-tools" 0 stdout "55" "$tmp" sum_to 10
    else
        echo "skip: wasm-tools not on PATH; .wasm round-trip not exercised"
    fi

    exit $fail

# Run the runner executable against samples/.
[group("runner")]
[working-directory("interpreter")]
runner-run +args:
    lake exe runner {{ args }}

# ── testsuite ─────────────────────────────────────────────────────────────────

# Run the WebAssembly spec testsuite (vendor/testsuite/). Optional pattern
# is a case-sensitive substring on the .wast filename stem.
[group("testsuite")]
testsuite pattern="":
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ -n "{{pattern}}" ]]; then
        lake -d "{{justfile_directory()}}/interpreter" exe testsuite "{{pattern}}"
    else
        lake -d "{{justfile_directory()}}/interpreter" exe testsuite
    fi

# Regenerate testsuite_report.txt at the repo root. CI runs the same command
# and fails if the working tree drifts, so contributors whose changes shift
# coverage must commit the updated report.
[group("testsuite")]
testsuite-report:
    #!/usr/bin/env bash
    set -euo pipefail
    if ! command -v wasm-tools >/dev/null 2>&1; then
        echo "error: wasm-tools not on PATH (need exactly {{WASM_TOOLS_VERSION}})" >&2
        exit 1
    fi
    got=$(wasm-tools --version | awk 'NR==1 {print $2}')
    if [[ "$got" != "{{WASM_TOOLS_VERSION}}" ]]; then
        echo "error: wasm-tools {{WASM_TOOLS_VERSION}} required, found $got" >&2
        echo "       the committed testsuite_report.txt is pinned to that version" >&2
        exit 1
    fi
    lake -d "{{justfile_directory()}}/interpreter" exe testsuite --report \
        > "{{justfile_directory()}}/testsuite_report.txt"

# ── verifier workflow ─────────────────────────────────────────────────────────
# All verifier recipes run from programs/ (project root: rust/ + lean/).

[private]
[working-directory("programs")]
_verifier +args:
    VERIFIER_TEMPLATE={{ROOT}}/verifier/template lake -d ../verifier exe verifier {{ args }}

# Full pipeline: build wasm → emit Program.lean → lake build.
verifier-check:
    @just _verifier check

# Same as check but re-emit every Program.lean.
verifier-check-force:
    @just _verifier check --force-emit

# CI freshness: regenerate Program.lean without lake build.
verifier-check-no-prove:
    @just _verifier check --no-prove

# Scaffold a new verifier project at <path> (relative to programs/ cwd).
verifier-init path:
    just build-verifier
    just _verifier init {{ path }}

# Add one crate to the current project (snake_case, e.g. my_crate).
verifier-add crate:
    @just _verifier add {{ crate }}

# Build wasm/wat only (optional crate names).
verifier-build +crates:
    @just _verifier build {{ crates }}

# Transpile program.wat → Program.lean (optional crate names).
verifier-emit +crates:
    @just _verifier emit {{ crates }}

# Re-emit all crates unconditionally.
verifier-emit-force:
    @just _verifier emit --force-emit

# lake build in lean/ only.
verifier-prove +crates:
    @just _verifier prove {{ crates }}

# Extract JSON metadata per crate.
verifier-extract +crates:
    @just _verifier extract {{ crates }}

# HTML progress report (needs npm in verifier/report).
verifier-report:
    @just _verifier report

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
