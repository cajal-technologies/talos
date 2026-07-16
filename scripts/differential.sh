#!/usr/bin/env bash
# Differential-test the runner against a trusted oracle (V8) using miscast.
#
# miscast (@jasisz) generates or replays WebAssembly modules — GC included — runs
# each on the runner and on V8, and reports a SOUNDNESS divergence when the runner
# accepts or runs something V8 rejects or traps on. See cajal-technologies/talos#108.
#
# The runner speaks miscast's verdict contract directly, with no adapter: a value
# on stdout reads as a result, a `trap:` line reads as a trap (including an
# uncaught exception), float args take the same WAT literal grammar V8 sees, and
# out-of-fuel (exit 2, empty stdout) reads as unsupported — never a false
# divergence. (miscast also ships tools/talos_run.py, an adapter predating this
# alignment; driving the runner directly keeps the contract in one place.)
#
# The contract is enforced, not assumed: every run starts with canaries that
# probe the runner's actual output against miscast's own classification regexes
# (see "contract canaries" below), and lints the seed corpus for the export-"f"
# convention its loader requires.
#
# Usage:
#   just differential                                  # recgroup soundness mode, V8 oracle
#   just differential --mode recgroup -n 300           # reproduce the full #108 cluster
#   just differential --mode mutate --seeds differential/seeds
#
# Env:
#   MISCAST_DIR=/path/to/miscast   use an existing checkout instead of the pinned clone
#   NODE=/path/to/node             override oracle node discovery (still gated to >= 22)
#   SKIP_BUILD=1                   skip `lake build runner` (assume it is already built)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# miscast is pinned as an external dependency (not vendored) so it can evolve upstream.
MISCAST_REPO="https://github.com/jasisz/miscast"
MISCAST_REV="125d25b69b20462fe03505b30eb281851f0be3a8"
CACHE="$ROOT/.differential-cache"

# ── dependencies ──────────────────────────────────────────────────────────────
for tool in python3 wasm-tools git; do
    command -v "$tool" >/dev/null 2>&1 || { echo "differential: '$tool' not on PATH" >&2; exit 127; }
done
# Fail fast (before any clone) when node is nowhere to be found. The
# authoritative version gate runs below, via miscast's own discovery.
command -v node >/dev/null 2>&1 || [[ -n "${NODE:-}" ]] || [[ -d "$HOME/.nvm/versions/node" ]] \
    || { echo "differential: node not found (PATH, ~/.nvm, or NODE=) — required for the V8 oracle" >&2; exit 1; }

# ── seed-corpus lint ──────────────────────────────────────────────────────────
# miscast's corpus loader drives a bare .wat through the export named "f"; a
# seed exporting anything else is silently skipped by the seed-driven modes.
bad="$(grep -L -F '(export "f"' "$ROOT"/differential/seeds/*.wat 2>/dev/null || true)"
if [[ -n "$bad" ]]; then
    echo "differential: seeds must export their entry point as \"f\" (miscast's corpus convention):" >&2
    echo "$bad" >&2
    exit 1
fi

# ── miscast (pinned) ──────────────────────────────────────────────────────────
if [[ -n "${MISCAST_DIR:-}" ]]; then
    miscast="$(cd "$MISCAST_DIR" && pwd)"
else
    miscast="$CACHE/miscast"
    if [[ ! -d "$miscast/.git" ]]; then
        echo "differential: fetching miscast @ ${MISCAST_REV:0:12} …"
        mkdir -p "$CACHE"
        git clone -q "$MISCAST_REPO" "$miscast"
    fi
    git -C "$miscast" checkout -q "$MISCAST_REV" 2>/dev/null \
        || { git -C "$miscast" fetch -q origin && git -C "$miscast" checkout -q "$MISCAST_REV"; }
fi

# ── node (the V8/WasmGC oracle, >= 22) ────────────────────────────────────────
# Ask miscast's own discovery (PATH or ~/.nvm, `NODE` env override) rather than
# re-implementing it: the gate then tests exactly the binary the oracle will use.
NODE_BIN="$(cd "$miscast" && python3 -c 'from miscast.config import NODE; print(NODE or "")')"
[[ -n "$NODE_BIN" ]] || { echo "differential: no node >= 22 found (PATH or ~/.nvm) — required for the V8 oracle" >&2; exit 1; }
# find_node only returns >= 22, but a `NODE=` override reaches here unchecked —
# gate it too, and catch a path that isn't runnable at all.
node_major="$("$NODE_BIN" -p 'process.versions.node.split(".")[0]' 2>/dev/null)" \
    || { echo "differential: cannot run node at $NODE_BIN" >&2; exit 1; }
if (( node_major < 22 )); then
    echo "differential: node >= 22 required for the V8 oracle ($NODE_BIN is $("$NODE_BIN" --version))" >&2
    exit 1
fi
export NODE="$NODE_BIN"   # pin the run to the binary we just gated on

# ── build the runner (the system under test) ──────────────────────────────────
if [[ -z "${SKIP_BUILD:-}" ]]; then
    ( cd "$ROOT/interpreter" && lake build runner )
fi
RUNNER="$ROOT/interpreter/.lake/build/bin/runner"
[[ -x "$RUNNER" ]] || { echo "differential: runner not built at $RUNNER" >&2; exit 1; }

# The runner reads .wat directly and takes `<file> <method> [args]`, exactly
# miscast's {wat} {export} plus positional invoke args — so it plugs in unwrapped.
# miscast shlex-splits this template, so the quotes keep a runner path that
# contains spaces as one argv word.
export CUSTOM_CMD="\"$RUNNER\" {wat} {export}"

# Resolve `--seeds PATH` / `--seeds=PATH` (relative to ROOT) to an absolute
# existing directory, since miscast runs from its own directory below. An empty
# or missing path must fail loudly here — passed through, miscast would glob an
# empty corpus and report a green files=0 run.
args=()
while (( $# )); do
    case "$1" in
        --seeds|--seeds=*)
            if [[ "$1" == --seeds ]]; then p="${2:-}"; n=2; else p="${1#--seeds=}"; n=1; fi
            [[ -n "$p" ]] || { echo "differential: --seeds needs a path" >&2; exit 2; }
            [[ "$p" == /* ]] || p="$ROOT/$p"
            [[ -d "$p" ]] || { echo "differential: seeds directory not found: $p" >&2; exit 2; }
            args+=("--seeds" "$p"); shift "$n"; continue ;;
    esac
    args+=("$1"); shift
done
# Default: the recgroup soundness mode that pins #108.
(( ${#args[@]} )) || args=(--mode recgroup -n 50)

cd "$miscast"

# ── contract canaries ─────────────────────────────────────────────────────────
# The no-adapter design couples the runner's output vocabulary to miscast's
# classification regexes. That coupling is easy to break silently (a reworded
# error message, a dropped `trap:` prefix), so probe it with the real regexes
# before every run:
#   (a) a CLI arg-count complaint must NOT read as validator rejection or trap
#       (else the validation differential records false REJECT agreement);
#   (b) an uncaught exception must read as a trap (matching V8);
#   (c) a garbage float arg must fail the run (empty stdout, no trap) — never
#       parse as 0.0 and fake a comparable result.
canary_dir="$(mktemp -d "${TMPDIR:-/tmp}/differential-canary.XXXXXX")"
trap 'rm -rf "$canary_dir"' EXIT
printf '(module (func (export "f") (param i32 i32) (result i32) local.get 0))' > "$canary_dir/args.wat"
printf '(module (tag $t) (func (export "f") (throw $t)))'                      > "$canary_dir/exn.wat"
printf '(module (func (export "f") (param f64) (result f64) local.get 0))'     > "$canary_dir/flt.wat"
python3 - "$RUNNER" "$canary_dir" <<'EOF'
import subprocess, sys
from miscast.engines import _VALERR, _TRAP, _CRASH, _NUM

runner, d = sys.argv[1], sys.argv[2]

def run(*argv):
    r = subprocess.run([runner, *argv], capture_output=True, text=True)
    return r, r.stdout + r.stderr

r, both = run(f"{d}/args.wat", "f")                       # (a) arg-count wording
if _VALERR.search(both) or _TRAP.search(both) or _CRASH.search(both):
    sys.exit(f"differential: canary: arg-count wording matches miscast rejection/trap vocabulary: {both.strip()!r}")

r, both = run(f"{d}/exn.wat", "f")                        # (b) uncaught exception
if not _TRAP.search(both):
    sys.exit(f"differential: canary: uncaught exception does not read as a trap: {both.strip()!r}")

r, both = run(f"{d}/flt.wat", "f", "not-a-float")         # (c) garbage float arg
if r.returncode == 0 or _NUM.match(r.stdout.strip()) or _TRAP.search(both):
    sys.exit(f"differential: canary: garbage float arg did not fail cleanly: {both.strip()!r}")
EOF

echo "differential: runner   = $RUNNER"
echo "differential: miscast  = $(git rev-parse --short HEAD)   oracle = v8 (node $("$NODE_BIN" --version))"
python3 -B -m miscast --sut custom --oracles v8 "${args[@]}"
echo "differential: reproducers under $miscast/work/repro/"
