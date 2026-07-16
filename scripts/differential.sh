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
# Usage:
#   just differential                                  # recgroup soundness mode, V8 oracle
#   just differential --mode recgroup -n 300           # reproduce the full #108 cluster
#   just differential --mode mutate --seeds differential/seeds
#
# Env:
#   MISCAST_DIR=/path/to/miscast   use an existing checkout instead of the pinned clone
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
if [[ -z "$NODE_BIN" ]]; then
    echo "differential: no node >= 22 found (PATH or ~/.nvm) — required for the V8 oracle" >&2
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

# Resolve a relative `--seeds PATH` / `--seeds=PATH` (relative to ROOT) to
# absolute, since miscast runs from its own directory below.
args=()
while (( $# )); do
    case "$1" in
        --seeds)
            if [[ -n "${2:-}" && "$2" != /* ]]; then
                args+=("--seeds" "$ROOT/$2"); shift 2; continue
            fi ;;
        --seeds=*)
            v="${1#--seeds=}"
            if [[ -n "$v" && "$v" != /* ]]; then
                args+=("--seeds=$ROOT/$v"); shift; continue
            fi ;;
    esac
    args+=("$1"); shift
done
# Default: the recgroup soundness mode that pins #108.
(( ${#args[@]} )) || args=(--mode recgroup -n 50)

cd "$miscast"
echo "differential: runner   = $RUNNER"
echo "differential: miscast  = $(git rev-parse --short HEAD)   oracle = v8 (node $("$NODE_BIN" --version))"
python3 -B -m miscast --sut custom --oracles v8 "${args[@]}"
echo "differential: reproducers under $miscast/work/repro/"
