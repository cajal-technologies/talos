#!/usr/bin/env bash
# Smoke-test the runner executable against samples/.
# Builds the runner, runs a handful of sample programs, and verifies
# both the exit code and the chosen output stream against expectations.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/interpreter"
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
