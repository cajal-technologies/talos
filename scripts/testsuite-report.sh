#!/usr/bin/env bash
# Regenerate testsuite_report.txt at the repo root.
#
# Requires the WASM_TOOLS_VERSION env var (passed by the justfile) and a
# wasm-tools binary on PATH whose version matches exactly — the committed
# report is pinned to that version because different wasm-tools releases
# can produce different .wast decodes.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
required_version="${WASM_TOOLS_VERSION:?WASM_TOOLS_VERSION must be set}"

if ! command -v wasm-tools >/dev/null 2>&1; then
    echo "error: wasm-tools not on PATH (need exactly $required_version)" >&2
    exit 1
fi
got=$(wasm-tools --version | awk 'NR==1 {print $2}')
if [[ "$got" != "$required_version" ]]; then
    echo "error: wasm-tools $required_version required, found $got" >&2
    echo "       the committed testsuite_report.txt is pinned to that version" >&2
    exit 1
fi
lake -d "$ROOT/interpreter" exe testsuite --report \
    > "$ROOT/testsuite_report.txt"
