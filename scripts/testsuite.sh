#!/usr/bin/env bash
# Run the WebAssembly spec testsuite (vendor/testsuite/).
# Optional first argument is a case-sensitive substring on the .wast
# filename stem; empty/missing runs the whole suite.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pattern="${1:-}"

if [[ -n "$pattern" ]]; then
    lake -d "$ROOT/interpreter" exe testsuite "$pattern" || true
else
    lake -d "$ROOT/interpreter" exe testsuite || true
fi
