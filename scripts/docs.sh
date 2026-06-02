#!/usr/bin/env bash
# Generate HTML documentation and serve it at http://localhost:8080.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/docbuild"
lake build Project:docs
echo "Serving docs at http://localhost:8080 (Ctrl-C to stop)"
python3 -m http.server 8080 --directory .lake/build/doc
