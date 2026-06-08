#!/usr/bin/env bash
# Remove Lake build artefacts from all Lean packages and Cargo target dir.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
for pkg in interpreter codelib programs/lean verifier docbuild; do
    dir="$ROOT/$pkg"
    [[ -d "$dir/.lake" ]] && rm -rf "$dir/.lake" && echo "cleaned $pkg/.lake"
done
cargo clean --manifest-path "$ROOT/programs/rust/Cargo.toml"
echo "cleaned programs/rust/target"
