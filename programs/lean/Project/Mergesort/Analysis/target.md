# Frozen verification target

## Source and toolchain

- Repository revision at analysis start:
  `4b3eaa97c3127b19f9f2a07475bdde775c27021d`.
- Working branch: `codex/prove-simple-stream-programs`.
- Rust toolchain: `1.95.0 (59807616e 2026-04-14)`, selected by
  `programs/rust/rust-toolchain.toml`.
- Cargo profile: release, `opt-level = 3`, `lto = false`,
  `codegen-units = 1` for both `mergesort` and `talos-stdio`.
- Target: `wasm32-unknown-unknown`.
- Crate: `programs/rust/mergesort`, version `0.1.0`, edition 2024.

## Exact artifacts

| Artifact | SHA-256 |
| --- | --- |
| Stripped verifier input `programs/rust/build/mergesort/program.wasm` | `f0e959667cccfe5aa2526a71c9a234bdac5aace8f4a5471b80a9e7e59e7d3f93` |
| Verifier WAT `programs/rust/build/mergesort/program.wat` | `4c8b133cb580c623b3e75cead86579047dd7e445cb7987c8a50cc573714f73e6` |
| Generated `Project/Mergesort/Program.lean` | `999bebe36b76dfb1e23d0dd8e276d7e01604b66a8fa866684b547b4d3d0e1061` |
| Matching unstripped Cargo Wasm | `68693e946b7dd5cde677fd6dca2f73cbe19a6cfbf6cacd9805c3290e4c96b284` |

The unstripped binary is evidence for source names only.  The generated Lean
module embeds the stripped WAT and has a compile-time fidelity check against
that WAT.  Function order, types, sizes, and instruction bodies were compared
between the stripped and unstripped artifacts before transferring names.

## Public meaning

The export `mergesort` reads a finite byte stream that is the packed
little-endian encoding of a `List UInt32`.  The proved partial-correctness
statement classifies every finite terminal execution as exactly one of two
outcomes:

1. normal return with a packed output that is sorted and a permutation of the
   input; or
2. the distinguished `talos.oom` host trap with the OOM host marker raised.

The current Iris adequacy API does not establish that a terminal execution
exists.  In particular, this is not a termination theorem.

Fuel, linear-memory addresses, the bump allocator, compiler stack frames, and
the scratch array are not part of the public statement.

## Change policy

Any artifact-hash change invalidates freshness.  Before reusing a contract or
proof, re-check function identities, types, body hashes, call sites, constants,
frame layouts, and the public-path terminal classification.
