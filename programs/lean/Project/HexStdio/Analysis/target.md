# Frozen verification target

## Source and toolchain

- talos base revision: `73d08a4` (merge of #197), branch `hex-examples`.
- Program: a Rust crate wrapping the `hex` crate, exporting `encode` and
  `decode` over standard I/O, linked with the `talos-stdio` OOM-signalling
  allocator (the allocator calls the `talos.oom` host on allocation failure
  instead of trapping, giving an explicit terminal outcome).
- Rust toolchain: `1.95.0`, profile minimal, target `wasm32-unknown-unknown`
  (`programs/rust/rust-toolchain.toml`).

## Exact artifacts

| Artifact | SHA-256 |
| --- | --- |
| Verifier input `programs/rust/build/hex_stdio/program.wasm` | `6f84d8084de10ebf9bc2a39a23ff6c541dd0f74f3d733dfba3614fe936ab2eca` |
| Verifier WAT `programs/rust/build/hex_stdio/program.wat` | `28ec861ca915307ddfc1d9793d9328fadc719bfe25cb16b5cc2f4b41e6a4aadb` |
| Generated `Project/HexStdio/Program.lean` | `69314dd1191f67465e3919dea3fcc56a989859ccc29b6a34e80f4bfdeaccbb13` |

The generated Lean module embeds the stripped WAT and has a compile-time
fidelity check against it. Both exports are proved against this one module.

## Public meaning (total)

- `encode` reads a finite byte stream and writes its lowercase hexadecimal
  encoding — two ASCII characters per input byte (`Spec.encode`).
- `decode` reads a finite byte stream of hex characters and writes the bytes it
  spells out, preceded by a status byte: `0` accepted, `1` odd length, `2`
  non-hex character (`Spec.decodeOutput`).

For every input, execution reaches exactly one terminal outcome: it computes the
reference function above, or its private allocator reaches the `talos.oom` host
trap with the OOM marker raised. **This is a totality claim** — unlike the
mergesort example, a terminal outcome is proved to exist; divergence is
excluded. Fuel, linear-memory addresses, the allocator, and compiler stack
frames are not part of the public statement.

## Axioms

The public theorems reduce to `propext`, `Quot.sound`, `Classical.choice`, and
the native `bv_decide` reflection axiom (`_native.bv_decide.ax`), used for a
small number of 32-bit bit-vector obligations. `bv_decide` is an allowed axiom
for these targets (bit-blast to SAT with an LRAT certificate checked by
reflection — the same trust class as `native_decide`, but narrower).

## Change policy

Any artifact-hash change invalidates freshness. Before reusing a contract or
proof, re-check function identities, types, body hashes, call sites, constants,
frame layouts, and the terminal-outcome classification.
