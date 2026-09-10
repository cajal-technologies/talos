# Frozen verification target

## Source and toolchain

- The original proof target was based on `73d08a4` (merge of #197), branch
  `hex-examples`. Its Rust source and build artifacts were not committed.
- The current source is reconstructed in `programs/rust/hex_stdio`, using
  `hex` **0.4.3** and the shared `talos-stdio` crate. Both crates and the
  wrapper use optimization level 3; the workspace pins the remaining release
  settings. Build with `verifier build hex_stdio` from `programs/` and regenerate
  the Lean module with `verifier emit hex_stdio`.
- Program: a Rust crate wrapping the `hex` crate, exporting `encode` and
  `decode` over standard I/O, linked with the `talos-stdio` OOM-signalling
  allocator (the allocator calls the `talos.oom` host on allocation failure
  instead of trapping, giving an explicit terminal outcome).
- Rust toolchain: `1.95.0`, profile minimal, target `wasm32-unknown-unknown`
  (`programs/rust/rust-toolchain.toml`).

## Exact artifacts

| Artifact | SHA-256 |
| --- | --- |
| Verifier input `programs/rust/build/hex_stdio/program.wasm` | `1394c9d6cbbd9eabda69b86d01b2961f5f5003891658cbd9116dd4ac4a8a337c` |
| Verifier WAT `programs/rust/build/hex_stdio/program.wat` | `1f01d8fcc79b29254ab2272f70fdb4db2df55aa6ed13bb49b2be726baed93069` |
| Generated `Project/HexStdio/Program.lean` | `a15adc6b2745d9a5e47622aa483ba834d959bc214ddedc39873e1c884da452b7` |

The generated Lean module reads the stripped WAT at elaboration time and has a
compile-time fidelity check against it. Both exports use this one module.

The reconstruction preserves all 99 defined function indices, signatures,
local-variable counts, and type indices. The generated `Program.lean` differs
only by its new WAT fingerprint. The lowercase lookup table remains at address
1048576, the allocator bump pointer at 1053960, and the heap base at 1054000.
The decoder drops the input vector before writing, matching the recorded
execution order. Wrapper stack slots differ and require corresponding
execution-proof changes. Matching `Program.lean` alone does not establish body
equivalence: its function bodies are macros that read the current WAT. The
emitter records the WAT SHA-256 in the generated source so a body-only change
also invalidates Lake's cached build after re-emission.

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

The only permitted axioms are `propext`, `Quot.sound`, and `Classical.choice`.
Bit-vector obligations use kernel-checked normalization or bit extensionality;
native evaluation axioms are not permitted. Run `scripts/axiom-audit.py` for
the entire `programs/lean` package, including both Hex libraries, before accepting
a changed target. A source scan or a successful build of only `Project` does
not establish this requirement.

## Validation of this reconstruction

- Four Rust tests cover all 256 bytes, upper/lowercase round trips, odd-length
  precedence, and all 65,536 character pairs.
- 120 Wasm stream checks cover varying read chunk sizes, empty input, longer
  inputs, both hex cases, and invalid-input statuses. Both exports signal OOM
  when memory is capped at 17 pages.
- The full program audit covers 211 modules, 8,573 declarations, and 5,576
  theorems with zero nonstandard-axiom dependencies.
- Both public correctness theorems retain their total success-or-OOM contracts
  and depend on exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Auxiliary growth rules now carry the logical allocation frontier explicitly,
  matching CodeLib's ownership API. Symbolic scratch checks use operational
  summaries with valid memory assumptions instead of unproved fixed-fuel runs.

## Change policy

Any artifact-hash change invalidates freshness. Before reusing a contract or
proof, re-check function identities, types, body hashes, call sites, constants,
frame layouts, and the terminal-outcome classification.
