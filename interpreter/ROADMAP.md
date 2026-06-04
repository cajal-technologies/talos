# Interpreter roadmap

A running, opinionated list of Wasm features the interpreter does not yet support, roughly ranked by how often they show up when verifying real Rust-compiled Wasm. This is a guide for contributors looking for impactful work, not a commitment. Items near the top unlock the most real-world programs; items near the bottom are specialized and can wait.

If you want to pick something up, open an issue first so we can compare notes on the design — especially for the higher-impact items, where the data-model choices ripple through the rest of the interpreter and the WP layer.

## Already supported

These were once on this roadmap and have since landed; listed here so the list above stays honest about what's done:

- **Host functions / imports.** `Module.imports`, a `HostEnv α` threaded through `exec`/`run`, `call` dispatch into host imports, and the `HostContract`/`HostSpec` contract layer. The store is polymorphic over host state (`Store α`).
- **Tables and `call_indirect`** (with `funcref` and element segments).
- **Multi-value results.** `Function` and the public `run` API carry `List ValueType` results, not just i32.
- **Start function.** `(start $f)` runs at instantiation; a trap there fails instantiation.

## Tier 1 — common in real codegen

### Floats (f32 / f64)

Large surface area: NaN propagation, rounding modes, canonicalization. The WAT decoder currently maps float types to an `i32` placeholder (`Decoder/Wat.lean`), so float programs decode but are not modeled faithfully — a real implementation needs the actual value domain and operations. Rarely worth the cost for verification work unless a target program needs them, but it is the largest remaining gap for "real" Rust output.

## Tier 2 — nice to have, lower priority

- Mutable global imports (memory/global/table imports are currently dropped by the decoder; only function imports are wired up).
- Multiple memories.
- Reference types beyond `funcref` (`externref`).
- SIMD (`v128`).
- Exception handling.
- GC proposal.
- Host reentrancy — a host function calling back into `run`. Out of scope today; real reentrant hosts (blockchain trampolines, JS) would need a dedicated milestone.

## Meta-gap: module linking

There is currently no story for one verified module calling another. If the project heads toward verifying a *system* rather than a single program, the linking model shapes the host-function design and is worth settling before more host machinery gets built out. Worth a design discussion before code.
