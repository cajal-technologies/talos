# Interpreter roadmap

A running, opinionated list of Wasm features the interpreter does not yet support, roughly ranked by how often they show up when verifying real Rust-compiled Wasm. This is a guide for contributors looking for impactful work, not a commitment. Items near the top unlock the most real-world programs; items near the bottom are specialized and can wait.

If you want to pick something up, open an issue first so we can compare notes on the design — especially for tier 1 items, where the data-model choices ripple through the rest of the interpreter and the WP layer.

## Tier 1 — common, blocking real programs

### Host functions / imports

Today `Module` has no `imports` field and `call` only dispatches to in-module functions. Without imports, no program that does I/O, allocates via a host allocator, or interacts with a runtime is verifiable — which rules out most "real" Wasm.

Sketch of what's needed:

- An import descriptor in `Module` (name, signature).
- A host-function environment threaded through `Config`.
- A `call_host` step rule that consults the environment.
- A spec-level story for "the host does X" — probably an uninterpreted relation the user supplies per program, so that proofs can reason about host effects abstractly.

### Tables and `call_indirect`

Rust emits `call_indirect` for trait objects, function pointers, and some closure shapes. Without it, anything using `dyn Trait` is off-limits. Implementation involves `funcref`, element segments for table initialization, and the runtime type-check (with trap on mismatch or out-of-bounds).

### Small but pervasive ops: `memory.grow`, `memory.size`, `unreachable`, `select`

All trivially small additions to `Instruction` and the step function, but constantly emitted by rustc. `unreachable` in particular is what panics lower to — without it you can't even state "this path panics", let alone prove a function is panic-free.

## Tier 2 — common in real codegen

### Bulk memory: `memory.copy`, `memory.fill`, `memory.init`, `data.drop`

LLVM emits these for `memcpy`/`memset`, struct moves, and `Vec` operations. Without them, rustc-compiled code only works with bulk-memory disabled, which is a persistent footgun.

### Multi-value results

`paramArity` / `resultArity` already exist on the block-like instructions, so the interpreter is mostly ready. The gap is in `Function` and the public `run` API, which are i32-shaped. Multi-value lets functions return tuples and is required for some Rust ABIs.

### Floats (f32 / f64)

Large surface area: NaN propagation, rounding modes, canonicalization. Rarely worth the implementation cost for verification work unless a target program needs them. Punt until forced.

## Tier 3 — nice to have, low priority

- Mutable global imports (rounds out the host-functions design).
- Start function.
- Multiple memories.
- Reference types beyond `funcref` (`externref`).
- SIMD (`v128`).
- Exception handling.
- GC proposal.

## Meta-gap: module linking

There is currently no story for one verified module calling another. If the project heads toward verifying a *system* rather than a single program, the linking model shapes the host-function design above and is worth settling before tier 1 (1) gets built out. Worth a design discussion before code.
