# hex_stdio Wasm analysis

This directory is the review boundary for the `hex_stdio` proofs: **total**
correctness of the two exported entry points, `encode` and `decode`, of a Rust
program that wraps the `hex` crate over standard I/O, compiled with Talos's
OOM-signalling allocator.

The two exports share one generated Wasm module (`Project/HexStdio/Program.lean`)
and are proved as two self-contained worked-example libraries:

- `HexEncodeStdio` — top theorem `hex_encode_stdio_correct :
  Project.HexStdio.Spec.EncodeSpec` (`HexEncodeStdio/Proof.lean`).
- `HexDecodeStdio` — top theorem `hex_decode_stdio_correct :
  Project.HexStdio.Spec.DecodeSpec` (`HexDecodeStdio/Proof.lean`).

## What is proved

For every input, each export reaches **exactly one** of two finite terminal
outcomes — a terminal outcome is always reached (this is a totality claim):

```
∀ input, RunsBytes «module» "encode" input (Spec.encode input)      ∨ RunsOutOfMemory input
∀ input, RunsBytes «module» "decode" input (Spec.decodeOutput input) ∨ RunsOutOfMemory input
```

Either the export computes the Lean reference function over its byte stream, or
its private allocator reaches the distinguished `talos.oom` host trap with the
typed OOM marker raised (`final.oom.raised = true`). Divergence and unrelated
traps satisfy neither branch. Fuel, linear-memory addresses, the allocator, and
compiler stack frames are hidden from the public statement.

The reference implementations live in `Spec.lean` (encode: `hexDigit` /
`encodeByte` / `encode` — two lowercase ASCII hex characters per byte) and
`DecodeSpec.lean` (decode: `decode` / `decodeOutput` — pairs hex characters back
to bytes, with a status byte for odd length or a non-hex character).

## Relation to the mergesort example (#200)

The proofs are stated against the same shared foundation as mergesort — the
`Universal` host; imports `stdio.read` / `stdio.write` / `talos.oom`; CodeLib's
`WasmHeap` / `stateInterp` / `pointsToBytes` byte-list memory model and total
weakest-precondition program logic — and reuse CodeLib's total-adequacy layer
(`SmallStepOutcomeAdequacy`) directly.

Three deliberate differences (see `differences.md`):

1. **Total public spec**, not partial. Mergesort proves
   `PartiallyRunsWithOutcome` (`@[spec_of "rust-exported-partial" ...]`) and
   explicitly does not claim a terminal outcome exists. hex proves the total
   OOM-disjunction — a terminal outcome is reached — via the same CodeLib
   total layer that mergesort's per-function twp proofs already satisfy.
2. **Real growing allocator.** hex sizes an output vector to the input (encode:
   two bytes out per byte in; decode: one byte out per two in, after
   validation), exercising genuine `memory.grow` with ownership of the
   newly-exposed physical range — vs mergesort's simplified bump allocator.
3. **Decode validation.** Odd input length or a non-hex character is an
   additional exhaustive terminal branch (status byte) inside the success leg.

## Contents

- [Frozen target](target.md) — artifacts, hashes, public meaning, change policy.
- [Differences from mergesort](differences.md) — the three points above, in full.
