# Deliberate differences from the mergesort example

Both examples share the same host, imports, memory model, and CodeLib program
logic. The three differences below are intrinsic to the program being verified,
not stylistic choices.

## 1. Total public specification (not partial)

Mergesort's public theorem is `PartiallyRunsWithOutcome`
(`@[spec_of "rust-exported-partial" ...]`): it classifies every finite terminal
trace but explicitly does not claim one exists. hex proves the **total**
OOM-disjunction (`@[spec_of "rust-exported" ...]`) — a terminal outcome is
always reached.

This costs nothing extra structurally: mergesort's per-function contracts are
already total weakest-preconditions (`WP … [{ Φ }]`); its adequacy step merely
weakens them to a partial `wp` via `twp.to_wp`. The hex proofs instead carry the
totality through to the public statement, using CodeLib's
`SmallStepOutcomeAdequacy` total layer (`stronglyNormalizing_adequate_outcome`,
`TerminatesWithOutcome.to_success_or_trap`) — the same machinery, not weakened.

## 2. Real growing allocator

Mergesort uses a simplified bump allocator. hex allocates an output vector whose
size depends on the input (encode: two output bytes per input byte; decode: one
output byte per two input characters, after validation), so it exercises genuine
`memory.grow`: on success the proof takes ownership of the newly-exposed
physical byte range and commits it into the sparse heap. The live allocation
path is `twp_memoryGrow_fresh`; the failure path calls `talos.oom` and discharges
the exceptional branch of the target.

Consequence for the sparse-heap frontier: committing a freshly-grown range
requires the `heapDomainInterp` frontier to dominate the new addresses. The hex
allocator keeps the maximal frontier (`UInt32.size`), under which
`heapBelow_uint32Size` discharges the obligation for any address.

## 3. Decode input validation

`decode` has an additional exhaustive terminal branch inside its success leg: an
odd input length or a non-hex character is not a trap but a defined result — a
status byte (`1` odd length, `2` non-hex character) with no decoded output — so
the reference function `Spec.decodeOutput` is total on all inputs and the
disjunction remains exhaustive.

## Reusable machinery added to CodeLib

The general total weakest-precondition instruction lemmas both examples need but
CodeLib did not yet provide are factored into
`CodeLib/SepLogic/SmallStepTotalLiftingAux.lean` — byte-granular load/store rules
and lighter-weight, resource-minimal variants of a few `SmallStepTotalLifting`
rules — so the encode and decode proofs share one copy rather than each carrying
its own. Both example libraries import only `CodeLib` (no `Mathlib`), matching
the mergesort example's dependency footprint.
