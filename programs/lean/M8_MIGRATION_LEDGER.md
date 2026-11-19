# M8 Migration Ledger

Tracks migration of legacy `TerminatesWith env` theorems to
`SmallStep.TerminatesWith` via TWP.

## Summary

- All three packages build clean under `--wfail`. Zero `sorry`.
- 6 programs migrated to `SmallStep.TerminatesWith`.
- Both equivalence proofs ported to `SmallStep.ObservationallyEquivOn`.
- `SwapElements/Spec.lean` retains legacy theorems (see Deferred).
- `import Interpreter.Wasm.Wp` remains only in `SwapElements/Spec.lean`.

## Completed

### FloatTrunc

- `FloatTruncSpec` redefined to `SmallStep.TerminatesWith (checkConfig x)`.
- `@[proves FloatTruncSpec]` on `check_correct := check_terminatesWith`.
- Legacy `func1_terminates`, `func0_terminates` and helpers deleted.

### FloatRound

- `FloatRoundSpec` redefined to `SmallStep.TerminatesWith (checkRoundConfig x)`.
- It is retained as an unregistered termination milestone: its postcondition
  says only that some `i32` is returned, not whether the two rounding
  implementations agree.
- 7 legacy `func*_term` theorems and helpers deleted.

### FloatReinterpret

- `FloatReinterpretSpec` redefined to conjunction of two `SmallStep.TerminatesWith`
  (checkAbs + checkCopysign).
- It is retained as an unregistered termination milestone: the two public
  properties still need explicit status/reference postconditions and separate
  export specifications.
- 12 legacy `func*_term` theorems and helpers deleted.

### SwapElements

- New `SmallStep.TerminatesWith` specs added in `SmallStepSpec.lean`:
  `SwapElementsDistinctTerminatesSpec` and `SwapElementsAliasTerminatesSpec`.
- These are now unregistered proof milestones: the supported partial/total
  distinction applies to a public export contract, not to four implementation
  variants, and `swap_elements_alias` is not an export.
- The single public `SwapElementsSpec` under `@[spec_of "rust-exported"]`
  remains the export contract.
- TWP proofs in `SwapSepLogic.lean` for all 5 functions (both distinct and alias).

### SwapElementsOpt3

- `SwapElementsOpt3Spec` defined as `SmallStep.TerminatesWith`, registered
  under `@[spec_of "rust-exported"]`.
- Delegates to existing `opt3_func0_distinct_store_terminatesWith` from
  `SmallStepEquivalence.lean`.
- Equivalence proof ported to `SmallStep.ObservationallyEquivOn.of_common_outcome`.

### NumInteger

- `GcdU64Spec` now exposes semantic `Input`/`Output`, `args`/`result`, and
  `Runs "gcd_u64"`; `func2_terminatesWith` remains its machine-level proof.
- TWP loop via `Nat.strongRecOn` on `x.toNat + y.toNat`.
- Legacy `meatLoop_wp`, `func1_terminates`, `func0_terminates`,
  `LegacyGcdU64Spec`, `gcd_u64_legacy_correct` all deleted.
- Equivalence proof ported to `SmallStep.ObservationallyEquivOn.of_common_outcome`.

## Already on small-step (no migration needed)

NumIntegerOpt3, RustU64, RustU64Tests, RustArray, RustArrayTests, TotalVariation.

## Deferred

| Item | Reason |
|---|---|
| `SwapElements/Spec.lean` legacy | The public `SwapElementsSpec` is still stated with the big-step `TerminatesWith env` and proved there by `swap_elements_correct` through the `Wp` layer; moving it to `SmallStep.TerminatesWith` changes the registered statement. M9 cleanup. |
| FloatMinmax | Stub (`True`), spec never written. |
| Near layer (2,996 lines) | Blocked on `wp_callHost` (module-linking). |
| SwapElementsOpt3 whole-array observation | The small-step `SwapOptEquiv` observes only the two swapped elements; the retired big-step theorem observed the whole caller array (`Mem.words64 ptr len.toNat`). Restoring it needs both builds' store-level adequacy theorems re-derived with a parametric per-element `pointsTo_u64` footprint for the unswapped words plus a `Mem.words64` reconstruction. Documented in `SwapElementsOpt3/Equivalence.lean`. |

## TWP infrastructure added

- `wasm_smallStep_heap_globals_runtime_store_terminates` in `SmallStepAdequacy.lean` —
  TWP adequacy bridge for programs with heap + globals.
- TWP lifting rules in `SmallStepTotalLifting.lean`; the SwapElements
  compound rules (`twp_swapElementsFunc2Prefix` and its siblings) live in
  `Project/SwapElements/SwapSepLogic.lean`.
- `CodeLib/Examples/MergeSort/Adequacy.lean` — merge sort adequacy closure (M7 item 8). The
  `PartiallyMeets` / `TerminatesWith` posts are memory-observing: the terminal
  store's `source` array (`readWordArray store.wasm.mem source input.length`)
  is a sorted permutation of the input.
