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
- `@[proves FloatRoundSpec]` on `check_round_correct := check_round_terminatesWith`.
- 7 legacy `func*_term` theorems and helpers deleted.

### FloatReinterpret

- `FloatReinterpretSpec` redefined to conjunction of two `SmallStep.TerminatesWith`
  (checkAbs + checkCopysign).
- `@[proves FloatReinterpretSpec]` on
  `check_reinterpret_correct := ⟨check_abs_terminatesWith, check_copysign_terminatesWith⟩`.
- 12 legacy `func*_term` theorems and helpers deleted.

### SwapElements

- New `SmallStep.TerminatesWith` specs added in `SmallStepSpec.lean`:
  `SwapElementsDistinctTerminatesSpec` and `SwapElementsAliasTerminatesSpec`.
- Registered under `@[spec_of "rust-exported-small-step-total"]`.
- Legacy `SwapElementsSpec` under `@[spec_of "rust-exported"]` retained
  (see Deferred).
- TWP proofs in `SwapSepLogic.lean` for all 5 functions (both distinct and alias).

### SwapElementsOpt3

- `SwapElementsOpt3Spec` defined as `SmallStep.TerminatesWith`, registered
  under `@[spec_of "rust-exported"]`.
- Delegates to existing `opt3_func0_distinct_store_terminatesWith` from
  `SmallStepEquivalence.lean`.
- Equivalence proof ported to `SmallStep.ObservationallyEquivOn.of_common_outcome`.

### NumInteger

- `GcdU64Spec` redefined to `SmallStep.TerminatesWith (func2Config a b)`.
- `@[proves GcdU64Spec]` on `gcd_u64_correct := func2_terminatesWith`.
- TWP loop via `Nat.strongRecOn` on `x.toNat + y.toNat`.
- Legacy `meatLoop_wp`, `func1_terminates`, `func0_terminates`,
  `LegacyGcdU64Spec`, `gcd_u64_legacy_correct` all deleted.
- Equivalence proof ported to `SmallStep.ObservationallyEquivOn.of_common_outcome`.

## Already on small-step (no migration needed)

NumIntegerOpt3, RustU64, RustU64Tests, RustArray, RustArrayTests, TotalVariation.

## Deferred

| Item | Reason |
|---|---|
| `SwapElements/Spec.lean` legacy | `swap_spec_sep` in `SwapSepLogic.lean` has `SwapElementsSpec` as its theorem TYPE — can't remove the Prop without changing the signature. M9 cleanup. |
| FloatMinmax | Stub (`True`), spec never written. |
| Near layer (2,996 lines) | Blocked on `wp_callHost` (module-linking). |
| SwapElementsOpt3 whole-array observation | The small-step `SwapOptEquiv` observes only the two swapped elements; the retired big-step theorem observed the whole caller array (`Mem.words64 ptr len.toNat`). Restoring it needs both builds' store-level adequacy theorems re-derived with a parametric per-element `pointsTo_u64` footprint for the unswapped words plus a `Mem.words64` reconstruction. Documented in `SwapElementsOpt3/Equivalence.lean`. |
| Program-specific TWP lemmas in codelib | `twp_swapElementsFunc2Prefix` / `…Alias` / `…Func3` (hard-coded addresses) live in `codelib/CodeLib/SepLogic/SmallStepTotalLifting.lean` rather than under `programs/`; pre-existing precedent (the WP counterparts live there too). Candidate M9 relocation. |

## TWP infrastructure added

- `wasm_smallStep_heap_globals_runtime_store_terminates` in `SmallStepAdequacy.lean` —
  TWP adequacy bridge for programs with heap + globals.
- 31 TWP lifting rules in `SmallStepTotalLifting.lean`
  (22 single-instruction, 5 SwapElements compound, 4 i64 state rules).
- `MergeSort/Adequacy.lean` — merge sort adequacy closure (M7 item 8). The
  `PartiallyMeets` / `TerminatesWith` posts are memory-observing: the terminal
  store's `source` array (`readWordArray store.wasm.mem source input.length`)
  is a sorted permutation of the input.