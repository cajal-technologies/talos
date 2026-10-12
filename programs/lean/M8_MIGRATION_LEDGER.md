# M8 Migration Ledger

Tracks migration of legacy `TerminatesWith env` theorems to
`SmallStep.TerminatesWith` via TWP.

## Summary

- All three packages build clean under `--wfail`. Zero `sorry`.
- 6 programs migrated to `SmallStep.TerminatesWith`.
- Both equivalence proofs ported to `SmallStep.ObservationallyEquivOn`.
- `SwapElements/Spec.lean` fully migrated to small-step.
- `import Interpreter.Wasm.Wp` is no longer present in any `programs/lean/` file.

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
- TWP proofs in `SwapSepLogic.lean` for all 5 functions (both distinct and alias).
- `func4_store_terminatesWith_array`: whole-array TWP adequacy theorem;
  observes `Mem.readWords64` over the full slice (the `∀k` clause).
- `func4_initialStore_terminatesWith_array`: public bridge; takes the module's
  initial store with array pre-written at `ptr`, no Iris witnesses required from
  caller.
- `Spec.lean` fully migrated to `Input`/`Output`/`args`/`result`/`Runs`/
  `SwapElementsSpec`/`swap_elements_correct` following NumIntegerOpt3 pattern;
  all legacy `TerminatesWith env «module»` theorems (`func2_swap` … `func4_swap`)
  and the old WP imports removed.

### SwapElementsOpt3

- `SwapElementsOpt3Spec` defined as `SmallStep.TerminatesWith`, registered
  under `@[spec_of "rust-exported"]`.
- Whole-array observation restored: `SwapElementsOpt3Spec` is restated over `Runs` and `SwapOptEquiv` observes `Mem.words64` over the caller's slice, via `opt3_func0_store_terminatesWith_array` and `opt3_initialStore_terminatesWith_array` (`SmallStepEquivalence.lean`); the distinct-cell `opt3_func0_distinct_store_terminatesWith` is kept.
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
| ~~`SwapElements/Spec.lean` legacy~~ | Resolved in M8: Spec.lean fully migrated to small-step. |
| FloatMinmax | Stub (`True`), spec never written. |
| Near layer (2,996 lines) | Blocked on `wp_callHost` (module-linking). |
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
