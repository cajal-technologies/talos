# Migrating proofs to fractional page authority

The state interpretation can keep full authority over the primary memory's
page count, or share that authority with a proof that needs an exact count.
Choose the mode when initializing the ghost state. In every mode,
`memoryPagesOwn n` is a persistent lower bound on the physical page count.

- **Legacy.** The state holds full authority. It can grow memory and issue new
  lower-bound snapshots.
- **Exact.** The state retains half of the authority. Growth consumes the
  client's linear `memoryPagesHalf n` and returns it at the new count.
- **Frozen.** The client holds a persistent `memoryPagesFrozen n`. It agrees
  with the state's retained half on the same count at every step.

## Existing proof callers

1. Introduce the extra instance in a callback to a legacy adequacy theorem.
   For example, change `intro gs` to `intro gs legacyPages` in a partial-WP
   callback, or `intro hlc gs` to `intro hlc gs legacyPages` in a total-WP
   callback. The frontend supplies the instance even when the program never
   grows memory. See the [partial-WP migration](CodeLib/RustStd/U64/AbsDiff.lean)
   and the [GCD total-WP migration](CodeLib/Examples/Gcd.lean).
2. A wrapper that calls `memoryPagesAuth_update`, `stateInterp_memoryGrow`,
   `twp_memoryGrow`, or a legacy tracked-growth rule needs
   `[WasmMemoryPagesLegacy α]`. Put it after the Wasm ghost-state instance.
   Thread it through each wrapper that uses the rule. Read-only page
   operations work for an arbitrary `WasmMemoryPagesGS α`.
3. At the state-interpretation level, growth also takes a proof that the cap
   passed to `Mem.grow` is the store's physical cap for primary memory.
   At instruction-rule call sites this equality is usually `rfl`.
   A host-return proof must preserve the tracked physical cap entries and
   their page bounds. A host that preserves the page count can use
   `stateInterp_hostCallReturn_samePages` in all three modes.

The `stateFrac` field of `WasmMemoryPagesGS` defaults to one when constructing
a record. A proof with an arbitrary instance needs evidence of that equality.
A custom initializer can obtain the witness from
`memoryPages_init_authority_legacy` or `memoryPages_init_legacy`. After
installing the returned ghost state, use
`letI : WasmMemoryPagesLegacy α := ⟨hmode⟩`. The older initialization lemmas
still return their original resources and omit this witness. See the
[compiled migration examples](CodeLib/Examples/MemoryPages.lean).

## Exact and frozen clients

Use `smallStep_init_exact_at_caps` to initialize an actual store and receive
a matching linear half. The supplied cap map identifies which instantiated
physical cap entries the proof tracks. The initializer requires the entries to
agree with the store and the primary page count to fit its tracked cap.
`twp_memoryGrow_exact` proves successful growth when the requested count fits.
`twp_memoryGrow_exact_failure` proves the failure branch above the cap and
returns the original token. See the [growth rules](CodeLib/SepLogic/SmallStepMemoryCaps.lean).

For a fixed-size proof, use `smallStep_init_frozen_at_caps` or freeze an
existing client half with `memoryPagesHalf_freeze`. The persistent token pins
the physical count. With a proof of the client's total WP,
`frozen_pages_at_every_prefix` obtains that count at any reached
configuration, including a running one. See the [initializers and frozen-page theorem](CodeLib/SepLogic/SmallStepExactPages.lean).

For a growing client, `bounded_pages_at_every_prefix` uses a total WP that
returns an exact token within a bound. Supply a terminating execution from the
same initial configuration. The theorem carries a snapshot from the chosen
prefix to that execution's terminal store to establish the bound. See the
[growing-page theorem](CodeLib/SepLogic/SmallStepGrowingPages.lean).
