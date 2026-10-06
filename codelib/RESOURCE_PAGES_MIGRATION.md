# Migrate proofs to fractional page authority

The page-resource API now supports exact memory bounds alongside the existing
monotone lower-bound snapshots. Existing adequacy callbacks and wrappers around
unrestricted page updates need an explicit `WasmMemoryPagesLegacy` instance.
This is a Lean source API change; it does not change Wasm execution, the physical
memory cap, or the intended legacy functional specifications.

## Why the default does not preserve every caller

[`WasmMemoryPagesGS`](CodeLib/SepLogic/WasmHeap.lean) has a new field
`stateFrac : Qp := 1`. The default fills an omitted field when constructing a
record. It does not establish `gs.stateFrac = 1` for an arbitrary instance
`[gs : WasmMemoryPagesGS α]`, which may retain only half of the authority.

`WasmMemoryPagesLegacy α` records precisely that equality for the selected
instance. Rules such as `memoryPagesAuth_update`, `stateInterp_memoryGrow`,
`twp_memoryGrow`, and `twp_memoryGrow_tracked` require it. A generic host-return
update that may increase pages also requires it; the page-preserving
`stateInterp_hostCallReturn_samePages` rule works in either mode, with its
explicit equality and other state-preservation premises.

The restriction is necessary: full authority may advance the page count without
a client token. With half retained by the state, another owner can hold exact
page knowledge. An unrestricted update would invalidate that knowledge.
`memoryPagesAuth_half_exclusive` and `memoryPagesAuth_frozen_exclusive` prove that
the full legacy authority cannot coexist with the corresponding exact tokens.
Do not install a blanket legacy instance or infer one from a lower-bound
snapshot.

## Existing proof callers

1. Introduce the additional instance in an adequacy callback. The callback to
   `wasm_smallStep_adequacy` now quantifies over
   `[WasmSmallStepGS .hasLC α] [WasmMemoryPagesLegacy α]`.
   Change `intro gs` to `intro gs legacyPages` before entering proof mode.
   The actual migration in
   [`RustStd/U64/AbsDiff.lean`](CodeLib/RustStd/U64/AbsDiff.lean) follows this
   pattern even though the function itself does not grow memory: the additional
   binder belongs to the adequacy frontend.
2. For a total-adequacy callback that explicitly quantifies over `hlc`, change
   `intro hlc gs` to `intro hlc gs legacyPages`.
   `wasm_smallStep_terminates` has this signature; the mergesort
   [`TotalProof.lean`](../programs/lean/Project/Mergesort/TotalProof.lean)
   provides a concrete caller of the cap-aware total frontend.
3. If a wrapper calls a legacy growth or host-update rule, add
   `[WasmMemoryPagesLegacy α]` after its Wasm instance. Carry this requirement
   through callers until the adequacy frontend supplies it. Proof helpers that
   do not need an unrestricted page update need no additional constraint merely
   because they use memory.

For example, this complete Lean snippet forwards the required instance through
a page-update wrapper and shows how to construct it from an actual mode witness:

```lean
import CodeLib.SepLogic.WasmHeap

open Iris Wasm.SepLogic

example {α : Type} [gs : WasmMemoryPagesGS α]
    [WasmMemoryPagesLegacy α] (old newPages : Nat)
    (hmono : old ≤ newPages) :
    memoryPagesAuth (α := α) old ==∗
      memoryPagesAuth newPages ∗ memoryPagesOwn newPages :=
  memoryPagesAuth_update old newPages hmono

example {α : Type} [gs : WasmMemoryPagesGS α]
    (hmode : gs.stateFrac = 1) : WasmMemoryPagesLegacy α :=
  ⟨hmode⟩
```

If a custom initializer needs this witness, use
`memoryPages_init_authority_legacy` or `memoryPages_init_legacy`. After unpacking
the returned `gs` and `hmode`, install `letI : WasmMemoryPagesGS α := gs` followed
by `letI : WasmMemoryPagesLegacy α := ⟨hmode⟩`, as in the implementation of
`memoryPages_init_legacy`. The compatibility initializers `memoryPages_init`
and `memoryPages_init_authority` intentionally omit the witness from their
results; it cannot be recovered from those results alone.

## Choosing the page contract for new proofs

- Legacy mode retains full state authority, witnessed by
  `WasmMemoryPagesLegacy`. Clients hold persistent lower-bound snapshots;
  legacy rules permit unrestricted monotone updates.
- Exact mode allows growth while the state retains half the authority.
  The client holds a linear `memoryPagesHalf pages` token. Checked updates
  consume that token and return one for the new page count.
- Frozen mode also retains half the authority in the state. The client holds
  a persistent `memoryPagesFrozen pages` token, so the physical page count
  stays fixed.

`memoryPagesOwn pages` remains a persistent **lower bound** in all modes.
It is not a persistent measurement of the current exact count.

For growing proofs, [`SmallStepMemoryCaps.lean`](CodeLib/SepLogic/SmallStepMemoryCaps.lean)
provides `twp_memoryGrow_exact`: supply the retained-half equality, the linear
page token, the actual cap token, and `pages + delta.toNat ≤ cap`. Its
continuation receives the new exact page token. The separate
`twp_memoryGrow_exact_failure` rule covers requests strictly above the actual
cap and preserves the token. Success is established in the repository's memory
semantics, not assumed as an execution outcome.

The retained fraction is fixed in the chosen ghost instance. Thread the linear
token through allocator and caller contracts that can grow memory. It cannot
be replaced by a persistent allocation policy or used to construct a legacy
instance. Freezing via `memoryPagesHalf_freeze` gives up the permission to
increase the count.

[`SmallStepExactPages.lean`](CodeLib/SepLogic/SmallStepExactPages.lean) supplies
`smallStep_init_exact_at_caps` and `smallStep_init_frozen_at_caps`. Both allocate
resources for the supplied physical store without replacing its memory, cap,
runtime instance, or host. `frozen_pages_at_every_prefix` derives exact pages
throughout a proved client execution. For growing clients,
[`SmallStepGrowingPages.lean`](CodeLib/SepLogic/SmallStepGrowingPages.lean)
provides `bounded_pages_at_every_prefix`; its caller must also establish the
terminal execution premise. Neither frontend makes the client's execution
proof optional.
