# Proof ledger

## Status meanings

- `discovered`: body and calls are annotated.
- `first pass`: a useful dossier exists, but one or more required analysis
  fields or call-site details remain open.
- `draft contract`: semantic interface written but not audited.
- `frozen`: provability and all call sites audited.
- `proved`: Lean theorem closed and verified without unapproved axioms.
- `adequate`: connected to the public fuel-free theorem.

## Current status

| Component | Status | Evidence / blocker |
| --- | --- | --- |
| Frozen artifact and module | discovered | hashes and inventories recorded |
| All 56 function cards | first pass | one card per generated definition, but completeness and exact call-site preparation are not yet audited |
| Public-path dossier review | frozen | cards 0--11 record ABI, ownership, effects, control flow, valid call sites, terminal outcomes, loop measures, and originating exclusion guards |
| Excluded panic/error-support documentation | frozen | all funcs12--55 cards are documentation-only; direct and indirect subgraphs were audited without introducing callee specs |
| Call-site matrix | frozen | every valid edge has exact operands/resources/outcomes; unreachable edges remain caller-guard obligations |
| Valid-input exclusion boundary | frozen | all 11 frozen-WAT calls from funcs0--11 into funcs12--55 are assigned to exact originating guard obligations; independent red-team recheck passed |
| Codec and sorting vocabulary | frozen for current contracts | canonical `U32Codec`, serialization, byte-array equivalence, zero-fill serialization, aligned and arbitrary-four-byte word views, output-slot store reconstruction, empty dangling-pointer buffers, live-word token framing/resealing, allocator-order disjointness, exact byte/word offset and append arithmetic, `WordSlice_get`/`WordSlice_set`, `SortBuffers_append`, element-copy focus, and final whole-buffer copy-back focus compile; the exact merge/remainder inequalities are recorded at their originating guards |
| Terminal outcome bridge | proved | canonical outcome view, generic lifting, exact import-2 WP, store-sensitive partial outcome adequacy, and both arms of the closed non-target caller/frontend acceptance theorem are closed and axiom-audited |
| Allocator ownership | frozen interface / body proof pending | map-native history, live/retired tokens, retired-byte ownership, pure transition preservation, frontier authority, sparse physical fresh-range insertion, post-store `BumpHeap_commit`, complete `BumpHeap_retire`, reachable align-1/4 `BumpDecision` arithmetic, signed page-target bound, hard-cap grow success, unique live geometric lookup, exact reallocation-history progression, no-reserve append, and normal `GeometricVecFacts.reserveSuccess` are proved; allocator continuations accept exact OOM on physical grow failure instead of assuming an unlinked cap fact, while instruction-level cursor/store/domain/metadata composition remains implementation work |
| Exact contract declarations | re-frozen | `Contracts.lean` declares exactly imports 0--2 and funcs0--11 with outcome-valued continuations and no funcs12--55 contract. Every statement passed body-to-post and caller-to-pre/continuation review. Proof attempts caught and corrected both requesting running-instance ownership after a terminal host trap and incorrectly sharing one operand list between a shim call and its direct import call. |
| Imports/read/write shims | proved | exact host transfer lemmas exist; the false zero-length write generalization was removed; direct-import and shim-call operand lists are distinct. Authoritative proofs of imports0--2 and funcs6,10,11 compile and are axiom-audited. |
| Recursive `func2` sort | proved | `func2_correct` adapts the generated-body theorem to the canonical `SortBuffers` contract and reconstructs its exact piecewise scratch post; the theorem compiles without `sorry` or a declared axiom |
| RawVec/allocator functions | partial proof | funcs0,1,5,8,9 pass both statement directions. `func4` identity and `func7` logical retirement are proved; `func1` returns the exact shadow-frame bytes, and `func0` freshness is justified by frontier/domain authority. Prior allocator proof file contains only a concrete smoke test. |
| Export `func3` | frozen statement / body unproved | `Func3Spec` has exact normal and phase-classified OOM posts; read, decode, sort, output, retirement, mask arithmetic, and public-entry continuation directions all pass review |
| Entry adequacy | conditionally adequate | `entry_adequacy_of_func3` derives the real partial `PublicEntrySpecification` from a polymorphic `Func3Spec` hypothesis.  It constructs the exact runtime, raw 288-byte stack region, bump heap, and Streams resources, starts with a genuine `call 6`, maps all three `DriverOOMState` variants to exact `talos.oom`, and hides internal resources.  It deliberately makes no termination claim. |
| Public theorem | partial theorem conditionally proved | once `func3_correct` is closed, the public partial theorem is exactly `entry_adequacy_of_func3 func3_correct`.  The older total `MergesortSpec` remains a separate future termination obligation and is not concluded by current Iris adequacy. |

## Quarantined directions

- The unused second `ToVal` view in `SmallStepLanguage` was removed.  A value
  view without a matching `Language`, lifting rules, and adequacy theorem did
  not solve terminal OOM.
- `stateInterp_memoryGrow_allocBytes` was removed.  It was broken and attempted
  to materialize every new page as byte-by-byte ownership, which does not scale
  and did not match the intended bump-heap contract.
- The unused `byteHeapAux` insertion block was removed after allocator
  red-teaming.  It required client fragments for the entire old authoritative
  heap and therefore could not implement sparse fresh-range allocation from
  `StateInterp`; decision 0002 records the required authority-only interface.
- `AllocatorProof.lean` is not authoritative; its concrete 16-byte test is only
  a regression witness.
- The earlier `Proof.lean` scaffold is intentionally not included, and
  `Project.lean` does not advertise the incomplete merge-sort proof as complete.

## Retained reusable work

- Pure merge invariants, the generated `func2` body theorem, and its proved
  adapter to the canonical `Func2Spec`.
- Total lifting rules added for shifts, comparisons, select, i64 multiplication,
  memory copy, return, and related generated instructions.
- General memory `readBytes`/`writeBytes` lemmas.
- `pointsToBytes` physical-read facts and arbitrary host byte-write ghost update.
- Concrete Universal read/write/OOM resolution and transfer lemmas.

## Hard phase gate

**Passed for imports 0--2 and local functions 0--11 after corrective
re-audits.**  One proof attempt exposed that terminal host traps consume the
exclusive current-running-instance token; another exposed that shim calls and
their direct import calls have different top-first operand lists.  The affected
statements were corrected and proved compositionally before larger body proofs
resumed.  Steps 1--5 below are complete at the statement/interface level, so
bottom-up target body proofs may continue.  Local functions 12--55 remain
permanently documentation-only: they receive incoming-edge classification,
never WP specifications or body proofs.

1. Complete and critically review every function dossier.
2. State one authoritative main WP specification for every function in the
   public proof closure, using shared representations for memory objects and
   host/runtime state.
3. Record every syntactic call site in a matrix, including operand order,
   resource preparation, all possible callee outcomes, caller continuation
   needs, excluded branches, and termination measure where relevant.
4. Red-team every contract from both directions: body-to-postcondition and
   caller-to-precondition/continuation.
5. Freeze only then the remaining allocator infrastructure required by those
   contracts.  The separately isolated terminal-outcome interface has already
   passed its non-target acceptance gate.
6. Prove the remaining frozen function specifications bottom-up.  The public
   partial-adequacy composition has already been typechecked conditionally and
   must be closed only by supplying the eventual `func3_correct` theorem.
