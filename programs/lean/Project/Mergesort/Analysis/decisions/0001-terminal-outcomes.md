# Decision 0001: normal return versus terminal OOM

Status: **implemented, validated by the closed non-target caller/frontend
acceptance theorem, and connected conditionally to the public partial entry
specification**.

## Problem

The public theorem currently justified by Iris is partial and
outcome-sensitive.  It must classify every finite terminal execution as either
a normal `.done []` result with sorted output or the exact
`.trapped (.host OOM.trapMessage)` result with the OOM marker raised, without
claiming that a terminal execution exists.  The original Iris language maps
only `.done values` through `toVal`; `.trapped reason` is irreducible and not a
value.  Consequently its ordinary adequacy theorem cannot express the required
two-way terminal postcondition for code that may OOM.

The removed `Outcome` definition supplied only an alternative `ToVal`.  It did
not provide a `Language` instance, outcome-aware lifting rules, or adequacy, so
no existing WP theorem used it.

## Requirements

- One authoritative `SmallStep.Step` relation; no proof-only transition system.
- One principal contract per function, including both normal and OOM behavior
  where applicable.
- Compositional call rules: callers do not reopen allocator or callee bodies.
- Exact trap reason and final OOM host marker.
- Partial correctness: every finite observable terminal trace is classified;
  no termination or strong-normalization claim is introduced accidentally.
- Unrelated terminal traps do not satisfy the public postcondition.
- Existing normal-return proofs, especially `func2`, should remain reusable.

## Candidates

### A. Add an outcome-valued Iris view on the authoritative expression — selected

Map `.done` and `.trapped` to a shared `ObservableOutcome`.  This is semantically
clean and gives ordinary WP, as well as internal total-WP proofs where
available, a terminal postcondition for both cases.  A
Lean feasibility check showed that a higher-priority local/scoped
`Language (Expr α) ... ObservableOutcome` instance can coexist with the
existing `List Value` instance outside that scope.  Therefore the selected
design does not require changing every existing client globally.  Both views
use the same authoritative `Expr`, `MachineStore`, and `Step`.

### B. Add a separate outcome-language wrapper

Wrap the same `Expr`, `MachineStore`, and `Step` in a distinct expression type
whose values are `ObservableOutcome`.  This avoids changing existing clients,
but existing lifting rules and `func2` proofs do not transport automatically;
the spike must demonstrate a small, maintainable bridge rather than duplicate
the whole Wasm lifting library.

### C. Keep normal TWP and add relational trapping contracts

Use current TWP for resource-safe normal paths and `TrapsWith` contracts for
allocator failure.  This has the smallest core change and directly matches the
public predicates.  Its risk is duplicate symbolic execution: if the trap
contract must reanalyze every caller body, it violates the one-contract rule.
The red-team audit found that it does not compose with the retained
continuation-passing `twp_sort`: its NotStuck form cannot accept a continuation
that later traps, while its MaybeStuck form forgets the trap reason and final
host state.  A parallel `TrapsWith` proof would replay caller control flow.

### D. Maybe-stuck TWP plus terminal classification

Use total WP at `MaybeStuck` for strong normalization, ordinary WP for normal
postconditions, and a separate proof that every reachable irreducible state is
either a correct `.done` or exact OOM.  This preserves lifting rules, but the
exceptional-classification proof duplicates control-flow reasoning: total WP
can supply normalization, but not the exact terminal reason and host marker.

## Rejected direction

Treating all newly grown pages as a concrete `pointsToBytes` list does not solve
this outcome problem and creates an allocator interface that scales with page
capacity rather than the requested logical object.  It is rejected independently
of which terminal architecture wins.

Candidate C is also rejected for this proof pipeline.  Making it compositional
would require a new relational segment logic with prefix/bind/frame rules and
a state-sensitive bridge from existing TWP contracts.  That is effectively a
second proof logic and violates the requirement to analyze each body once.

Candidate D is rejected for the same duplication reason.  Candidate B remains
semantically possible but would require its own language instances, lifting
rules, adequacy, and a continuation-aware transport of the existing sort
contract; it is not a local wrapper.

## Selected Lean interface

The canonical `ObservableOutcome` moves next to `Expr` in the authoritative
small-step layer (the duplicate currently in `CodeLib.Equivalence` is removed):

```text
inductive ObservableOutcome
  | done (values : List Value)
  | trapped (reason : TrapReason)

ObservableOutcome.toExpr
  | done values => Expr.done values
  | trapped reason => Expr.trapped reason
```

Inside the outcome-proof scope, the active `ToVal`/`Language` instance for
`Expr` uses `ObservableOutcome`: both `.done` and `.trapped` are values and
`.running` is not.  `ofVal` is `ObservableOutcome.toExpr`.  Outside that scope,
legacy success-only clients may retain the existing `List Value` instance.
The authoritative `Step` relation is unchanged, and both terminal constructors
remain irreducible.

Shared total-WP lifting rules must be generalized over their terminal value
type rather than copied.  In the outcome scope they quantify
`Φ : ObservableOutcome -> IProp`.  Normal administrative completion applies
`Φ (.done values)`; a host trap applies `Φ (.trapped reason)` after updating
StateInterp and the owned host-state fragment.  A compatibility helper

```text
NormalPost Q (.done values) = Q values
NormalPost Q (.trapped _)   = False
```

serves closed success-only clients within the outcome view.  It is not used for a success-only callee
inside an OOM-capable caller: such a callee remains polymorphic in the caller's
arbitrary outcome post so a later caller instruction may trap.

The authoritative function theorem shape is therefore:

```text
forall Φ callerContinuation framedState,
  P(args, resources) -*
  (forall normalResult normalResources,
     Qnormal ... -* WP callerContinuation [{ Φ }]) -*
  (Qoom ... -* Φ (.trapped (.host OOM.trapMessage))) -*
  WP callWithContinuation [{ Φ }]
```

Success-only functions omit the OOM premise after proving their reachable
branches cannot trap.  `func6` has no normal-continuation premise.  Every
OOM-capable contract owns `Streams input output raised`; the terminal premise
receives `Streams input output true` plus the exact framed resources.

The store-sensitive adequacy post is generalized from
`List Value -> MachineStore -> Prop` to
`ObservableOutcome -> MachineStore -> Prop`.  The public bridge uses the
ordinary Iris adequacy theorem to derive `PartiallyMeetsOutcome`: every finite
trace ending in either observable outcome satisfies the store-sensitive post.
The merge-sort specialization accepts only normal sorted output or
`.trapped (.host OOM.trapMessage)` with the raised marker; every other terminal
outcome makes the pure post false.  This lowering does not exhibit a terminal
trace or prove strong normalization.

## Implemented infrastructure and completed acceptance test

The implementation now establishes all of these in compiled CodeLib modules:

- `ObservableOutcome` is canonical beside `Expr` in the interpreter;
- `TerminalView.canonicalLanguage` fixes the authoritative primitive-step
  relation while varying only terminal observation;
- the outcome-valued scoped `Language` and matching `IrisGS_gen` elaborate
  total WP over the existing Wasm `Expr` and ghost state;
- every shared total lifting rule is polymorphic in the selected terminal
  view, rather than copied; and
- the complete CodeLib build passes, including legacy `List Value` proofs and
  outcome-scoped checks for `.done`, `.trapped`, and `twp_const`.

The exact `talos.oom` import WP and generic store-sensitive partial and total
adequacy helpers compile against this interface.  The partial helper preserves
the precise terminal outcome and final host store for every finite trace.  The
`func2_correct` theorem now adapts the retained generated-body proof to the
reviewed canonical representations without an outcome-specific lifting
library.

The required closed miniature is now implemented in
`Project/Mergesort/OutcomeInfrastructure.lean`:

```text
function caller(flag):
  if flag then return 7
  else call a host function that traps with a marked OOM state
```

Its one principal caller contract proves, without reopening the host body at
the caller, both:

- `flag = true`: finite normal return with value seven;
- `flag = false`: finite exact OOM trap with the marker raised;

For this deliberately closed finite example, the shared store-sensitive total
adequacy lemma derives
`acceptance_returns` and `acceptance_oom` from that contract.  The normal arm
uses the generic total lifting library in the outcome view; the OOM arm uses
only the reviewed import theorem.  Lean diagnostics are clean and the three
acceptance theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
This validates the outcome architecture without executing any generated
merge-sort function body.  It is an infrastructure acceptance test, not a
termination proof for the exported merge-sort driver.

The generated entry now has a separate axiom-free conditional composition:
`entry_adequacy_of_func3` takes a polymorphic future `Func3Spec` theorem,
constructs the exact initial runtime, stack, bump-heap, and Streams resources
at a genuine `call 6`, and proves `PublicEntrySpecification`.  Normal return
maps to `.done []` with a sorted permutation; each of the reserve, values, and
scratch `DriverOOMState` cases maps to the exact `talos.oom` terminal result.
All internal and ghost resources are hidden from the public postcondition.

## Decision

Candidate A is the selected architecture because it directly matches the
one-contract requirement: the active merge-sort Iris view treats both
`.done values` and `.trapped reason` as observable terminal outcomes.  A single
outcome-valued postcondition can accept normal return or the exact OOM
reason/marker and reject every other terminal trap.  At the public boundary,
the function contract is converted to ordinary WP and discharged through the
strongest sound partial adequacy theorem currently available.

The compatibility requirements enforced by the implementation are:

- a normal-only adapter must preserve existing success contracts;
- the continuation-passing shape of `twp_sort` must remain usable without
  reopening its body;
- host-call lifting must return the exact trap reason and host resource to the
  common outcome postcondition; and
- partial adequacy must preserve a completed observable outcome and its final
  store without claiming that completion occurs.

The choice is implementation-validated: the closed flag/host-trap caller and
frontend theorem pass, and the real conditional entry theorem typechecks using
store-sensitive partial adequacy and the exact host-import contract.  The
generated `Func3Spec` is frozen by the representation and two-sided call-site
reviews.  The public theorem now applies the bridge directly, with its sole
temporary `sorry` isolated in `func3_correct : Func3Spec`; no body-entry or
total-correctness scaffold remains.

## Implementation follow-up

The milestone above is retained as the historical acceptance record for the
conditional bridge.  The generated `func3_correct : Func3Spec` proof is now
complete, and `Proof.mergesort_correct` instantiates
`entry_adequacy_of_func3` without a merge-sort proof placeholder.  The result
remains outcome-sensitive partial correctness and still makes no termination
claim.
