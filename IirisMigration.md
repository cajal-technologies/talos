# Iris migration plan

## Status and scope

This document is the working plan for the small-step and iris-lean migration on
the `iris` integration branch. Branches implementing this plan must be created
from `iris` and should target `iris` in their pull requests. Keep PRs small
enough that the old and new paths can coexist and be compared throughout the
migration.

The final architecture has:

- one relational small-step semantics, `Step`, used by iris-lean;
- one deterministic executable step function, `step?`, proved equivalent to
  `Step`;
- a fuel-bounded runner obtained by iterating `step?`;
- no separate, unproved executable semantics;
- iris-lean instances and proof rules for the complete supported interpreter;
- preserved behavioral and test coverage for all currently supported features.

The migration may change theorem statements and proof structure. It should
preserve the intent and coverage of existing examples wherever possible. Iris
proofs provide partial correctness for now: they describe executions that
reach completion but do not prove that completion occurs.

## Fixed design decisions

### Machine boundary

The target shape is approximately:

```lean
inductive Expr
  | running : ThreadState → Expr
  | done : List WasmVal → Expr
  | trapped : TrapReason → Expr
  deriving BEq, Repr

structure Store where
  functions : Array Function
  memories : Array Memory
  globals : Array Global
  tables : Array Table
  deriving BEq, Repr

structure Config where
  expr : Expr
  store : Store
  deriving BEq, Repr
```

These names and field types may change as the implementation teaches us more.
The ownership boundary must not become ambiguous:

- `ThreadState` owns the operand stack, locals, remaining code, control frames,
  call frames, and other per-execution control state.
- `Store` owns shared runtime resources, including functions, memories,
  globals, tables, segments, exception/GC data, and explicitly modeled host
  state where applicable.
- `.done` and `.trapped` are terminal.
- Exhausting runner fuel is not a semantic state and must not appear in `Expr`
  or `Step`.
- Validation or malformed internal configurations must remain distinguishable
  from runtime traps. Decide their representation before porting cases that
  currently return `.Invalid`.

### Step granularity

One `Step` normally executes one Wasm instruction. A step may perform all
atomic state effects intrinsic to that instruction.

Zero-instruction administrative steps are allowed to:

- expose, push, pop, or unwrap control frames;
- set up, enter, return from, or tail-call a function;
- route branches and returns through their enclosing frames;
- propagate a trap or exception;
- otherwise rearrange the abstract machine so the next instruction can run.

Prefer explicit administrative transitions to hiding several stages of control
behavior in one large transition. Do not split an ordinary instruction merely
because its implementation uses several helper functions. Any deviation from
this policy must be documented because step granularity determines the
atomicity exposed to Iris.

### Determinism

Assume the semantics is deterministic and target:

```lean
theorem step_iff {config config' : Config} :
    step? config = some config' ↔ Step config config'
```

Flag a case before implementation if it depends on scheduling, external input,
unspecified host behavior, or arbitrary choice. First consider making the
choice an explicit input or policy in `Store`. If genuine nondeterminism is
necessary, stop and design an executable successor collection and corresponding
Iris relation; never silently select one result.

### Sources of truth

- `Step` is the authoritative semantic relation.
- `step?` is its proved-equivalent executable presentation.
- The fuel-bounded runner is an iterator over `step?`.
- Iris instances and rules refer to `Step`, not to a second transition system.
- During coexistence, the old big-step interpreter is a regression oracle, not
  a permanent second specification.

## Definition of done

The migration is complete only when all of the following hold:

- Every instruction and proposal feature currently accepted by the decoder and
  interpreter has a small-step implementation or is explicitly documented as
  intentionally unsupported.
- `step?` is sound and complete with respect to `Step`.
- Determinism and terminal-state theorems are proved.
- The iterator over `step?` supports the runner and differential-testing CLI,
  including success, trap, invalid-input, and out-of-fuel classifications.
- Existing Lean examples and program packages have either been ported or have a
  reviewed replacement preserving their intent.
- Current differential seeds and the miscast/V8 workflow do not regress.
- The supported WebAssembly testsuite baseline does not regress.
- All required iris-lean language, state-interpretation, weakest-precondition,
  and proof-mode instances compile against a pinned iris-lean revision.
- The Iris heap model is connected to physical Wasm memory; memory facts are not
  merely unrelated ghost assertions.
- The handwritten memory corpus, including quicksort and mergesort, has both
  executable tests and Iris proofs.
- The old big-step implementation and temporary compatibility code are removed.
- The branch-only warning in `AGENTS.md` is removed or rewritten as permanent
  architecture documentation before merging `iris` into `main`.

## Cross-cutting invariants

State these early and preserve them at every transition:

- Operand and result stacks have the shapes required by the current
  instruction and control frame.
- Local, function, global, memory, table, type, tag, and segment indices are
  resolved consistently.
- A valid control stack determines an unambiguous next instruction or terminal
  result.
- Store mutation affects only the addressed resource and preserves unrelated
  resources.
- Linear-memory reads and writes obey bounds, width, offset, endianness, and
  overlap rules.
- Memory growth preserves old bytes and initializes new bytes correctly.
- Allocation and append-only structures use fresh, valid indices.
- Trap propagation cannot resume normal execution.
- Host interaction is explicit and deterministic under a fixed host policy.
- Initialization creates a state satisfying the runtime invariants.

Not all invariants need to be fields of `ThreadState` or `Config`. Prefer
well-formedness predicates and preservation theorems unless carrying evidence
in the data makes later proofs substantially simpler.

## Milestones

### M0 — Freeze the baseline and coverage map

Tasks:

- Pin the current `main`/`iris` baseline commit and the iris-lean revision.
- Run and record builds for `interpreter`, `codelib`, and `programs/lean`.
- Run the current WebAssembly testsuite and differential-testing workflows.
- Record existing expected failures, skips, timeouts, and known float-output
  noise rather than silently baselining new failures.
- Generate a coverage matrix from `Instruction`, decoder support, `execOne`,
  examples, testsuite cases, and differential seeds.
- Classify current results: success, trap, invalid, out-of-fuel, host effect,
  and unsupported.
- Inventory the existing `CodeLib.SepLogic` implementation. Mark each component
  as reusable, replaceable by iris-lean language machinery, or temporary.

Exit checks:

- Baseline commands and results are committed in a reproducible form.
- Every instruction constructor has an owner/milestone and at least one planned
  regression check.
- Known gaps are visible and are not confused with migration regressions.

### M1 — Introduce the abstract-machine types

Tasks:

- Define `TrapReason` as structured data instead of relying on free-form strings
  where practical.
- Define `Expr`, `ThreadState`, `Store`, control frames, call frames, and
  `Config`.
- Define module instantiation and entry-point initialization into `Config`.
- Define well-formedness predicates and terminal-state predicates.
- Decide how current `.Invalid` cases are represented. Prefer ruling them out
  with validation/well-formedness, while retaining an executable diagnostic
  path for malformed inputs.
- Write projections/conversions needed to compare old and new stores.

Exit checks:

- Representative straight-line, block, loop, call, return, trap, memory, table,
  exception, GC, and host states can be represented without placeholders.
- The state split accounts for every field of the current runtime `Store`.
- Initialization tests agree with the old interpreter on memories, globals,
  tables, and active/passive segments.

### M2 — Build the small-step kernel

Start with the smallest coherent subset:

- terminal and administrative transitions;
- constants, locals, globals, stack operations, and integer arithmetic;
- normal fallthrough and structured traps;
- blocks, loops, `if`, branches, returns, direct calls, and recursion.

For every transition family:

- add relational `Step` constructors;
- implement the matching `step?` branch;
- prove local soundness and completeness lemmas;
- compose them into global `step?_sound`, `step?_complete`, and `step_iff`;
- prove deterministic successor behavior;
- prove terminal configurations have no successors;
- prove preservation of the relevant well-formedness invariants;
- add positive, trap, and boundary tests.

Exit checks:

- Existing non-memory control-flow examples run on the new stepper.
- Factorial, GCD, early branches/returns, recursion, and infinite-loop
  out-of-fuel behavior have regression coverage.
- A trace printer can show administrative and instruction steps separately.

### M3 — Add the executable runner and old/new equivalence harness

Tasks:

- Define a fuel-bounded reflexive execution/iterator over `step?`.
- Return distinct success, trap, invalid, and out-of-fuel results.
- Prove basic iterator facts: zero fuel, fuel monotonicity after a terminal
  result, terminal stability, and trace-to-multistep correspondence.
- Preserve the current runner CLI/output contract used by differential tests.
- Build an old/new comparison harness over a common initial state and observable
  result projection.
- Compare terminal values, traps, selected store observations, and classification
  of out-of-fuel without requiring equal fuel counts.

The strongest desirable compatibility result is:

- old success implies a new finite trace to the same observable success;
- new success implies an old run with the same observable success;
- likewise for traps;
- neither relation claims equal internal states where representation changed.

Prove this per migrated instruction family where feasible. Use executable
differential checks until the global theorem is practical.

Exit checks:

- The new runner can replace the old runner for the M2 subset.
- Random and enumerated small programs find no unexplained divergence.
- Runner canaries continue to distinguish rejection, trap, and out-of-fuel.

### M4 — Port linear memory completely

Port in layers:

1. scalar loads/stores of every supported width and sign extension;
2. float and SIMD memory operations;
3. `memory.size` and `memory.grow`;
4. `memory.fill`, overlapping `memory.copy`, `memory.init`, and `data.drop`;
5. memory64 and multi-memory, including cross-memory copy;
6. initialization from active/passive data segments.

Tasks and checks:

- Prove byte-level read/write lemmas once and reuse them.
- Prove framing: a write changes only its target byte range.
- Prove failed bounds checks trap without partially mutating memory.
- Test zero lengths, exact-end accesses, one-byte overflow, large offsets,
  overlapping copies in both directions, dropped segments, growth limits, and
  address-width boundaries.
- Connect iris-lean ghost ownership to the physical memory in `Store`.
- Provide points-to, array/region, splitting, joining, load, store, copy, fill,
  and allocation/growth rules needed by program proofs.

Exit checks:

- All current memory examples pass on the new runner.
- Existing region and array lemmas have a replacement or compatibility bridge.
- Memory rules are proved from `Step` and the actual state interpretation.

### M5 — Port tables, references, calls, exceptions, GC, SIMD, and hosts

Use separate reviewable PRs for:

- tables, element segments, indirect calls, typed function references, and tail
  calls;
- exception tags, throwing, catching, and trap/exception distinction;
- reference and GC heap operations, subtyping, allocation, and casts;
- remaining SIMD and numeric conversions;
- host calls and host-owned state;
- imported/exported memories, globals, tables, and cross-module behavior.

At the start of each track, audit it for nondeterminism. Host calls in
particular must expose all result-producing inputs in the modeled state or
policy.

Exit checks:

- Every constructor in the coverage matrix is checked off.
- Existing feature-specific examples and differential seeds pass.
- No transition relies on an arbitrary list/array choice or opaque host result.

### M6 — Complete the iris-lean adapter

Tasks:

- Implement the iris-lean language interface for `Expr`, `Store`, values,
  terminal expressions, and primitive steps using the pinned API.
- Prove the required language laws from `Step`.
- Define the state interpretation for memories and other mutable resources.
- Implement weakest-precondition rules for administrative steps, ordinary
  instructions, traps, calls, control flow, and memory.
- Add derived rules at the level program proofs need: sequences, blocks, loops,
  calls, frames, arrays, and memory regions.
- Port or replace `CodeLib.SepLogic`; do not leave two competing Wasm WPs.
- Prove adequacy to the new small-step semantics.
- Document clearly that adequacy currently gives partial correctness, not
  termination.

Exit checks:

- No Iris rule mentions the old big-step `exec`, `execOne`, or `run`.
- Ghost memory and physical memory are tied by the state interpretation.
- Proofs can frame unrelated memories/resources and compose calls.
- At least one loop and one recursive call are proved through iris-lean.

### M7 — Trust-building handwritten memory corpus

Keep the programs small, handwritten, and reviewable. Prefer `.wat` sources
checked into the repository and decoded through the same supported path used by
the runner. If hand-built Lean modules are also useful for proof ergonomics,
prove or test that they decode to the same relevant module structure.

Build the corpus as a ladder:

1. `load_store.wat`: store and reload 8/16/32/64-bit values; prove little-endian
   layout, round-trip behavior, framing, and out-of-bounds traps.
2. `swap.wat`: swap two `i32` array elements; prove the two values exchange,
   array length is unchanged, and all other bytes are framed.
3. `reverse.wat`: reverse an in-memory array; prove bounds safety, permutation,
   and the expected index relation.
4. `copy_overlap.wat`: exercise overlapping moves in both directions; prove
   memmove-style behavior and no partial write on a trapping case.
5. `partition.wat`: the partition kernel used by quicksort; prove bounds,
   permutation, pivot placement, and left/right partition predicates.
6. `merge.wat`: merge two adjacent sorted ranges using a disjoint scratch
   region; prove sorted output, permutation, scratch/target framing, and bounds.
7. `quicksort.wat`: in-place quicksort over an `i32` array.
8. `mergesort.wat`: mergesort over an `i32` array with an explicit scratch
   buffer.

For quicksort and mergesort, formalize at least:

- a precondition describing valid, non-overflowing byte ranges and disjointness
  where required;
- no trap for executions that reach the relevant instruction states under the
  invariant;
- memory safety: every load/store stays within the owned regions;
- sortedness of the output range;
- permutation/multiset equality with the input range;
- framing of memory outside the target and scratch regions;
- preservation of array length and element representation;
- behavior for empty, singleton, duplicate-heavy, already sorted, reverse
  sorted, minimum/maximum `i32`, and pivot-adversarial arrays.

Because Iris does not yet establish total execution here, state the main
quicksort and mergesort theorems as partial-correctness results. Keep loop or
recursion measures in the proof design and document them so termination can be
added later. Separately run the executable stepper on exhaustive small arrays
and randomized larger arrays to establish engineering confidence that the
programs complete.

Each corpus example needs four kinds of evidence:

- parser/decoder and validation coverage;
- concrete `native_decide` or runner checks;
- old/new differential checks while the old interpreter exists;
- an iris-lean proof against the small-step semantics.

Exit checks:

- Both sorting implementations meet all listed functional and framing
  properties.
- Mutation tests that alter a comparison, index, bound, or store cause an
  expected proof or test failure.
- Concrete outputs also agree with an independent host-language sorting oracle.

### M8 — Port the existing proof corpus and downstream programs

Tasks:

- Port examples by intent, not by syntactic similarity.
- Maintain a ledger mapping every old theorem/example to its new theorem,
  replacement test, intentional deletion, or deferred termination claim.
- Port `CodeLib` lifting lemmas and Rust memory/array abstractions.
- Port `programs/lean` specs in coherent groups.
- Replace fuel-free total-correctness statements with accurately named
  partial-correctness statements where necessary; do not imply termination.
- Preserve result-and-memory observations used by equivalence proofs.

Exit checks:

- No old example disappears without a reviewed ledger entry.
- Downstream packages build entirely against the new public API.
- Deferred termination properties are documented in one searchable list.

### M9 — Cut over and clean up

Tasks:

- Switch all builds, runners, tests, docs, and imports to the new semantics.
- Run the complete baseline suite and investigate every delta.
- Remove the old big-step semantics, obsolete WPs, compatibility conversions,
  and temporary differential harness.
- Check for dead definitions and stale references to the old result/fuel model.
- Update architecture documentation and public specification guidance.
- Remove or rewrite the branch-only migration warning in `AGENTS.md`.

Exit checks:

- All three packages build from a clean checkout.
- Differential and testsuite results are at least as strong as the M0 baseline.
- The handwritten corpus and all iris-lean proofs build in CI.
- There is exactly one semantic relation and one proved executable stepper.
- No migration TODO lacks an owner or follow-up issue.

## Per-PR checklist

Every migration PR should answer:

- Which milestone and coverage-matrix rows does this PR address?
- Which old behavior is the oracle, and what observation is compared?
- Does the PR add both `Step` and `step?` support?
- Are soundness, completeness, determinism, and invariant preservation proved?
- Does it introduce or expose possible nondeterminism?
- Are success, trap, invalid, and boundary cases covered as applicable?
- Are unrelated store components proved or tested unchanged?
- Which existing examples or theorems were ported?
- Which commands were run in each affected Lake package?
- Does the PR change Iris atomicity or the `Expr`/`Store` ownership boundary?
- Are new TODOs linked to a milestone and prevented from silently becoming the
  permanent architecture?

Do not merge a feature transition with only an executable test and no
relational correspondence proof. Do not remove the old implementation for a
feature until the replacement has equivalent coverage.

## Continuous checks

Run checks in increasing cost:

### On each focused PR

- `git diff --check`
- `cd interpreter && lake build`
- focused `lake env lean <file>` while iterating
- focused old/new trace and result comparisons
- affected handwritten examples and differential seeds

### When `CodeLib` changes

- `cd codelib && lake build`
- all Iris adequacy and state-interpretation tests
- memory-rule framing and negative tests

### When public APIs or generated programs change

- `cd programs/lean && lake build`
- freshness and equivalence checks used by CI

### At milestone boundaries

- clean builds of every package in dependency order;
- the complete existing example corpus;
- the WebAssembly testsuite baseline comparison;
- `just differential` and the pinned seed corpus;
- exhaustive bounded small-program old/new comparison for the migrated subset;
- randomized traces with reproducible seeds;
- sorting-corpus concrete and Iris checks after M7.

## Migration ledger

Maintain a table in this document or a nearby generated file:

| Area | Old implementation/proof | New implementation/proof | Tests | Status | Notes |
|---|---|---|---|---|---|
| Initialization | `Module.initialStore` | TBD | TBD | Not started | Include segments/imports |
| Core stepping | `execOne`/`exec` | `Step`/`step?` | TBD | Not started | |
| Runner | `run`/`runTail` | fuel iterator | differential canaries | Not started | |
| Control flow | current WP tactics | Iris rules | control examples | Not started | |
| Linear memory | `Mem`, memory arms | small-step memory | memory ladder | Not started | |
| Iris integration | `CodeLib.SepLogic` | iris-lean adapter | adequacy proofs | Not started | Reuse vs replace audit |
| Existing examples | `Interpreter/Wasm/Examples` | ported corpus | package build | Not started | |
| Downstream proofs | `CodeLib`, `programs/lean` | new API | package build | Not started | |

Expand this ledger before M2 and update it in every migration PR.

## Resolved architecture questions

These are starting decisions, not open questions. Changing one requires an
explicit architecture PR that updates this document and explains the effect on
the small-step relation, executable stepper, runner, and Iris rules.

### Where `Module` lives

**Decision:** the decoded source `Module` is initialization input, not a
parameter to `Step`. Module instantiation resolves it into immutable runtime
metadata stored alongside mutable resources in the iris-lean `State`.

Use a shape such as:

```lean
structure RuntimeEnv where
  functions : Array Function
  types : Array RuntimeType
  tags : Array TagType
  -- Other immutable instantiated metadata and resolved imports.

structure Store where
  runtime : RuntimeEnv
  memories : Array Memory
  globals : Array Global
  tables : Array Table
  -- Segments, exceptions, GC heap, host state, ...
```

`RuntimeEnv` is immutable by the transition rules even though it is nested in
`Store`. This is preferable to an external `Module` argument because the pinned
iris-lean `PrimStep` interface relates `(Expr, State)` pairs and its `Language`
instance is global for the types involved; it cannot conveniently vary with a
module value. It also handles indirect calls and multiple instantiated modules
without putting code into `ThreadState`.

Rejected alternatives:

- Putting `Module` in `Expr` duplicates immutable data in every thread and
  obscures the thread/store ownership boundary.
- Making `Step m` take an external module parameter complicates the iris-lean
  instance and makes multi-module linking awkward.
- Keeping only source-level `Module` in `Store` postpones import resolution and
  forces runtime transitions to repeat instantiation work.

Required checks:

- Prove every step preserves `store.runtime`.
- Give functions and other instantiated resources stable runtime indices.
- Keep the source `Module` available only in initialization/debug metadata when
  useful; semantic execution must use `RuntimeEnv`.

### Deterministic imports and host functions

**Decision:** concrete execution steps call a resolved host function that is a
pure Lean function of the current store and argument list. The abstract
`HostContract` is used to reason about that function, but is not itself the
executable transition relation.

The current `HostFn.invoke : Store α → List Value → HostResult α` is already
deterministic as a Lean function. Preserve that model:

- resolved `HostFn`s belong in immutable `RuntimeEnv`;
- mutable host state belongs in `Store`;
- external inputs, clocks, randomness, and oracle replies must be supplied
  explicitly in the initial host state, for example as an input stream consumed
  by calls;
- externally visible effects may additionally be emitted as iris-lean
  observations, but observations do not choose the next state;
- proof rules quantify over a `HostSpec` and assume the concrete environment
  satisfies its contracts.

The important distinction is that a relational host contract may permit several
outcomes, while `Step` must use the single result returned by the fixed concrete
host implementation. Do not define executable host stepping directly from an
underspecified contract.

Alternatives if true environmental nondeterminism becomes necessary:

1. Preferred when possible: make the environmental choice explicit in an input
   stream or oracle state. Execution remains deterministic for a fixed initial
   state.
2. Change `Step` and the executable interface to a successor relation/list.
   This is a larger architecture change and invalidates the current
   `step?_complete` shape.

### Validation and `.Invalid`

**Decision:** invalidity is a front-end/driver outcome, not a Wasm runtime
expression and not a `Step`. The semantic transition system is defined for
successfully decoded, validated, instantiated, well-formed configurations.

Use three layers:

```lean
decode      : Input → Except DecodeError Module
validate    : Module → Except ValidationError ValidatedModule
instantiate : ValidatedModule → Imports → Except InstantiationError Config
```

The runner retains an `.invalid` result for failures in these layers. Once a
`Config` starts stepping, its semantic outcomes are success or trap; fuel
exhaustion remains a runner outcome.

The current validator is deliberately partial and many current `.Invalid`
branches defensively detect malformed operand stacks or bad indices. Therefore
this decision must be reached incrementally:

- classify every existing `.Invalid` site as decode error, validation error,
  instantiation error, unreachable internal-invariant failure, or incorrectly
  classified runtime trap;
- extend validation and the well-formedness invariant until all dynamic
  defensive cases are proved unreachable from an initialized valid config;
- during migration, use a checked executable wrapper such as
  `stepChecked? : Config → Except InternalError (Option Config)` for diagnostics;
- keep the semantic `step? : ValidConfig → Option ValidConfig`, or equivalently
  require/prove well-formedness around it;
- treat an `InternalError` reached from a validated initial configuration as an
  interpreter bug and CI failure, not as a user-visible Wasm behavior.

Do not add `.invalid` to `Expr`: that would turn a validator/interpreter defect
into a language terminal state. Do not map malformed configurations to
`.trapped`: WebAssembly validation failure and runtime trap are observably
different.

### Traps, values, and stuckness

**Decision:** `.trapped reason` is an observable terminal expression but is not
an Iris value. Only `.done values` maps through `ToVal`:

```lean
instance : Iris.ProgramLogic.ToVal Expr (List WasmVal) where
  toVal
    | .done values => some values
    | _ => none
  ofVal := .done
  -- inverse laws
```

Both `.done` and `.trapped` have no `Step`. Consequently a trapped expression is
technically `Stuck` in iris-lean, while a completed expression is an
irreducible value. This is intentional: a standard not-stuck WP proof then
establishes that the program does not trap. The runner and relational semantics
still retain the trap reason for differential testing and explicit trap
theorems.

Expected-trap examples should use reachability/multistep theorems or executable
checks stating that evaluation reaches `.trapped reason`; they should not be
presented as successful WP proofs.

Alternative: make `Val` an `Outcome` containing both `.done` and `.trapped`.
That makes traps available to ordinary WP postconditions, but a standard
not-stuck WP would no longer rule them out automatically. Choose this only if
reasoning compositionally about programs expected to trap becomes more
important than making safety proofs exclude traps by construction.

An invalid internal configuration is also stuck, but it is not represented by
an `Expr` constructor and is unreachable under the validity invariant. Thus an
observable `.trapped` expression remains distinct from a malformed stuck
configuration.

### Administrative transitions and Iris atomicity

**Decision:** every instruction or administrative `Step` is one iris-lean
`PrimStep`. The default granularity remains one Wasm instruction, with explicit
zero-instruction administrative reductions for frame and call machinery.

Do not conflate “one `PrimStep`” with iris-lean's `Atomic` class. In the pinned
API, strong atomicity requires the successor to be a value, and weak atomicity
requires it to be irreducible. Most Wasm instruction steps leave a runnable
`.running` expression, so most instructions are neither strongly nor weakly
atomic in that technical sense.

Proof-rule policy:

- expose instruction steps in primitive semantic lemmas;
- provide derived WP rules that hide deterministic frame-unwrapping, call
  setup/return, and branch-routing transitions from ordinary users;
- state an `Atomic` instance only when its actual iris-lean obligation is
  proved, normally for an operation whose one step reaches a terminal
  expression;
- never combine several store-mutating Wasm instructions merely to obtain a
  convenient atomic rule;
- make transition traces label instruction steps versus administrative steps so
  granularity regressions are visible.

If proof ergonomics suffer from many administrative laters, add derived rules
over a proved finite administrative closure. Do not change `PrimStep` or silently
declare the closure atomic.

### Naming memories and resources in ghost state

**Decision:** assign every instantiated resource a stable typed identity that
does not depend on its current array position or size. Ghost locations combine
that identity with a resource-local address.

Use types along these lines:

```lean
structure ModuleInstanceId where ...
structure MemoryId where
  module : ModuleInstanceId
  index : Nat

inductive WasmLoc
  | memoryByte : MemoryId → UInt64 → WasmLoc
  | global : GlobalId → WasmLoc
  | tableSlot : TableId → UInt64 → WasmLoc
  | gcField : ObjectId → FieldId → WasmLoc
```

The exact ghost construction may use separate authoritative maps per resource
kind instead of one sum-typed `WasmLoc`; stable identities and laws matter more
than the encoding.

Required behavior:

- `memory.grow` preserves the `MemoryId`, retains ownership/facts for old
  addresses, and extends the authoritative map with freshly initialized bytes;
- store extension allocates fresh resource IDs and never renumbers existing
  resources;
- multi-memory rules mention the selected `MemoryId`, so framing another memory
  is automatic;
- table growth and GC allocation follow the same stable-name discipline;
- a persistent registry in the state interpretation relates runtime indices to
  stable ghost IDs;
- the physical `Store` contents and authoritative ghost maps agree.

Index-only names such as `(memoryIndex, offset)` are acceptable only while a
single module instance exists and resources are never inserted/reordered.
Choosing `(ModuleInstanceId, index, offset)` now avoids a later breaking change.

### Old/new observation relation

**Decision:** compatibility compares WebAssembly-observable outcomes, not
internal `ThreadState`, control frames, fuel counts, or representation-specific
allocation details.

Define:

```lean
inductive ObservableResult
  | done : List WasmVal → StoreObservation → ObservableResult
  | trapped : NormalizedTrap → StoreObservation → ObservableResult

structure StoreObservation where
  memories : ...
  globals : ...
  tables : ...
  segmentStatus : ...
  host : HostObservation
  -- Add GC/reference observations through a renaming relation.
```

The default full observation includes:

- returned values or normalized trap category;
- pages and bytes of every memory;
- mutable globals and tables;
- data/element segment drop state where future execution can observe it;
- Wasm-observable exception and GC heap behavior;
- the explicitly selected host-state/trace observation.

Comparison details:

- compare float and SIMD values by bits, not display text;
- compare trap categories structurally; diagnostic wording is not semantic;
- compare invalidity only at the driver classification/error-category level;
- ignore fuel and counts of administrative transitions;
- for GC/reference identities, use a bijection/renaming relation preserving
  reachable object structure rather than requiring equal internal addresses;
- allow a narrower parameterized store projection for focused tests, but require
  the full observation at milestone and cutover gates.

Compatibility is bidirectional for terminating outcomes: an old success/trap
has a matching new success/trap and conversely. It deliberately says nothing
about termination when one side consumes all supplied fuel; differential tests
must increase fuel or report the case as inconclusive rather than a semantic
divergence.

### Total-correctness theorem migration

**Decision:** preserve the distinction in theorem names and in the migration
ledger.

- Current `PartiallyMeets` theorems map naturally to iris-lean WP/adequacy
  results, subject to matching postconditions.
- A current `TerminatesWith` theorem must not be replaced by only an Iris WP
  theorem under the same name, because that would silently discard termination.
- When only partial correctness is ported, give the replacement an explicitly
  partial/safety-oriented name and record the lost termination obligation in the
  ledger.
- Concrete `native_decide` or runner completion checks are regression evidence,
  not a general termination proof.

Keep a dedicated termination ledger with:

| Old theorem | Partial replacement | Termination status | Intended measure |
|---|---|---|---|
| TBD | TBD | Preserved / deferred / not applicable | loop variant or recursion measure |

Termination need not wait for iris-lean support. For valuable cases, define a
small-step `TerminatesWith` predicate—existence of a finite multistep trace to
`.done`—and prove it directly using a well-founded loop/recursion measure. Then
combine it with Iris partial correctness to recover total correctness. During
this migration it is acceptable to defer those proofs, but never acceptable to
erase their intent or describe partial correctness as termination.
