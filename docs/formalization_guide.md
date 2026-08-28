# Guide to Large-Scale Wasm Formalization in Talos

This guide describes how to organize a large verification effort for a Rust or
Wasm program in Talos. The central idea is to separate discovery, specification,
machine proof, and adequacy so that each fact about the generated code is learned
once, recorded, reviewed, and then reused.

The workflow is deliberately front-loaded. A proof should not begin while the
program, its environment, or its intended contract is still poorly understood.
For a large target, one week spent removing uncertainty before proving can save
several weeks of spec churn later.

This document follows the small-step, iris-lean architecture used on the Iris
migration line. Older files using the legacy big-step WP layer remain useful as
examples of individual simplification lemmas, but they are not the default
architectural template for new large proofs.

## 1. The deliverable

A completed formalization is more than a theorem with no `sorry`. It consists of
five connected artifacts:

1. A reproducible identification of the Wasm program being verified.
2. An evidence-backed description of every relevant function and state resource.
3. Reviewed internal contracts that compose at every call site.
4. Machine proofs of those contracts, including explicit termination or failure
   arguments where the public theorem requires them.
5. An adequacy theorem connecting the internal proof to a fuel-free, domain-level
   public specification.

The public theorem is the final product. Instruction-level facts, loop
invariants, memory ownership, generated locals, compiler stack frames, and fuel
are proof machinery and should normally be hidden from clients.

## 2. Non-negotiable principles

### Understand before specifying; specify before proving

Do not discover the meaning of a function while closing its main theorem. The
discovery pass should explain every relevant branch, call, loop, memory access,
and state mutation. The specification pass should then make that understanding
precise. Only after a call-site audit should the main proof begin.

Small exploratory Lean lemmas are encouraged during discovery. They test whether
an abstraction or invariant matches the actual semantics. They are experiments,
not permission to commit prematurely to a full proof architecture.

### One authoritative semantics and one authoritative contract family

The relational `Wasm.SmallStep.Step` semantics is authoritative. Executable
traces must be justified by the proved executable/relational correspondence; do
not introduce a second, proof-only model of Wasm execution.

Each nontrivial function should likewise have one authoritative contract family.
All call-site rules and convenience theorems should follow from it without
re-analyzing the body. “One” here does not mean forcing genuinely different
behaviors into an unusable theorem. Normal return, structured traps, OOM,
aliasing cases, and partial versus total correctness may require separate views.
They should share a clear semantic core and an explicit derivation structure.

### Assumptions are obligations

It is reasonable to verify only well-formed application inputs. It is not
reasonable to ignore a branch because it appears unreachable. Every restriction
must be:

- present in the formal precondition or derived from it;
- strong enough to prove the excluded path unreachable; and
- visible in the public contract if it is a restriction on callers rather than
  an internal representation fact.

Typical obligations include length bounds, alignment, address no-wrap, memory
bounds, initialized representations, non-aliasing or a specified alias case,
allocator capacity, import behavior, and the shadow-stack invariant.

### Partial correctness is not termination

An ordinary Iris `WP` explains successful executions that reach a result. It does
not by itself prove that a result is reached. A total public specification needs
separate termination evidence: for example a supported total-WP/normalization
bridge, a well-founded relational argument, or a checked finite trace for a
closed case. Never describe a `PartiallyMeets` result as a termination proof.

Fuel may appear inside an executable witness, but never as part of the public
meaning of a function.

### Reuse must cross the call boundary

A helper theorem is reusable only if callers can establish its precondition and
use its postcondition without unfolding its body. A proof that closes in
isolation but cannot be applied at a real call site is not a finished function
contract.

## 3. Freeze the verification target

Before analyzing the code, record exactly what is being verified:

- Rust source revision and compiler/toolchain;
- build profile, target, features, and relevant environment flags;
- SHA-256 of the `.wasm`, printed `.wat`, and emitted `Program.lean`;
- exported entry point and its Wasm function identity;
- expected imports and host implementation;
- intended input domain and observable outcomes; and
- the public theorem in one paragraph of natural language.

Talos-generated `Program.lean` embeds the exact WAT and checks its freshness.
Keep the corresponding artifacts together and re-run emission intentionally
when the binary changes. Function indices alone are not stable identifiers:
record the source/WAT name when available, the generated Lean definition, the
absolute runtime index, whether imports affect that index, and a body hash.

If the binary changes after analysis begins, stop and run an impact audit. At a
minimum, re-check function identities, the call graph, layouts, constants,
control-flow shapes, and every proof lemma that selected a generated subprogram
by position.

### Target-freeze exit criterion

The phase is complete when a reviewer can reproduce the exact generated module
and state, without guessing, which entry point and host semantics the final
theorem concerns.

## 4. Build a program dossier

Keep analysis beside the formalization, for example:

```text
docs/formalization/<target>/
  README.md                 # scope, artifact hashes, public goal
  module.md                 # imports, exports, memories, globals, tables, data
  call-graph.md             # graph, recursive components, indirect calls
  assumptions.md            # trusted inputs and environment assumptions
  spec-matrix.md            # functions × call sites × outcome coverage
  proof-ledger.md           # status, blockers, risks, spec changes
  decisions/                # abstraction and architecture decisions
  functions/
    <stable-function-name>.md
```

For a very large module, create a full inventory first, then write individual
function cards for all reachable nontrivial functions. Tiny forwarding shims can
share a card if their behavior is completely mechanical. The inventory must
still account for every reachable function, import, and indirect-call target.

### 4.1 Module-level inventory

Record:

- exports and their resolved runtime functions;
- imported functions and the exact host contracts assigned to them;
- defined functions and their type signatures;
- memories, tables, globals, data segments, and element segments;
- initial memory/global state relevant to the proof;
- mutable shared resources and their owners;
- start functions and initialization effects;
- possible structured traps and host failures; and
- compiler conventions such as parameter order, shadow-stack globals, frame
  layout, allocator metadata, and return-value areas.

Do not treat the Wasm operand stack as if it used source-language argument
order. Record the exact stack order expected by Talos at call entry and return.

### 4.2 Call graph and proof order

Build a graph containing:

- every direct call edge;
- every import edge;
- every possible indirect-call target, with the table/type justification;
- tail calls and callbacks;
- all call sites for each callee; and
- recursive strongly connected components.

The call graph is also the first proof-dependency graph. Acyclic callees can be
specified and proved bottom-up. A recursive component must be designed as a unit:
its contracts, invariants, and termination measures are mutually dependent.

For each call site, record how arguments and owned resources are prepared, which
facts establish the callee precondition, which result/resources are consumed
after return, and which failure outcomes propagate.

### 4.3 Function-card template

Use the following template for each relevant function.

```markdown
# `<source name>` / `<generated Lean name>`

## Identity and freshness

- Wasm/runtime index:
- Defined-function index:
- Type:
- Body hash:
- Artifact hash/date:
- Analysis status/reviewer:

## Purpose

One sentence at the domain level, followed by a precise low-level summary.

## Inputs

- Operand-stack parameters and exact order:
- Locals initialized from parameters:
- Linear-memory regions read:
- Globals, tables, segments, and host state read:
- Caller/control-stack assumptions:
- Representation and ownership assumptions:

## Outputs and effects

- Returned operand-stack values and order:
- Memory/global/table/host mutations:
- Resources preserved or returned:
- Normal, trap, OOM, and other terminal outcomes:

## Control and data flow

- Meaning of every parameter and local:
- Purpose and invariant of every loop:
- Meaning of each branch condition:
- Reachability condition for each block/early return:
- Address calculations and no-wrap/bounds facts:

## Calls

| Site | Callee | Arguments/resources prepared | Result/resources used |
| --- | --- | --- | --- |

## Pseudocode

Faithful structured pseudocode. Preserve overflow, signedness, aliasing,
allocation, trap, and host behavior that matters to the theorem.

## Complexity

- Source-level time/space model:
- Candidate termination measure:
- Compiled-cost observations, if the project intends to prove them:

## Candidate contract

- Pure semantic relation:
- Representation/ownership precondition:
- Postcondition and frame:
- Failure outcomes:
- Termination claim and measure:

## Proof plan and risks

- Pure lemmas:
- Wasm/WP lemmas:
- Callee contracts:
- Hardest obligation:
- Open questions and evidence needed:
```

### 4.4 Discovery standard

A function is “understood” only when:

- every load and store has a semantic object and an ownership source;
- every local has an identified role or is explicitly irrelevant;
- every branch has a meaning and reachability condition;
- every loop has a candidate invariant and, for total correctness, a variant;
- every call site has a candidate callee contract instantiation;
- arithmetic signedness, width, overflow, and pointer no-wrap are settled;
- aliasing possibilities are classified;
- all terminal outcomes are classified; and
- remaining unknowns are logged rather than hidden in prose.

Concrete runs and `native_decide` checks are useful during this phase. They are
sanity checks, not substitutes for symbolic understanding.

## 5. Design the specification stack

Large proofs are easier to maintain when their specifications form explicit
layers.

### 5.1 Public, domain-level specification

State what a caller actually cares about. Prefer lists, maps, records, streams,
and mathematical relations over byte arrays and compiler locals. Hide fuel,
scratch space, allocator internals, shadow-stack frames, and generated indices
unless they are part of the observable interface.

On the Iris migration line, choose the public operational predicate deliberately:

- `Wasm.SmallStep.TerminatesWith` for successful total correctness;
- `Wasm.SmallStep.PartiallyMeets` for successful partial correctness; and
- `Wasm.SmallStep.TrapsWith` or a host-aware wrapper for a specified trap.

Some legacy files use the older fuel-free `Wasm.TerminatesWith` interface. Do
not copy that execution architecture into a new small-step proof merely because
the theorem statement looks convenient.

List every permitted terminal outcome. For example, an allocator-using program
may return a correct result or reach one distinguished OOM host trap. An
unrelated trap, an internal error, and divergence satisfy neither branch unless
the public contract explicitly says otherwise.

Register exported and internal source links with `@[spec_of ...]`; register the
final proof with `@[proves ...]`. Give each formal spec a docstring with a clear
`Informal spec:` section so the verifier report can present it correctly.

### 5.2 Pure functional model

Define the mathematical operation independently of Wasm execution. Examples
include list merge, vector push, serialization, parser relations, or a state
transition over a domain record.

Prove the difficult mathematical facts here first:

- preservation and permutation;
- sortedness or other inductive invariants;
- bounds and length equations;
- encoding/decoding laws;
- loop-invariant transitions; and
- well-founded decrease.

Keeping these facts outside Iris makes the machine proof shorter and exposes
whether the proposed invariant is mathematically adequate before ownership and
control stacks obscure the issue.

### 5.3 Representation predicates

Connect domain objects to machine state with reusable predicates. Useful
building blocks include byte/word ownership, arrays, slices/fat pointers,
records, stack frames, allocator state, globals, tables, and host-state lenses.

A representation predicate should say:

- which bytes or resources it owns;
- how bytes decode into the abstract value;
- required alignment, bounds, and no-wrap conditions;
- whether the ownership is exclusive, fractional, or persistent;
- which mutations preserve the representation; and
- how it splits, combines, frames, and handles aliasing.

Avoid a single opaque “whole heap” or “whole stack” assertion unless the program
really requires global ownership. Monolithic state makes callees hard to frame
and prevents independent proofs. Prefer small compositional resources, with a
separate invariant only for genuinely shared allocator or runtime metadata.

Before adopting a major abstraction, test it on at least two structurally
different functions and one real call boundary. Record the choice and rejected
alternatives in a short decision note. Generalize into `CodeLib` only after a
second concrete consumer exists.

### 5.4 Canonical internal function contract

The canonical contract should be contextual: it must work with an arbitrary
caller remainder, control/call stack, and framed resources whenever the function
semantics permits that generality. It should describe:

- exact entry locals and operand-stack layout;
- owned and persistent resources;
- pure well-formedness facts;
- return values and state changes;
- resources returned to the caller;
- allowed traps/failures; and
- the continuation after return.

Use Iris `WP` for partial correctness. If total correctness is required and the
total layer is available for the required features, give the corresponding
total contract and a well-founded measure. Otherwise keep termination as a
separate explicit theorem. Do not add a fixed fuel constant to make a symbolic
contract look total.

Convenience call rules may specialize stack order, instantiate frames, or weaken
the postcondition. They must invoke the canonical theorem and must not unfold the
function body again.

## 6. Audit specifications before the main proof

Specification review is a formal phase, not an informal glance. Review each
contract from four directions.

### 6.1 Callee sufficiency

Ask whether the precondition is enough to execute every instruction covered by
the contract and prove the promised postcondition:

- Are all reads owned and in bounds?
- Are all writes exclusively owned?
- Are arithmetic and address calculations non-wrapping where required?
- Are module, function, table, global, segment, and import lookups justified?
- Are all branches, traps, and host outcomes represented?
- Is the termination measure actually decreasing on every recursive/loop edge?

### 6.2 Caller usability

Instantiate the contract at every call site on paper or in a small Lean proof:

- Can the caller establish every precondition from facts it really has?
- Does the callee return the ownership the caller needs?
- Is the postcondition strong enough for the next instruction and eventual
  caller postcondition?
- Does the contract preserve unrelated framed state?
- Do aliases at the site match the ownership shape of the contract?
- Can failures be propagated to the caller's allowed outcomes?

Maintain these results in `spec-matrix.md`. A green callee with a red call site is
not ready for proof.

### 6.3 Semantic fidelity

Try to falsify the specification:

- Is the precondition inconsistent or unnecessarily impossible?
- Is the postcondition vacuous?
- Does it accidentally permit the wrong trap, output, or state mutation?
- Does it omit multiplicity, order, aliasing, overflow, or host effects?
- Does an existential hide the property clients actually need?
- Does the abstraction identify states the code treats differently?
- Would the theorem still hold for an obviously broken implementation?

If the last answer is yes, the spec is probably too weak.

### 6.4 Boundary and adversarial cases

Audit empty and singleton inputs, maximum lengths, zero-sized regions,
pointer/address boundaries, overlapping regions, equal indices, allocation
failure, partial host I/O, early returns, traps, and recursion base cases.

At this point, ask an independent reviewer—or a deliberately adversarial agent—to
find counterexamples and unusable call sites. The reviewer should receive the
binary dossier and specs, not the intended proof, so it is not biased toward the
chosen implementation strategy.

### Specification-freeze exit criterion

The phase is complete when every call site is compatible, every outcome is
classified, the hardest invariant has survived an exploratory proof, and no
reviewer has an unresolved semantic objection. Freeze a reviewed version of the
spec matrix before large proof work begins.

## 7. Plan proofs around risk and dependencies

Create an obligation graph, not a flat to-do list. Typical layers are:

1. Pure definitions and laws.
2. Numeric, encoding, address, and layout lemmas.
3. Representation-predicate laws and primitive load/store rules.
4. Straight-line chunks and branch bodies.
5. Loop invariants and recursive components.
6. Canonical function contracts.
7. Call rules and caller composition.
8. Entry wrapper, host behavior, and failure propagation.
9. Adequacy and the public theorem.

Work bottom-up along dependencies, but test the highest-risk assumptions early.
The hardest loop invariant, aliasing case, indirect call, allocator interaction,
or host boundary should receive a time-boxed proof spike before dozens of easy
lemmas are polished. Early failure is valuable information.

### Suggested Lean file structure

Split by semantic responsibility, not by an arbitrary line limit. A useful
starting point is:

```text
Project/<Target>/
  Program.lean              # generated; never edit by hand
  Spec.lean                 # public domain-level specs, little proof machinery
  Pure.lean                 # mathematical model, relations, invariants
  Layout.lean               # encodings, address arithmetic, representations
  <Component>Proof.lean     # one function family or recursive component
  HostProof.lean            # import contracts and host-state transfer, if needed
  Adequacy.lean             # physical/ghost initialization and recovery
  Proof.lean                # short final bridge and @[proves] declarations
```

Small targets can combine files. Large targets should split further by call-graph
component, not one file per arbitrary proof phase. Avoid circular imports: pure
facts and layouts belong below machine proofs; component proofs belong below
adequacy; the final public proof belongs at the top. Ensure the package umbrella
imports the proof modules, otherwise a successful build of `Spec.lean` alone does
not establish that the advertised proof is part of the project build.

### Loop checklist

For every loop, record:

- a semantic state record rather than an unstructured tuple where practical;
- the invariant over the current machine and abstract state;
- initialization;
- preservation for every branch;
- the exit condition and how it implies the desired postcondition;
- the resources framed through an iteration; and
- for total correctness, a natural or well-founded measure and strict decrease.

### Recursion checklist

For every recursive component, record:

- the mutually assumed contracts;
- the exact smaller argument or well-founded relation;
- preservation of representations across recursive calls;
- base cases, including machine-level early-return behavior; and
- how saved call frames and caller remainders are restored.

## 8. Execute the Lean proof

Use a `sorry`-driven, goal-directed workflow, but keep every `sorry` visible in
the proof ledger. Start with statements and decomposition, inspect the exact Lean
goal, try the smallest relevant rules, and close one semantic step at a time.

For interactive work:

1. Warm the required package build once after a branch or dependency change.
2. Use Lean LSP goal inspection and diagnostics after edits.
3. Try several candidate tactics or local lemmas without repeatedly rebuilding.
4. Search local declarations before inventing a duplicate helper.
5. Run the affected package build only at meaningful integration points.
6. Build `interpreter`, then `codelib`, then `programs/lean` when upstream changes
   require the full dependency chain.

Prefer named generated-body and shape lemmas over repeated deep positional
unfolding. If a proof extracts a block or loop by a numeric list index, prove a
small shape lemma near that extraction so binary drift fails locally and
readably.

Use `native_decide` for closed, decidable facts and executable regression checks.
Do not use it to hide a symbolic theorem, an unreviewed abstraction boundary, or
a missing general lemma.

### When a contract fails during proof

Treat an incorrect contract as a pipeline incident:

1. Stop proving downstream users.
2. Classify the failure: missing assumption, weak postcondition, wrong model,
   omitted outcome, representation problem, or semantics/tooling gap.
3. Check all sibling contracts and call sites for the same error pattern.
4. Update the canonical contract and spec matrix centrally.
5. Re-run the adversarial audit on the changed surface.
6. Only then repair dependent proofs.

Do not patch one call site with an implementation-specific fact merely to move
the same problem into its caller.

## 9. Prove adequacy and the public bridge

The internal WP theorem is not yet the advertised program theorem. The bridge
must account for the exact initial machine and recover facts about the reached
physical state.

An adequacy layer typically proves:

- construction of the initial `SmallStep.Config` for the exported function;
- resolution of the correct module instance, function, memory, and imports;
- agreement between physical memory/state and ghost ownership;
- allocation of the initial representation resources;
- application of the canonical entry-function WP;
- recovery of final physical memory, globals, tables, and host state;
- encoding/decoding between byte-level I/O and domain values;
- conversion to `PartiallyMeets`, `TerminatesWith`, or `TrapsWith`; and
- derivation of the `@[proves ...]` theorem from the entry spec alone.

Keep the mathematical result separate from the machine bridge. For example,
first prove that the machine returns the output of a pure sorting function, then
prove once that this pure output is a sorted permutation.

The public proof should be short enough to audit. Ideally it selects an allowed
operational outcome, invokes the entry adequacy theorem, and discharges the
domain-level property with pure lemmas.

## 10. Validation and completion gates

Before declaring the formalization complete, perform all of the following.

### Logical checks

- No `sorry`, placeholder axiom, or accidental admitted theorem remains.
- Every public spec has a `@[proves ...]` theorem.
- Axiom usage is reviewed for important theorems.
- Partial and total correctness claims are labeled accurately.
- Unreachable paths are ruled out by formal hypotheses and lemmas.
- All allowed and disallowed terminal outcomes are explicit.

### Composition checks

- Every call site uses a callee contract rather than re-analyzing its body.
- Every canonical contract is exercised by at least one real caller or entry
  bridge.
- Recursive components use one coherent family of contracts.
- Framed resources and ownership are returned as promised.
- Alias cases are covered or excluded by an explicit public precondition.

### Reproducibility and execution checks

- Artifact hashes and generated-source freshness match the frozen target.
- All affected packages build in dependency order.
- Closed executable examples cover representative and boundary cases.
- Relational/executable correspondence is used for finite runner witnesses.
- Differential testing against a trusted Wasm engine is run when the target or
  interpreter change makes it relevant.

### Documentation checks

- Function cards and the call graph match the final binary.
- The spec matrix contains no unresolved call site.
- Assumptions are collected in one place and reflected in Lean statements.
- Abstraction decisions and known limitations are documented.
- The proof ledger has no unexplained blocked or deferred obligation.

## 11. Track progress without rewarding churn

Raw theorem count and lines of Lean are poor progress measures. Track semantic
milestones instead. A useful per-function state is:

```text
inventoried
  → understood
  → contract drafted
  → call-site audited
  → contract frozen
  → pure obligations proved
  → partial machine proof proved
  → termination/failure obligations proved
  → integrated at callers
  → adequacy/public bridge proved
  → independently reviewed
```

Also track project-wide:

- reachable functions covered by reviewed contracts;
- call sites successfully instantiated;
- unresolved semantic unknowns;
- open `sorry`s by critical-path depth;
- spec changes after freeze and their blast radius;
- unproved loop/recursion measures;
- uncovered terminal outcomes; and
- stale analysis caused by binary changes.

Opening two lemmas while closing one is progress only when the new lemmas are
strictly clearer obligations on the critical path. A rewrite that merely moves
the difficult proposition behind a new name is not progress.

## 12. Review cadence for long efforts

Use several kinds of review because they find different failures:

- **Discovery review:** Does the dossier accurately explain the binary?
- **Spec review:** Is the theorem meaningful, satisfiable, strong enough, and
  usable at every call site?
- **Invariant review:** Are initialization, preservation, exit, and decrease all
  plausible before the loop proof grows?
- **Adversarial review:** Can an input, alias pattern, trap, or host behavior break
  the claim?
- **Proof review:** Does the Lean proof use only intended assumptions and preserve
  the abstraction boundary?
- **Adequacy review:** Does the final physical state really imply the public
  domain-level result?

Run adversarial review after the first spec draft, after any material spec
change, and before final completion. For especially risky components, ask a
reviewer to pursue a competing invariant or abstraction for a fixed time. A
short failed alternative can expose a hidden commitment in the main plan.

## 13. Common failure modes

- Starting instruction proofs before the public outcome is agreed.
- Treating source-language parameters as the function's only inputs.
- Using function indices as stable identities.
- Ignoring compiler-generated failure paths without a reachability proof.
- Giving a callee exactly the whole current store, making framing impossible.
- Requiring disjoint ownership while a real call site may alias.
- Stating only the happy path for code that can legitimately trap or signal OOM.
- Confusing a WP partial-correctness theorem with termination.
- Putting fuel in a public specification.
- Proving the same function body again at multiple call sites.
- Choosing a loop invariant that states safety but not enough semantic progress
  to derive the exit postcondition.
- Polishing easy leaf lemmas before testing the hardest invariant or bridge.
- Fixing a broken spec locally without auditing its other callers.
- Letting per-function notes drift after recompilation.
- Counting generated lemmas instead of closed semantic milestones.

## 14. Compact phase checklist

### A. Target

- [ ] Binary, WAT, generated Lean, toolchains, and hashes frozen.
- [ ] Entry point, imports, host semantics, inputs, and outcomes identified.
- [ ] Public goal written in natural language.

### B. Discovery

- [ ] Module inventory complete.
- [ ] Direct, indirect, host, and recursive call edges mapped.
- [ ] Relevant function cards complete and fresh.
- [ ] Memory layouts, implicit inputs, traps, and alias cases understood.

### C. Specification

- [ ] Public fuel-free spec written.
- [ ] Pure model and representation predicates selected.
- [ ] Canonical contract family drafted for every relevant function.
- [ ] Every call site passes the usability audit.
- [ ] Termination and failure obligations classified separately.
- [ ] Adversarial review completed and specs frozen.

### D. Proof

- [ ] Highest-risk invariant/bridge tested early.
- [ ] Pure lemmas proved before machine composition where possible.
- [ ] Function bodies proved once and reused through call rules.
- [ ] Loops and recursion have preservation and, when required, decrease proofs.
- [ ] Contract changes propagated through the full spec matrix.

### E. Bridge and completion

- [ ] Initial physical/ghost agreement proved.
- [ ] Entry contract lowered through adequacy.
- [ ] Final physical state decoded into the domain result.
- [ ] `@[proves ...]` theorem follows from the entry spec.
- [ ] No admits; axiom usage and diagnostics reviewed.
- [ ] Affected packages and representative executions pass.
- [ ] Documentation and artifact hashes match the final binary.

The essential discipline is simple: make uncertainty explicit, freeze interfaces
before scaling the proof, and ensure every internal theorem earns its place by
composing into the public result.
