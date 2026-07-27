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

## Implementation status

The current migration branch has crossed the executable cutover boundary:

- `Wasm.SmallStep.Step` is the relational semantics and `stepChecked?` is its
  proved sound, complete, deterministic executable presentation.
- The CLI runner and testsuite execute only the small-step iterator. Neither
  production entry point calls the legacy `run` function or evaluates a
  second in-process semantics. Differential testing is isolated in the
  dedicated V8/miscast harness.
- The full recorded testsuite baseline is
  `64740 pass / 0 fail / 357 skip / 18 cascade / 27 decode errors /
  0 interpreter errors / 0 out of fuel`; `testsuite_report.txt` has SHA-256
  `67ff73b1d4094747ae1df8a0220e50373779b2614774c5fb9bf39c186ac1bc07`.
  Static branch-depth,
  passive bulk-memory, and table/element validation converted a cumulative
  2,346 formerly unrejected `assert_invalid` cases into passes without losing
  any prior pass.
- Indirect-call null-table traps now retain and render the selected element
  index rather than collapsing it to a generic string. This closes the
  isolated `bulk.wast` mismatch; the focused bulk corpus is 187/187 green.
- Instantiated memories and tables now carry stable script-wide identities in
  the testsuite driver. Imported resources hydrate from and commit to shared
  registries instead of remaining disconnected snapshots. Memory growth caps
  belong to the instantiated memory, so an importer cannot widen an
  exporter's maximum; `memory_grow*`, `imports*`, and the focused load corpus
  are green. Active-segment and start-function instantiation traps commit
  earlier shared effects. Functions now also carry stable identities:
  cross-instance table entries invoke the exporting instance rather than
  being reinterpreted in the caller's local function index space. The focused
  linking corpus is 123/123 green.
- Passive GC element-segment constant expressions are evaluated once at
  instantiation and cached as runtime values. Nested `array.new_elem` and
  `array.init_elem` therefore retain heap references instead of replacing
  them with null, while dropped segments behave as empty for zero-length
  operations. Array destination bounds now report structural array traps
  before source data/element bounds. The focused `array.wast`,
  `array_init_data.wast`, and `array_init_elem.wast` executed cases are all
  green.
- `any.convert_extern` and `extern.convert_any` now have explicit syntax,
  validation, and semantics. `AnyRef.host` retains internalized host identity;
  managed references externalize through a deterministic reserved handle
  range. All executed `extern.wast` cases pass, and the related reference
  test/cast clusters no longer fail.
- iris-lean `ToVal`, `PrimStep`, `Language`, `StateInterp`, primitive lifting,
  and adequacy are implemented over the small-step relation. The authoritative
  GenHeap state is tied to physical memory bytes. Instantiated globals use a
  separately named authoritative ghost map (avoiding the ambiguity of two
  simultaneous `genHeapGS` instances). Instantiated tables likewise use a
  stable-index authoritative map; `table.get` preserves complete-table
  ownership and `table.set` updates physical and ghost contents together.
  A table-aware state-sensitive adequacy theorem and closed set/get proof
  recover the reached physical table. Primitive `table.size`, successful
  32/64-bit `table.grow` (including deterministic capacity failure), and
  `table.fill` rules now cover immutable width/capacity metadata and lockstep
  physical/ghost growth and filling. Closed grow/fill/read and table64
  success-then-failure proofs recover the exact enlarged tables. Same-table
  `table.copy` now has an authoritative overlap-safe rule and a closed
  regression that proves source snapshot semantics. Distinct-table copy has a
  separate rule and closed proof that update-framing preserves the physical
  source while replacing only the destination. `global.get` has a physical-state
  lifting rule plus a concrete end-to-end adequacy witness. Immutable runtime
  module ownership now ties direct-call function lookup to the physical
  `MachineStore`; call entry and caller resumption have primitive rules and a
  closed end-to-end adequacy witness.
- Instantiated element segments now have typed authoritative ownership threaded
  through `StateInterp` and every adequacy allocator. `table.init` reads both
  its live segment and destination table through physical agreement;
  `elem.drop` updates physical and ghost segment status together. A closed
  initialize-then-drop proof recovers both the reached table and dropped
  segment.
- A state-sensitive strong-adequacy bridge now preserves the reached
  `StateInterp` instead of discarding it like iris-lean's value-only
  convenience wrapper. WP posts can combine returned byte/global ownership
  with the final physical `MachineStore`; the manual word roundtrip uses this
  bridge to prove the actual final `Mem.read32`.
- Handwritten byte/word roundtrip, fill, aligned and overlapping copy, swap,
  passive initialization/drop, reverse, a three-word partition kernel, and a
  compare-and-branch merge of two singleton runs have executable and
  relational checks plus Iris WP contracts. The word roundtrip, mutating
  two-word swap, three-word partition, singleton merge, fill, aligned copy, overlapping copy, and passive
  initialization/drop additionally have end-to-end iris-lean adequacy theorems
  with allocated physical/ghost agreement. The overlapping copy owns the
  aliased source and destination as one eight-byte region and proves
  memmove-style snapshot behavior.
- Host failures and known GC failures now use distinct structural
  `TrapReason` constructors; the generic `.legacy` trap escape hatch has been
  removed. Host traps retain committed host-store effects, and a focused GC
  regression checks that a null i31 access becomes `.nullI31Reference`.

Open cutover rows:

- `Project/SwapElements/SwapSepLogic.lean` no longer imports or elaborates the
  legacy custom `wp_wasm` layer. The repository-level
  `CodeLib.SepLogic.WasmWP` fixpoint and its `CodeLib.SepLogic.Adequacy`
  bridge are now deleted after a reference audit confirmed that no live module
  imported them; iris-lean's WP and `SmallStepAdequacy` are the sole live
  separation-logic execution path. The obsolete duplicate proof block in
  `SwapSepLogic` is commented migration history pending final source deletion; the separately
  maintained public `TerminatesWith` theorem in `SwapElements/Spec.lean`
  remains until that API is moved to finite small-step traces. The `CodeLib`
  umbrella likewise no longer exports the legacy layer; new clients see the
  small-step Iris API.
  `RustStd.UInt` is now a contextual iris-lean chunk API, and every U64
  arithmetic, bitwise, shift, division, remainder, and not chunk has been
  ported to the primitive small-step lifting rules. The unused fuel-bounded
  array callee/ABI tactics were removed; `FatPtrAt` plus the authoritative
  small-step loader are the live slice interface. Among CodeLib and programs,
  only the terminating `SwapElements` public spec now directly imports
  `Interpreter.Wasm.Wp.*`.
- Authoritative `i64.load`, `i64.store`, global ownership, `global.get`,
  direct-call entry, and caller resumption are complete. Migrating the
  `SwapElements` callers next requires composing the generated bounds-check
  path with the newly available block, branch, comparison, bitwise, shift,
  and arithmetic lifting rules. The exact 28-step successful `func1` prefix
  and its physical-runtime-checked `call 2` entry are proved. The generated
  `func3` spill helper is now also closed through iris-lean adequacy from its
  concrete initial module memory, with all eight affected bytes owned by the
  physical/ghost agreement. The generated `func2` proof is call-stack
  polymorphic, and the complete successful
  `func1 → func2 → func1 return` path is now composed over authoritative
  runtime, global, scratch-word, and array-word ownership. `func1` itself is
  now call-stack polymorphic, and the generated `func0` forwarding wrapper is
  composed through its concrete direct-call frame with both contextual and
  top-level Iris WPs. `func3` likewise has a contextual pre-return rule ready
  for composition in the export. The full successful `func4` export now
  composes stack-pointer lowering, the `func3` spill call, physical reloads,
  the nested `func0 → func1 → func2` swap, stack-pointer restoration, and
  terminal return. A concrete two-element array closes this WP through
  authoritative heap/global/runtime adequacy, covering five disjoint physical
  words and both nested direct-call frames. Equal indices now have a separate
  one-cell lifting rule: the exact 16-instruction exchange leaf sequentially
  reuses one exclusive eight-byte owner, rather than assuming two owners for
  aliased bytes. This rule is composed through `func1` and `func0`, and a
  concrete same-index execution has closed authoritative heap/global/runtime
  adequacy proving the array word is unchanged. The alias rule is now also
  composed through the exported `func4`; its closed footprint owns exactly
  scratch, two spill words, and one array word. Both the distinct-index and
  equal-index export examples have executable finite-trace
  `SmallStep.TerminatesWith` witnesses in addition to their Iris
  `PartiallyMeets` proofs. State-sensitive adequacy now additionally proves
  that the equal-index export's reached physical memory still contains the
  original array word. A framed `u64` agreement rule preserves state and word
  ownership across observations, so the distinct-index export example proves
  both reached physical reads (`0 ↦ 22`, `8 ↦ 11`) in one postcondition. The
  distinct-index export now also has a fully parameterized non-aliasing
  `PartiallyMeets` contract: for arbitrary validated pointer, length, indices,
  initial words, heap/global ghost maps, and physical store agreement, it
  proves that the reached physical store contains the two exchanged words at
  the computed dynamic addresses. The equal-index path has the corresponding
  fully parameterized one-owner contract and proves that the reached physical
  word is unchanged. `Project.SwapElements.SmallStepSpec` now registers both
  cases as the public small-step/Iris specification surface. The legacy
  total-correctness spec remains imported by the opt-level-3 equivalence proof
  until that proof is recast over finite traces. Out-of-bounds paths remain.
  Element segments, exceptions, and GC registries need analogous authoritative
  treatment as their proof rules are ported; bulk-table rules still need to be
  derived from the table registry.
- The remaining interpreter example/spec files retain legacy theorem
  statements. Their intent must be ported or recorded as termination-deferred.
  `ClzPopcnt.lean`, `MultiValue.lean`, `MemFill.lean`, `MemCopy.lean`,
  `MemReplace.lean`, `MemGrow.lean`, `MemDataSection.lean`,
  `MemNarrowI32.lean`, `MemI64.lean`, `SegmentOffsetExpr.lean`,
  `GlobalInitExpr.lean`, `GlobalCounter.lean`, `SelectAbs.lean`,
  `SelectMin.lean`, `SumI64.lean`, `IsEven.lean`, `TrapDivZero.lean`, and
  `TrapUnreachable.lean`, `RefIsNull.lean`, `EarlyBr.lean`,
  `EarlyReturn.lean`, `IfAbs.lean`, `DecoderImport.lean`,
  `DecoderImportedGlobal.lean`, `EarlyBrInvalid.lean`, `FloatOps.lean`,
  `HostDispatch.lean`, `CallIndirect.lean`, `TableDispatch.lean`,
  `Switch.lean`, `InfiniteLoop.lean`, `CallIndirectSubtype.lean`,
  `RefCastFuncType.lean`, `Counter.lean`, and the shared `Harness.lean` are fully cut over:
  none imports the custom WP or calls `runValues`. Successful public specs are small-step
  `TerminatesWith` theorems with matching `PartiallyMeets` results; trapping
  examples instead state exact structured terminal outcomes and relational
  reachability. All 41 example files are now cut over from the legacy proof
  API. `Factorial.lean`, `Gcd.lean`, and `SimpleLoop.lean` prove decreasing
  loops with explicit relational traces; `EvenOddRec.lean` proves mutual
  recursion contextually over arbitrary saved call stacks.
  `MultiValue` additionally covers multi-result block exit and call-frame
  return ordering. The bulk-memory pair specifies successful physical-memory
  effects, overlapping `memmove` behavior, and atomic out-of-bounds traps.
  The reusable `SmallStep.TrapsWith` predicate and its runner soundness bridge
  now give those terminal trap specifications the same fuel-free public shape
  as `TerminatesWith`, while keeping traps distinct from successful values.
  `TrapDivZero` and `TrapUnreachable` use this public contract and preserve the
  reached physical store in their postconditions. Bulk fill/copy, SIMD memory,
  table get/fill, indirect and tail-indirect calls, and null-reference examples
  now use it as well. `TrapsWith` supports trace prefixing and postcondition
  framing, and semantic determinism proves that one initial configuration
  cannot both terminate normally and trap. The remaining structured example
  families—memory64/indexed memory, data/element segment reuse, numeric and
  float conversion, GC, exceptions, host dispatch, and concrete-reference
  casts—also expose `TrapsWith`; host abort additionally proves its committed
  physical-memory effect. A reason-projection bridge supports host-parametric
  stores that intentionally lack decidable whole-store equality.
  `MemReplace` preserves the stronger symbolic theorem over an arbitrary
  sufficiently large store, including an explicit instruction-granular
  relational trace. `MemGrow` frames an existing word across successful
  growth and proves exact whole-store preservation on failure. The data
  section examples cover literal initialization plus deferred const-expression
  data and element offsets, observed through a load and an indirect call.
  `GlobalInitExpr` covers extended arithmetic plus leaf and arithmetic GC
  allocator initializers as observed through small-step `struct.get`.
  `MemNarrowI32` and `MemI64` bundle total and partial contracts for all 17
  full-width/narrow load and partial-width store cases.
  `GlobalCounter` does the same for mutable global state and threads three
  concrete calls through the physical store.
- The handwritten Iris memory ladder now closes physical-store
  `PartiallyMeets` results for a word roundtrip, a two-word in-place swap, and
  a three-word reverse, a three-word partition kernel, a four-byte `memory.fill`, and an aligned four-byte
  `memory.copy`, and an overlapping four-byte `memory.copy`. The reverse
  theorem proves both endpoint exchange and preservation of the framed middle
  word. The partition theorem preserves all three words, places pivot `22`
  between the lower and upper partitions, and proves both unsigned partition
  inequalities from the reached physical store. The merge kernel executes a
  Wasm unsigned comparison and structured `if`; regressions exercise both
  branches, while Iris adequacy proves the swapping case is sorted in physical
  memory. Fill proves its target update while framing a disjoint word; aligned
  copy proves preservation of its source and the destination update; and
  overlapping copy proves snapshot/memmove semantics under one exclusive
  eight-byte owner. Passive `memory.init` and `data.drop` are tied to a new
  authoritative data-segment registry: initialization reads the owned live
  segment and dropping changes both the physical status and ghost fragment to
  `none`. A reusable framed `u32` agreement lemma preserves the authoritative
  state interpretation while physical facts are extracted for several
  disjoint words; this is the 32-bit counterpart of the existing framed `u64`
  rule used by `swap_elements`.
- Validation closure remains substantial. The new checked stepper currently
  has 229 explicit `InternalError` exits, while the retained big-step
  implementation still has 309 `.Invalid` sites. The current `ValidConfig`
  wrapper proves semantic error-freedom, but decode/type validation has not
  yet been connected to a concrete machine well-formedness predicate. Static
  branch-depth validation now rejects out-of-scope `br`, `br_if`, `br_table`,
  reference-branch, and GC cast-branch labels before execution.
  Host exceptions are no longer diagnostic exits: direct and indirect calls,
  their tail-call forms, and `call_ref`/`return_call_ref` all enter the
  ordinary structured exception-unwinding machine. Focused regressions cover
  every imported call form. Nested propagation markers are also handled by an
  explicit administrative unwind: the current exception continues outward
  and supersedes the stale marker instead of producing an internal error.
  Passive bulk-memory validation now also rejects missing memories and invalid
  data-segment indices for `memory.init`, invalid `data.drop` indices, and the
  straight-line wasm32/memory64 operand-type matrix. Successful instruction
  checks expose the exact index bounds used by instantiation, which proves one
  runtime segment-status entry per declared data segment. The focused
  `memory_init`, `memory_init0`, and `memory_init64` corpus now has 493 passes
  with zero skips or failures.
  Passive data segments are now correctly accepted without a linear memory,
  as required by GC `array.new_data`/`array.init_data`; only active segments
  set the decoder's `dataWithoutMemory` validation marker. Constant-expression
  validation now recognizes floating-point and SIMD constants, and
  `array.init_data` validation checks destination mutability and numeric/vector
  storage explicitly. Precise concrete-reference signatures now cover GC
  struct and array construction, access, mutation, and copy; declaration
  checks retain `ref.func` precision; and reference branches refine nullable
  operands on their non-null paths. A forced-validation run of the focused
  array corpus improved from 38 direct passes and 16 rejected normal modules
  to 244 passes with no rejected normal modules. Focused `call_ref` and
  `return_call_ref` runs likewise have 86 passes with no rejection, while the
  reference-branch corpus has 84 passes and only its 12 intentional harness
  skips. Global production validation remains gated on the remaining
  proposal-specific false rejections.
  Table/element-segment validation rejects missing tables and invalid element
  indices for `table.init`, rejects invalid `elem.drop` indices, and selects
  the destination operand type from the wasm32/table64 declaration. The
  focused `table_init` and `table_init64` corpus now has 1,658 passes with
  zero skips or failures. Instantiation proves that active element writes
  preserve the table registry length and that every validated table or
  element-segment index resolves in the initial store.
  Ordinary table get/set/size/grow/fill/copy now validate every selected
  table and derive element/address types from its declaration, including
  table64 and mixed-width copy. The focused mixed `table.copy` corpus now has
  3,460 passes with zero skips or failures; declaration-check proofs expose
  every table lookup required by execution.
  Bulk fill/copy validation rejects a missing selected memory and enforces
  the exact wasm32/memory64 destination, source, and length types for default
  and indexed memories. The focused `memory_fill` corpus now has 216 passes,
  and `memory_copy` has 8,943 passes, both with zero skips or failures.
  Scalar integer and floating load/store validation now covers the complete
  value-type matrix, selected-memory existence, memory64 addresses, and
  indexed-memory wrappers. It converted 120 additional invalid assertions
  across the full suite. The remaining scalar load/store skips are nested
  under structured control and require the structured validator track rather
  than additional instruction signatures.
  `memory.size` and `memory.grow` now validate selected-memory existence and
  use the selected declaration’s wasm32/memory64 type for results and deltas,
  including indexed-memory wrappers. The focused `memory_size` corpus has
  95 passes with no skips or failures.
  Function-body `global.get`/`global.set` references now reject out-of-range
  indices and expose the concrete declaration lookup required by execution.
  `GlobalDecl` and the WAT decoder now retain declared type and mutability;
  immutable writes and folded initializer type mismatches are rejected while
  hand-built legacy modules remain source compatible. Successful
  `global.set` checks expose both the declaration and its mutability proof.
  Decoded initializer programs are retained separately from runtime-deferred
  expressions. Validation enforces the supported constant-expression
  instruction set, exact stack result, declaration order, and immutable
  source-global requirement without changing instantiation behavior. The
  focused global corpus now has 109 passes and 12 skips; its remaining
  validation cases are nested function-body stack-flow and one reference-type
  precision gap.
  Direct calls and `ref.func` now reject unknown function indices using the
  unified imported-plus-local function lookup. Indirect, tail-indirect,
  `call_ref`, and tail-reference calls validate their type indices; indirect
  calls additionally validate the selected table and use its table32/table64
  selector type. Straight-line direct, indirect, and reference-call stack
  signatures are checked. The focused call corpus has 417 passes, zero
  failures, and 60 skips.
  The operand checker now traverses blocks, loops, and both `if` arms instead
  of abandoning validation at the first structured instruction. It tracks
  branch transfers, exact label signatures, branch-only exits, and the
  WebAssembly unreachable-stack polymorphism rule. Structured instructions
  retain their declared parameter/result types in addition to cached arities;
  legacy handwritten constructors remain source-compatible through defaulted
  metadata. Core integer, float, conversion, and reinterpretation instructions
  have complete scalar signatures. The focused `block`, `if`, `loop`,
  `unreached-invalid`, and `return` suites now report 790 passes with no skips
  or failures.
  Exception validation checks `throw` tag indices and argument signatures,
  the `throw_ref` operand, exact `try_table` parameter/result types, and every
  catch clause against its tag arguments and selected outer label signature.
  `throw.wast` and `throw_ref.wast` now have no validation skips;
  `try_table.wast` has one remaining validation skip owned by concrete
  reference nullability.
  SIMD validation now covers every grouped unary, binary, ternary, test,
  shift, splat, extract, replace, shuffle, relaxed, and memory constructor.
  Scalar lane types and memory32/memory64 address widths are checked, as are
  lane and shuffle immediates. The focused SIMD corpus has 25,989 passes,
  zero failures, and one remaining skip; that skip is an unknown-local case
  shared with the local-index validation track rather than a SIMD signature
  gap.
  Function-local references are validated recursively against the combined
  parameter/local namespace, including code following `unreachable`. The
  focused `local_get`, `local_set`, and SIMD-load corpora now have no skips or
  failures; successful checks expose the concrete local-index bound.
  Module-interface validation checks function/global/table/memory export
  indices, name uniqueness across all four export kinds, and the start
  function's unified index and empty parameter/result signature. The focused
  export and start corpora now have 132 passes, zero failures, and two
  non-validation skips.
  Data and element declarations now retain folded offset types, explicit
  empty/deferred offset-expression presence, and declared element types.
  Validation rejects decoder-synthesized “data without memory”, unknown
  active memory/table targets, wrong memory64/table64 offset types,
  non-constant or mistyped offsets, mutable/unknown globals, unknown element
  functions, and active table/segment type mismatches. Successful active
  checks prove the selected resource exists. This closes all previously
  unrejected `data.wast` and `elem.wast` assertions and adds 51 full-suite
  passes without changing any execution failure.
  Direct, indirect, and reference tail calls now consume their complete
  operand signatures, require their result signature to agree with the
  enclosing function, and enter the unreachable terminal typing state. All
  direct-tail invalid assertions and all but one indirect-tail assertion are
  closed; the remaining reference-tail cases require precise reference
  subtyping rather than the validator's current coarse reference classes.
  Memory declaration-limit validation still requires an AST/decoder repair:
  `MemDecl` stores limits as `UInt32`, erasing source overflow before
  validation. The former “active data without a declared memory” information
  loss is closed by the explicit `dataWithoutMemory` decoder marker.
  Testsuite driver limitations account for the five baseline
  `interpreter_error` rows (`extern.wast` reference arguments and
  `instance.wast` named module instances); they are not small-step execution
  fallbacks.
- `Interpreter/Wasm/SmallStepCoverage.md` records the constructor-family and
  runtime-error ledger. `stepPlainChecked?` now enumerates every
  `Instruction` constructor explicitly: there is no generic unsupported
  fallback, and adding new syntax causes an exhaustiveness error until its
  behavior is classified. `memOp` is explicitly owned by the checked indexed
  memory wrapper.
- Quicksort and mergesort still need complete executable, oracle, mutation, and
  Iris proof coverage.
- The legacy big-step implementation remains for old theorem statements and
  focused source-level comparison lemmas until those proof and example
  ledgers are closed; it is no longer on the runner or testsuite execution
  path.

Latest gates after the precise-reference validation slice:

- a temporary full validation gate improved from `64240` passes, `451`
  validation cascades, and `94` decode errors to `64514` passes, `212`
  cascades, and `58` decode errors; it was removed after measurement because
  the remaining normal-module rejections are not production-safe;
- regenerating the production testsuite report with pinned
  `wasm-tools 1.251.0` produces `64739` passes, zero failures, `358` skips,
  `18` unavailable-module rows, `27` decode-error rows, and no interpreter
  errors or out-of-fuel results (SHA-256
  `a7f64212824ec3dcf3611fe0af8c3df7b6ea6749aa90a3c4f6a4b5359b0c8b38`);
- the pinned differential mutation corpus reports `AGREE=70`,
  `FINDINGS=0`, `SOUNDNESS=0`, and `VALUE=0`; the focused 50-case recgroup
  rerun also reports `AGREE=50` with no findings.

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
| Core stepping | `execOne`/`exec` | `Step`/`step?` | correspondence and package builds | In progress | Small-step covers the testsuite; old definitions remain only for proof migration and focused comparisons |
| Runner | `run`/`runTail` | fuel iterator | full baseline and differential canaries | Complete | CLI and testsuite are small-step-only; external V8 differential remains green |
| Control flow | current WP tactics | Iris rules | control examples | Not started | |
| Linear memory | `Mem`, memory arms | small-step memory | byte/word/fill/copy/swap/reverse ladder | In progress | byte, u32, and u64 Iris ownership rules implemented |
| Iris integration | `CodeLib.SepLogic` | iris-lean adapter | memory/global adequacy proofs | In progress | Physical byte and global agreement implemented |
| Existing examples | `Interpreter/Wasm/Examples` | ported corpus | package build | Complete | All 41 files are fully cut over; the shared harness executes only `initConfig`/`runSteps`, and no example imports the custom WP layer |
| Downstream proofs | `CodeLib`, `programs/lean` | new API | package build | In progress | Generated `func2`/`func3` leaves, the successful `func1 → func2` call/return path, and the reusable `u64::abs_diff` body are ported to Iris small-step WP; Iris adequacy lowers generically to relational `PartiallyMeets`. Every `Project.RustU64` public spec now uses this path, including guarded division/remainder; `TotalVariation` and other outer callers remain |

The companion inline-operator corpus in `Project.RustU64Tests` is fully cut
over: all 22 public specs use closed small-step Iris adequacy, including the
four guarded div/rem and four masked-shift compositions.

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

`CodeLib.Equivalence` now also provides the fuel-free
`Wasm.SmallStep.ObservationallyEquivOn` relation directly over initialized
`Config`s. It distinguishes `.done values` from `.trapped reason`, so
structural traps are observable and are not conflated with divergence. Its
outcome-uniqueness and common success/trap rules are proved from deterministic
terminal `Steps`; no theorem in this new layer mentions legacy `run`. Program
equivalence files should move to this relation as each side acquires a
finite-trace total-correctness theorem.

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

### Downstream proof cutover ledger

- `Project.RustU64.Spec` and `Project.RustU64Tests.Spec`: all public operator
  specifications use small-step `PartiallyMeets` and iris-lean WP.
- `Project.TotalVariation.Spec`: both generated calls reuse the contextual
  Iris `abs_diff` body rule with authoritative scratch memory, globals, and
  runtime-module ownership.
- `Project.RustArray.Spec` and `Project.RustArrayTests.Spec`: every internal and
  exported specification uses small-step `PartiallyMeets` and iris-lean WP.
  Export wrappers allocate authoritative ownership for the physical
  `(dataPtr, len)` words through `fatPtrHeap`; `wp_loadFatPtr` then performs the
  two `i32.load`s and preserves the generated call structure. Neither file
  imports or mentions the legacy interpreter or custom WP.
- `Project.NumIntegerOpt3.Spec`: the complete optimized Stein GCD body now has
  a small-step `PartiallyMeets` proof. Its subtract-and-halve loop uses Iris
  Löb induction over nonzero odd operands and a preserved mathematical GCD;
  both equality exits share a proved recombination tail. Total correctness is
  also complete in the small-step semantics: generated setup, odd-part
  normalization, both decreasing loop arms, both equality exits, and final
  recombination have explicit `SmallStep.Steps` traces, composed by strong
  induction on `x.toNat + y.toNat`. The final result theorem combines this
  finite termination proof with Iris partial correctness. This total
  small-step theorem is now the registered public `@[spec_of]/@[proves]`
  contract for the exported `num_integer_opt3::gcd_u64`. The former legacy
  theorem remains referenced only by the old `ObservationallyEquiv` API;
  migrating that API is the remaining optimized-GCD equivalence cutover.
- `Project.NumInteger.Spec`: the memory-backed opt0 implementation now has an
  authoritative 64-byte frame model spanning the caller and callee frames,
  with proved physical-memory agreement, bounds, typed ownership
  decomposition, and a reusable spill-prologue rule. Both generated zero
  branches have complete iris-lean WP proofs through the nested blocks,
  result store/load, and return. They are combined into a mathematical-GCD
  rule and a closed `SmallStep.PartiallyMeets` theorem over a concrete
  `Config`. The nonzero normalization prefix is also complete: the shared
  trailing-zero count and both operand counts are stored and reloaded from
  their exact scratch offsets, and both frame operands are replaced by their
  odd parts before entering the generated loop. The loop's equality guard and
  recombination exit now have compositional iris-lean WP rules: the guard reads
  both authoritative operand slots, the tail shifts by the saved shared count,
  updates the result slot, and exposes the generated `br 2` to the enclosing
  control-frame proof. Both arm-specific odd-part normalization tails are also
  proved over their physical operand and scratch words (`fp+28` for the left
  arm and `fp+32` for the right arm), including their generated `br 0`/`br 1`
  exits. Both complete mutating arms now also perform their frame-backed
  subtraction before invoking those normalization tails, preserving the
  untouched operand and all framed resources. The generated unsigned
  comparison now dispatches through the actual second-block frame: its taken
  edge exits into the left-decreasing continuation, while its fallthrough
  executes the right-decreasing body; both finish at real loop-frame
  back-edges. Equality dispatch is likewise connected to its concrete first
  block: equal operands reach recombination and `br 2`, while unequal operands
  enter the second block. A composed loop-body rule now hides both
  administrative block frames and exposes exactly the final exit and two
  back-edges. The complete loop rule is parameterized over locals 6–9 rather
  than assuming their first-iteration zero values: each arm overwrites only
  its generated temporaries and carries the other scratch locals through the
  back-edge. The enclosing Iris Löb invariant is now proved: both real
  back-edges preserve nonzeroness, oddness, and the mathematical GCD via the
  Stein-step lemmas, while equality proves recombination and hands `br 2` to
  the caller. The boxed recursive hypothesis is threaded explicitly through
  the compositional control rule, so no spatial resource is duplicated.
  Loop entry is connected to the generated `.loop` instruction, and the full
  nonzero core now composes physical scratch-memory normalization, the loop,
  and the original-input recombination identity into one Iris rule. Its
  `br 2` exit is now proved against the concrete three-frame control stack:
  it targets the generated outer block, executes the actual result-slot load
  epilogue, and returns the mathematical GCD. This is composed with the
  nonzero core while existentially retaining the loop-mutated operand and
  scratch ownership. The initial nested guards and spill prefix are now also
  connected: the nonzero path traverses the three generated blocks, retains
  the real outer control frame, executes the complete core, and returns.
  Authoritative-frame adequacy yields a closed `SmallStep.PartiallyMeets`
  theorem for nonzero inputs; combined with the earlier zero theorem, opt0
  `func1` now has one small-step partial-correctness theorem for all operands.
  The zero and nonzero paths also now have contextual pre-return rules. These
  are composed through the actual direct-call frame in `func0`: its prologue
  allocates and fills the caller frame, `func1` returns into the suspended
  caller, and the epilogue restores the stack pointer and returns the GCD.
  The resulting `func0_smallStep_wp` retains the complete physical frame under
  existential ownership. Canonical memory/global agreement now connects that
  rule to a closed `SmallStep.PartiallyMeets` theorem for `func0`. The generated
  `func2` export wrapper is also composed through its real call frame and has
  both an Iris WP rule and closed operational partial correctness from the
  canonical module store. That theorem is now the registered public
  `@[spec_of]/@[proves]` contract for `num_integer::gcd_u64`. The former total
  big-step theorem is explicitly named `gcd_u64_legacy_correct` and remains
  only behind the legacy cross-optimization equivalence API. Finite-trace
  opt0 termination and migration of that equivalence API remain.
- The small-step Iris lifting layer now includes authoritative `global.set`.
  A ghost/physical agreement lemma updates the instantiated global array and
  ghost map together; `StateInterp` preserves that invariant, and the primitive
  WP rule consumes `globalPointsTo index oldValue` and returns ownership of the
  new value. Opt0 `func0` exercises the rule in both directions for its stack
  pointer (`1048576 → 1048560 → 1048576`).
- `Project.FloatTrunc.Spec`: both generated conversion functions and the
  exported agreement check have authoritative small-step Iris proofs. The
  `naive_trunc` proof covers its NaN, positive saturation, negative saturation,
  and ordinary conversion paths while preserving the scratch word and stack
  pointer global; contextual body rules compose both calls in `check`. The
  legacy theorems remain only to preserve the public `TerminatesWith` contract
  until finite-trace total correctness is connected to that API.
- `CodeLib.RustStd.U64.AbsDiff` is now small-step-only. Its unreferenced custom
  `wp` body theorem and all legacy WP imports were removed after the
  contextual iris-lean body rule and closed `SmallStep.PartiallyMeets`
  adequacy theorem were verified as the stronger live API.
- Symbolic memory-loop migration now has typed whole-region ownership on both
  word widths. `arrayAt` supplies append/split and indexed get/set laws for
  u32 copy loops; the new `array64At` supplies the corresponding u64 laws for
  fill loops. These assertions are built from the authoritative byte
  `pointsTo` resources consumed by the small-step load/store rules, so a loop
  invariant can split a completed prefix from its remaining suffix and
  reassemble an updated region without referring to the legacy interpreter.
  `SmallStep.wp_loop_löb` now packages the guarded iris-lean Löb hypothesis,
  invariant resource, and initial administrative `.loop` transition, leaving
  concrete proofs to establish the body exit/back-edge cases.
  The family-indexed `wp_loop_löb_family` variant additionally allows locals
  and ownership to change at each back-edge while retaining the fixed
  operational control frame. Typed prefix/head/suffix split laws now expose
  exactly one next u32/u64 cell, and `array64At_fill_next` returns a separating
  continuation that reassembles the u64 region with its filled prefix extended
  by one element. `fillWords_storeIteration_wp` now connects that spatial
  update to the actual seven-instruction Wasm body
  (`local.get`/shift/add/`i64.store`), including all non-wrapping byte-address
  obligations and preservation of an arbitrary framed Iris resource.
  The u32 copy side now has the analogous two-region transition:
  `arrayAt_copy_next` focuses disjoint source/destination cells and returns a
  continuation preserving the source while extending the copied destination
  prefix. `copyWords_loadStoreIteration_wp` connects that ownership update to
  the generated dual address calculation, `i32.load`, and `i32.store`, again
  framing an arbitrary resource.
  The u64 fill loop is now migrated completely. Its nested block guard, taken
  `br_if`, false-path `br 1`, authoritative store, local increment, real
  outer-block-to-loop back-edge, and final administrative loop exit compose
  under a Löb invariant indexed by the current word and remaining suffix.
  `fillWords_smallStep_wp` is universal in `n` and the original region
  contents. The unreferenced legacy `wp_loop_cons` theorem and all old WP
  imports were removed from `MemFillLoop`.
  The u32 copy loop is likewise migrated completely.
  `copyWords_smallStep_wp` covers initialization, nested blocks, its guard,
  the authoritative source load and destination store, increment, real
  back-edge, and terminal exit under a family-indexed Löb invariant. It is
  universal in the source words and preserves arbitrary framed resources.
  The unreferenced legacy copy theorem and all old WP imports were removed
  from `MemCopyLoop`.
- The `swap_elements` element-address vocabulary is now isolated in
  `Project.SwapElements.Address`, independent of either execution semantics.
  The authoritative distinct-address and aliasing contracts remain in
  `SmallStepSpec`; the legacy total-correctness file and opt-level equivalence
  consume the neutral address layer only where their still-deferred
  finite-trace migration requires it.
  A first authoritative opt-level comparison now lives in
  `Project.SwapElementsOpt3.SmallStepEquivalence`. It runs the real opt0
  exported call chain and the real opt3 inlined export from the same concrete
  two-word store, proves finite relational termination for both, and derives
  `SmallStep.ObservationallyEquivOn` for the caller-visible array while
  excluding opt0's private scratch traffic. The reusable
  `runSteps_checked_terminates` bridge keeps the executable fuel inside the
  proof and supports state-sensitive Boolean checks of the reached store.
  The opt3 side now also has a universal authoritative Iris rule and physical
  adequacy theorem. `opt3_func0_distinct_smallStep_wp` executes both generated
  `geU` guards, both address calculations, both `i64.load`s, both
  `i64.store`s, and the return; its store-level companion proves the two
  reached physical words are exchanged for arbitrary owned stores. This added
  the previously missing primitive `wp_geU` rule proved directly from
  `SmallStep.Step.geU`.
  `opt3_func0_terminates` separately constructs the complete symbolic finite
  trace from relational `Step` constructors. Combining it with adequacy gives
  `opt3_func0_distinct_store_terminatesWith`, a fuel-free universal total
  contract whose postcondition reads the swapped words from the reached
  physical memory. No legacy interpreter theorem is used on the opt3 side.
- `Project.FloatReinterpret.Spec`: both pure reinterpret leaves now have
  authoritative small-step Iris rules and closed `PartiallyMeets` theorems.
  Their generated bit-manipulation callers for `f32.abs` and `f32.copysign`
  are composed through the real saved call frames and likewise have closed
  operational partial-correctness proofs. The frame-backed `f32.abs`
  implementation now owns its concrete shadow-stack word and stack-pointer
  global authoritatively, and its generated wrapper is composed through the
  actual call frame; both have closed small-step partial-correctness theorems.
  This migration also added the previously missing primitive Iris lifting
  rules for `i32.or`, `f32.load`, `f32.store`, `f64.load`, and `f64.store`;
  both store rules update physical memory and authoritative ghost bytes
  together. The frame-backed `f64.abs` implementation now also has a closed
  authoritative proof, and its promote/call/demote wrapper is composed through
  the actual saved call frame. The frame-backed `f32.copysign` implementation
  and its generated wrapper are now proved in the same style. All internal
  functions in this module therefore have small-step proofs. The two exported
  comparison functions use a proved combined authoritative heap: their outer
  result word is at `1048572`, while calls made under the lowered stack pointer
  use an inner `f64` scratch range at `1048552–1048559` (whose upper four bytes
  are also the `f32` scratch word). Physical agreement, bounds, and typed
  ownership decomposition are complete. Lowered-stack contextual rules now
  compose `func0 → func1`, `func2 → func3`, and `func7 → func8` while framing
  the other export resources. The overlapping inner `u64` ownership now has
  proved split/merge rules for its two `u32` halves, and the bitwise `func9`
  path is call-stack polymorphic. For `check_abs`, the shared result-load,
  local-update, stack-pointer restoration, and return epilogue is proved, as
  are both generated block exits (`0` via outer fallthrough and `1` via
  `br 1`). Both comparisons are now connected to those exits. The complete
  `check_abs` body covers stack-pointer lowering/restoration, both nested
  blocks, both failure points, the successful `br 1`, and its result
  epilogue. `check_copysign` is likewise complete through its frame-backed and
  bit-manipulation calls and both administrative exit paths. Authoritative
  heap/global/runtime adequacy gives closed `SmallStep.PartiallyMeets`
  theorems for both exports.
- `Project.FloatRound.Spec`: migration has started with a three-word
  authoritative footprint covering the deepest callee scratch word, the
  naive-round frame result, and the exported result. Physical agreement,
  bounds, global agreement, and typed ownership decomposition are proved. The
  optimized `f32.nearest` frame and wrapper have contextual small-step Iris
  rules. A shared deep-frame rule now proves the generated `f32.trunc`,
  `f32.ceil`, and `f32.floor` bodies at their concrete nested-frame address.
  The four-block naive-round control flow is now complete as compositional
  Iris rules: the positive-half branch executes the generated ceil call and
  `br 2`, the negative-half branch executes the floor continuation, and the
  neutral branch stores the truncation result and exits through `br 1`.
  `func0` composes its stack-pointer prologue, truncation call, fraction
  calculation, all four administrative frames, result epilogue, and return in
  one call-stack-polymorphic rule. The exported comparison now composes that
  arbitrary naive result with the optimized wrapper through both real call
  frames, proves both boolean exits, restores the stack-pointer global, and
  returns. Authoritative heap/global/runtime adequacy gives a closed
  `SmallStep.PartiallyMeets` theorem for `check_round`.
