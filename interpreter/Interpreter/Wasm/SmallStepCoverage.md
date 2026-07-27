# Small-step constructor coverage

This ledger records the executable and relational coverage of the instruction
syntax during the Iris migration. It is checked primarily by Lean rather than
by keeping a second handwritten list:

- `stepPlainChecked?` matches every `Instruction` constructor explicitly.
  There is no catch-all instruction arm. Adding a constructor to
  `Instruction` therefore makes `Interpreter.Wasm.SmallStep` fail to compile
  until its executable behavior is classified.
- `Step` has a constructor corresponding to every successful or trapping
  result of the executable stepper, and `stepChecked?_sound` /
  `stepChecked?_complete` are exhaustive proofs.
- `execGcOp` and the `.gc` arm cover every `GcOp`. Its `.Invalid` results are
  validation/invariant failures, while `.Trap` results become structural
  `TrapReason`s where a category is known.
- `TrapReason.message` is exhaustive, so adding a semantic trap requires an
  explicit driver-facing representation.

## Instruction-family matrix

| Family | Executable `stepChecked?` | Relational `Step` | Regression evidence | Iris rules |
|---|---|---|---|---|
| Completion and traps | Complete | Complete | terminal/trap examples and full testsuite | value, finish, return |
| Blocks, loops, branches, calls, exceptions | Complete | Complete | examples, testsuite, differential corpus | core block/branch/direct-call/return rules |
| Locals, globals, integer numeric operations | Complete | Complete | examples and testsuite | representative arithmetic, locals, authoritative globals |
| Scalar floating point and conversions | Complete; explicitly enumerated | Complete | float examples and testsuite | Pending derived family rules |
| Linear memory, bulk memory, memory64, multi-memory | Complete | Complete | testsuite plus byte/u32/u64/fill/copy/memory.init/data.drop/swap/reverse examples; closed physical-store adequacy | authoritative byte/u32/u64/load/store/fill/copy/passive-segment rules |
| Tables, indirect/tail/reference calls | Complete | Complete | testsuite, V8 differential corpus, physical/ghost table set/get adequacy | authoritative stable-index table registry and get/set rules; bulk-table derived rules pending |
| SIMD and SIMD memory variants | Complete | Complete | SIMD testsuite files and focused examples | Pending derived family rules |
| GC proposal operations | Complete through `execGcOp` | Complete | GC examples and testsuite | Pending authoritative GC registry rules |
| Host calls | Complete for the deterministic `HostFn` interface, including structured exceptions through every call form | Complete | host return/trap/throw/effect examples | direct-call runtime ownership |
| Indexed-memory wrapper (`memOp`) | Complete in `stepChecked?`; explicitly rejected by the private plain stepper | Complete via `Step.memOp` | indexed-memory examples and testsuite | Pending indexed-memory derived rules |

## Runtime error ledger

There are currently 229 explicit `InternalError` exits in the checked
stepper. None denotes an unimplemented instruction constructor. They fall into
these migration obligations:

- operand-stack shape/type conditions that module validation should establish;
- local/global/function/table/memory/segment/tag indices and branch depths that
  validation or instantiation should establish;
- unresolved host imports that instantiation should reject;
- private wrapper invariants, such as preventing nested `memOp`;
- `.Invalid` results from `execGcOp`, which validation should make unreachable.

Validation is not yet enabled for every normal module because the checker still
has proposal-specific false rejections. The latest focused closure accepts
passive data segments without linear memory, recognizes float/SIMD constant
expressions, and validates `array.init_data` mutability and storage constraints.
Precise concrete-reference signatures cover GC struct/array creation, access,
mutation, and copy; function-reference declarations keep their concrete type;
and nullable reference branches refine the non-null path. Under a temporary
forced-validation gate, the array corpus improved from 38 direct passes with 16
rejected normal modules to 244 passes with no rejected normal modules. The full
forced-validation corpus improved from 64,240 passes with 451 validation
cascades and 94 decode errors to 64,514 passes with 212 cascades and 58 decode
errors. The temporary gate was removed after measurement; the authoritative
production run has 64,739 passes, no failures, 358 skips, 18 unavailable-module
rows, 27 decode-error rows, and no interpreter errors or out-of-fuel results.

Host-thrown exceptions are not part of this ledger: direct, indirect, tail,
`call_ref`, and `return_call_ref` execution all create the same throwing
control frames used by Wasm `throw`. Each executable branch has a matching
`Step` constructor and correspondence case, and `HostDispatch.lean` exercises
all imported call forms through terminal structured exceptions. A nested
propagation marker is likewise an explicit administrative unwind rather than
an error: the current exception discards the stale marker and continues.

The present `ValidConfig` uses semantic error-freedom (`Config.Safe`) to expose
the total `step?` API. The remaining validation milestone is to define a
concrete machine well-formedness predicate, prove decode/validate/instantiate
establish it, prove every `Step` preserves it, and derive `Config.Safe`.
Out-of-scope branch labels are already rejected statically for ordinary,
table, reference, and GC cast branches.

The handwritten memory ladder now includes a three-word partition kernel after
swap and reverse. Its executable and relational checks preserve all three
words, place the pivot at its final address, and establish the two unsigned
partition inequalities. The matching Iris rule retains exclusive ownership of
all three words, and state-sensitive adequacy extracts the same facts from the
reached physical memory.

The next merge rung uses two singleton sorted runs and performs its comparison
inside Wasm. Focused executable checks cover both the keeping and swapping
branches and compare each result with the retained big-step oracle. A generic
`wp_iff` lifting rule exposes structured conditional execution to iris-lean;
the merge WP and state-sensitive adequacy theorem use it to prove exclusive
word ownership and ascending order in the reached physical memory.

The `CodeLib.RustStd.U64.AbsDiff` leaf no longer imports or exposes the legacy
custom WP. Its reusable body theorem is the contextual iris-lean rule over the
small-step language, closed by an adequacy theorem from concrete physical
memory and globals. This is the first completed removal from the remaining
CodeLib custom-WP dependency graph rather than a compatibility duplication.

The unimported `CodeLib.SepLogic.WasmWP` least-fixpoint implementation and its
legacy `CodeLib.SepLogic.Adequacy` bridge have been deleted. A repository-wide
reference audit leaves iris-lean's WP over `Wasm.Step`, together with
`SmallStepAdequacy`, as the only live separation-logic execution semantics.

The shared `RustStd.UInt` chunk abstraction is also small-step-only now.
`BinChunk` and `UnChunk` are contextual iris-lean entailments, and all U64
arithmetic/bitwise/shift/division/remainder/not instances use the primitive
lifting rules. The old fuel-bounded chunk equivalences, checked-body helpers,
and array callee bridges were removed after downstream Rust array specs were
confirmed to use their authoritative small-step proofs.

Passive bulk-memory validation is now closed for straight-line functions:
`memory.init` checks that its selected memory and data segment exist and uses
the correct wasm32/memory64 operand signature; `data.drop` checks its segment
index without requiring a memory. The checker exposes lemmas turning successful
instruction validation into the exact index bounds used by instantiation, and
instantiation proves one runtime status entry per declared data segment. The
focused `memory_init`, `memory_init0`, and `memory_init64` tests now report
493 passes with no skips or failures.

Table/element-segment validation is likewise closed for straight-line
`table.init` and `elem.drop`: table and element indices are checked before
instantiation, and the destination operand is `i32` or `i64` according to the
selected table declaration. Successful checks expose table/segment bounds;
instantiation proves that active-element writes preserve the table registry
length and that validated indices resolve in the initial store. The focused
`table_init` and `table_init64` tests report 1,658 passes with no skips or
failures.

Ordinary table get/set/size/grow/fill/copy validates selected table indices
and derives element/address types from the declarations, including table64
and mixed-width copy. Successful checks expose all table lookups needed by
execution. The focused mixed `table.copy` corpus reports 3,460 passes with
no skips or failures.

Bulk fill/copy validation now checks that the selected memory exists and
models the exact wasm32/memory64 destination, source, and length operand
types for both default and indexed memories. Successful checks expose the
selected declaration lookup needed by the executable machine. The focused
`memory_fill` corpus reports 216 passes and `memory_copy` reports 8,943
passes, both with no skips or failures.

Indirect-call null-table traps retain the selected element index in
`TrapReason.uninitializedElement`. Driver rendering therefore preserves
precise messages such as `uninitialized element 2` while remaining compatible
with generic expected-message substrings. The focused `bulk`/`bulk64` corpus
now reports 187 passes with no failures or skips.

Instantiated stores now retain stable memory and table identities. The
testsuite driver maintains script-wide shared registries, hydrates an
instance before each action, and commits its post-store by identity, so
memory/table imports alias their exporter instead of copying a permanently
detached snapshot. Memory growth limits are stored with the instantiated
memory resource: an importing declaration cannot widen the exporter's
maximum. The focused `memory_grow`/`memory_grow64` corpus is 100/100, the
`imports` family is 212/212 for executed cases, and the focused `load1`
corpus is 54/54. A small-step regression theorem in `Examples/MemGrow.lean`
checks the exporter-limit rule directly. Table limits remain declaration
owned until their resource-owned representation lands together with matching
authoritative ghost ownership.

Module definitions and generative module instances are now represented by the
testsuite driver instead of being skipped. Globals and exception tags join
memories and tables in carrying stable instantiated identities: repeated
imports of one export alias, while two instantiations of the same definition
remain distinct. Canonical global/tag lookup is part of `Step`, and the
existing Iris global rules explicitly cover canonical (currently index-zero)
ownership until the authoritative registry is generalized to aliased local
indices. The focused `instance.wast` corpus is 20/20 for executed commands,
with no failures, decode errors, or interpreter errors.

Active-segment and start-function `assert_uninstantiable` commands now execute
the instantiation path and commit effects which precede a trap. Foreign
function references stored in shared tables carry stable script-wide
identities and dispatch through `HostEnv.foreignFuncs`; local references are
decoded only when the receiving instance owns the same function identity.
The complete focused `linking`/`simd_linking` corpus is 123/123 green.

GC composite fields and function signatures retain concrete named heap types
through decoding and resolve them after the complete module type table is
known. Iso-recursive equivalence therefore distinguishes references to
different recursion groups while preserving true structural equivalence.
The focused `type-subtyping.wast` corpus is 122/122 for executed assertions.

Passive GC element-segment item expressions are evaluated exactly once during
instantiation and cached as runtime values. `array.new_elem` and
`array.init_elem` consume those cached references, including nested array
objects, while the authoritative legacy segment state continues to govern
live/dropped behavior. Dropped segments act as empty sources, so zero-length
initialization succeeds. Destination array bounds are classified before
source data/element bounds. The executed cases in `array.wast`,
`array_init_data.wast`, and `array_init_elem.wast` are 130/130.

The GC instruction layer now implements `any.convert_extern` and
`extern.convert_any`. Internalized host references use the explicit
`AnyRef.host` shape; managed references externalize into a deterministic
reserved handle range above unsigned 64-bit host IDs and round-trip back to
their original i31/struct/array identity. The testsuite harness parses
`ref.host` values as host references rather than i31 values. All 14 executed
`extern.wast` assertions pass.

Scalar integer and floating memory access now has a complete reusable
signature matrix for wasm32 and memory64 addressing. Default and indexed
loads/stores also validate that their selected memory exists, with lemmas
exposing the declaration lookup required by execution. This converts 120
additional full-suite invalid assertions into passes. The remaining scalar
load/store invalid cases occur inside structured control constructs, where
the deliberately partial straight-line checker currently stops.

Memory size/growth validation checks that the default or indexed memory
exists and derives both the `memory.size` result and `memory.grow` delta/result
types from its wasm32/memory64 declaration. Successful checks expose the
selected declaration lookup. The focused `memory_size` corpus now reports
95 passes with no skips or failures.

Function-body global references now check `global.get` and `global.set`
indices before instantiation, with successful-check lemmas exposing the
declaration used by the runtime store. `GlobalDecl` and decoded imports/locals
now retain source mutability and declared value type. Validation rejects
immutable writes and folded initializer type mismatches; successful
`global.set` checks expose a mutability proof. Decoded initializer programs
are retained separately from runtime-deferred expressions, allowing
validation of the supported constant-expression instruction set, exact stack
result, declaration order, and immutable source-global requirement. The
focused global corpus now reports 109 passes and 12 skips.

Function-reference validation uses the same imported-plus-local function
lookup as execution. Direct calls and `ref.func` reject unknown functions;
indirect and reference calls reject unknown type indices; indirect calls also
reject unknown tables and derive the selector width from table32/table64.
Straight-line direct, indirect, and reference calls validate their complete
operand/result signatures. Successful-check lemmas expose the function,
type, and table lookups needed by execution. The focused direct, indirect,
tail, reference, and `ref.func` corpus reports 417 passes, no failures, and
60 skips.

The operand checker recursively validates `block`, `loop`, and both `if`
arms, carrying exact label signatures and branch transfers through nested
constructs.
It implements unreachable-stack polymorphism without forgetting concrete
values pushed after an unreachable point, resets polymorphism at nested
control-frame entry, and preserves `br_if` label arguments on fallthrough.
Structured instructions retain exact declared parameter/result types alongside
cached arities; defaulted metadata keeps existing handwritten modules
source-compatible. Core scalar integer, float, conversion, and reinterpretation
instructions have complete stack signatures. The focused `block`, `if`,
`loop`, `unreached-invalid`, and `return` suites report 790 passes with no
skips or failures. Polymorphic `ref.as_non_null` and `ref.is_null` preserve or
check their operand type without bailing out of whole-function validation.

SIMD validation covers all grouped vector constructors: constants, unary and
binary operations, bitselect/FMA/dot-add, tests, shifts, splats, lane
extract/replace, shuffle, and every SIMD memory form. Lane scalar types are
derived from `Simd.Shape`; memory signatures use the selected memory32 or
memory64 address type. Extract/replace/load/store lane indices and shuffle
indices are checked before execution. The focused SIMD corpus reports 25,989
passes, no failures, and one unknown-local skip owned by the local-index
validation track.

Local references are checked against `params.length + locals.length` for every
nested instruction, including unreachable code. A successful check proves the
index bound used by local execution. The focused `local_get`, `local_set`, and
SIMD-load corpora now report no skips or failures.

Module-interface validation checks every function, global, table, and memory
export index before instantiation and requires export names to be unique
across kinds. Start functions must resolve in the unified imported/local
function space and have no parameters or results; a successful start check
exposes that signature. The focused export/start corpus reports 132 passes,
no failures, and two harness-owned skips.

Data and element declarations retain source offset types and whether an
explicit deferred offset expression was present, including an empty invalid
expression. Element declarations also retain their source reference type.
Validation rejects decoder-synthesized data memories, missing active
memory/table targets, memory64/table64 offset mismatches, invalid constant
expressions and globals, unknown element functions, and active
table/segment-type mismatches. Successful active checks expose the selected
memory or table lookup. All `data.wast` and `elem.wast` invalid assertions are
now rejected.

Direct, indirect, and reference tail calls are terminal cases in the
recursive operand checker. They consume the callee parameters (plus selector
or reference), require callee and enclosing-function results to agree, and
then switch to unreachable stack polymorphism. The focused tail-call corpus
reports 168 passes, no failures, and nine reference/subtyping-owned skips.

Exception validation resolves `throw` tags and checks their complete operand
signatures, requires an exception reference for `throw_ref`, and retains exact
`try_table` parameter/result types. Catch clauses are checked against the
selected tag arguments (plus `exnref` for reference catches) and the exact
outer label signature. The focused `throw` and `throw_ref` suites report 28
passes with no skips or failures. `try_table` converts eight additional
invalid assertions into passes; its remaining validation skip requires
concrete reference nullability that the current `ValueType` representation
does not retain.

`ValueType.ref` now retains exact heap type and nullability metadata, including
resolved named and concrete types. `br_on_null` and `br_on_non_null` validate
their exact label-stack and fallthrough effects; the focused suites are closed
at 10 and 12 passes respectively. `call_ref`, `return_call_ref`, `ref.eq`, and
`ref.func` are also closed, including declaration-site validation.

Iso-recursive type equivalence compares concrete references by recursion-group
position rather than raw type-table index. Nominal indirect calls and
`ref.test` use that relation, closing the newly runnable type-equivalence and
recursive-subtyping cases.

GC array-copy validation requires a mutable destination, compatible precise
storage types, and the complete five-operand stack signature.

One decoder information-loss issue remains a prerequisite for complete memory
declaration validation: `MemDecl` narrows parsed limits to `UInt32`, erasing
source overflow. Missing-memory data assertions are now preserved explicitly
by `Module.dataWithoutMemory` and rejected.

## Acceptance evidence

The constructor-level compile check is supplemented by:

- `stepChecked?_sound`, `stepChecked?_complete`, and `step_deterministic`;
- terminal irreducibility and runtime/store framing theorems;
- the complete committed WebAssembly testsuite report;
- the external V8/miscast differential corpus;
- executable, relational, and Iris memory examples in
  `Interpreter/Wasm/Examples/SmallStep.lean`.
- the fully migrated `ClzPopcnt.lean`, `MultiValue.lean`, `MemFill.lean`,
  `MemCopy.lean`, `MemReplace.lean`, and `GlobalCounter.lean` examples, whose
  public total- and partial-correctness specifications use only the small-step
  API. The bulk-memory examples also check physical post-state,
  overlapping-copy behavior, and atomic traps; `MemReplace` proves a symbolic
  relational trace for arbitrary memory satisfying its bounds precondition;
  `GlobalCounter` proves the analogous symbolic mutable-global trace and a
  three-call physical-state regression.
- the fully migrated `MemGrow.lean`, which proves successful page growth
  preserves existing bytes and failed growth preserves the whole machine
  store.
- the fully migrated `MemDataSection.lean` and `SegmentOffsetExpr.lean`,
  covering literal data initialization and deferred const-expression
  data/element placement as observed by small-step loads and indirect calls.
- the fully migrated `GlobalInitExpr.lean`, covering extended arithmetic and
  GC allocator global initializers observed through small-step global/GC
  execution.
- the fully migrated `MemNarrowI32.lean` and `MemI64.lean`, with bundled
  total and partial contracts for 17 full-width/narrow loads and
  partial-width store roundtrips.
- the fully migrated `SelectAbs.lean`, `SelectMin.lean`, `SumI64.lean`, and
  `IsEven.lean`, whose symbolic results are justified by explicit relational
  instruction traces rather than unfolding the checked executable stepper.
- the fully migrated `TrapDivZero.lean` and `TrapUnreachable.lean`, covering
  normal arithmetic completion and structured terminal trap reachability.
- the fully migrated `RefIsNull.lean`, whose AST proof is a symbolic
  relational trace and whose WAT decoder checks execute only the small-step
  runner, including constant-global initialization.
- the fully migrated `EarlyBr.lean`, `EarlyReturn.lean`, and `IfAbs.lean`,
  covering function-label branches, returns through nested control frames,
  conditional selection, and explicit administrative frame exit.
- the fully migrated `DecoderImport.lean` and
  `DecoderImportedGlobal.lean`, which run decoded host calls and imported-
  global index offsets through the small-step runner, plus
  `EarlyBrInvalid.lean`, which proves malformed label depth is rejected by
  validation rather than surfaced as runtime invalidity.
- the fully migrated `FloatOps.lean`, covering scalar arithmetic,
  comparisons, conversions, reinterpretation, and a physical `f64`
  store/load roundtrip through `runSteps`.
- the fully migrated `HostDispatch.lean`, whose host-call proof is
  parametric over any `HostEnv` satisfying its contract and whose concrete
  regressions cover return, structured host trap, and physical memory reads.
- the fully migrated `CallIndirect.lean` and `TableDispatch.lean`, exposing
  table lookup, signature agreement, callee entry, call-frame return,
  table inspection, and decoded dispatch through relational or executable
  small-step evidence.
- the fully migrated `Switch.lean`, with symbolic traces for all
  `br_table` targets, and `InfiniteLoop.lean`, whose closed reachable-state
  invariant proves that no finite trace reaches `.done`.
- the fully migrated `CallIndirectSubtype.lean`, with relational structured
  traps for ordinary and tail indirect-call subtype mismatches.
- the shared `Harness.lean` compatibility projections now initialize and run
  only the small-step machine. Its scaled fuel is deliberately an
  over-approximation for old example checks and is never exposed in a spec.
- the fully migrated `Counter.lean`, whose two-step storage host protocol is
  proved parametrically from `HostEnv.Satisfies`; the relational trace
  preserves the physical store and proves the exact updated host state.
- the fully migrated `Factorial.lean`, whose 13-transition nonzero iteration
  and 7-transition exit traces are composed by strong induction to prove a
  fuel-free total-correctness theorem and its partial-correctness companion.
- the fully migrated `Gcd.lean`, whose relational Euclidean iteration is
  composed by strong induction on the second operand and proves both
  fuel-free termination and partial correctness.
- the fully migrated `SimpleLoop.lean`, whose nested-block control trace
  preserves a modular `UInt32` accumulator invariant while strong induction
  on the counter proves termination.
- the fully migrated `EvenOddRec.lean`, whose simultaneous strong induction
  is contextual over arbitrary saved call stacks and explicitly traces
  callee entry, administrative return, caller resumption, and completion.
- `runSteps_finalConfig_of_steps` and `runSteps_eq_success_of_steps`, which
  execute public relational traces without exposing the private checked-step
  implementation.
- `runSteps_values_terminates` and `runSteps_values_partiallyMeets`, which
  turn successful executable value projections into relational contracts
  without requiring equality instances for runtime host functions.
- Iris primitive lifting now includes `i64.const`, add/sub/mul, bitwise
  and/or/xor, left/right unsigned shifts, `i64.lt_u`, and unsigned
  `i32 → i64` extension, plus `i64.eq` and nonzero unsigned division/remainder.
  These rules cover every `Project.RustU64` operator, including successful
  guarded div/rem paths, and are derived directly from the corresponding
  authoritative `Step` constructor.
- Scalar float constants, unary conversions/rounding, binary operations, and
  successful trapping conversions now have generic Iris lifting rules over
  the same public evaluator functions used by `Step`; no parallel float
  semantics is introduced. The `i32.eq` and `i32.xor` primitives are also
  available for generated slice and comparison code.
- Memory-resident Rust slice exports use the authoritative `fatPtrHeap` bridge:
  a physical `FatPtrAt` contract determines the exact eight ghost-owned bytes,
  and `wp_loadFatPtr` derives both `i32.load` transitions before generated
  callees run. The ABI contract explicitly records both allocated bounds and
  wasm32 non-wrapping bounds.
- Authoritative contiguous-word ownership is available for symbolic loops:
  `arrayAt` covers u32 words and `array64At` covers u64 words. Both support
  concatenation splits plus indexed extraction/update and restoration. This
  is the region algebra used to frame untouched suffixes and unrelated memory
  while migrating the universal copy/fill loop proofs to iris-lean.
  `wp_loop_löb` supplies the fixed-state guarded recursive wrapper;
  `wp_loop_löb_family` supports changing locals and ownership at back-edges.
  Prefix/head/suffix focusing and `array64At_fill_next` implement the spatial
  update performed by one symbolic fill iteration. The generated address
  calculation and `i64.store` are connected by
  `fillWords_storeIteration_wp`, which consumes and returns authoritative
  physical-byte ownership while framing an arbitrary resource.
  `arrayAt_copy_next` and `copyWords_loadStoreIteration_wp` provide the
  corresponding disjoint-source/destination transition for the generated
  u32 load/store copy body, returning source ownership unchanged.
  The complete generated u64 fill loop now has a universal iris-lean rule:
  `fillWords_smallStep_wp` covers index initialization, both nested blocks,
  guard selection, store, increment, `br 1` back-edge, and terminal loop exit
  under a changing prefix/suffix Löb invariant. Its legacy interpreter WP
  proof has been removed.
  The complete generated u32 copy loop now has the corresponding universal
  iris-lean rule. `copyWords_smallStep_wp` composes initialization, both
  nested blocks, guard selection, authoritative source load and destination
  store, increment, the real `br 1` back-edge, and terminal loop exit under a
  family-indexed Löb invariant. It preserves the source exactly, replaces the
  destination with the source words, frames arbitrary resources, and no
  longer imports or exposes the legacy interpreter WP proof.
- The generated `swap_elements` examples now take their shared `elemAddr`
  vocabulary from the semantics-neutral `Project.SwapElements.Address`
  module. This prevents address arithmetic used by authoritative Iris
  contracts from depending on the legacy total-correctness proof module.
  The concrete two-element opt0/opt3 comparison is also expressed entirely
  with authoritative finite traces: both generated exports terminate with
  `[]`, both expose `(22, 11)` through the array observation, and
  `SmallStep.ObservationallyEquivOn.of_common_outcome` proves exact terminal
  equivalence without observing private scratch locations.
  The optimized export additionally has a symbolic end-to-end Iris rule and
  store-sensitive adequacy contract. It covers the complete inlined
  bounds-check/load/store implementation and frames globals and unrelated
  memory. Universal total opt-level equivalence is now isolated to the
  separate finite-trace termination proof rather than missing operational or
  physical-memory correctness.
  The opt3 finite trace is now symbolic as well: it is assembled
  instruction-by-instruction from `Step` for arbitrary in-bounds inputs and
  combined with Iris adequacy into a universal `TerminatesWith` theorem.
  Consequently the only remaining universal equivalence obligation is the
  unoptimized generated call-chain trace.
- Passive data segments now have a separately named authoritative ghost map.
  `memory.init` proves that its source bytes come from the instantiated live
  segment, while `data.drop` updates both physical segment status and ghost
  ownership to `none`. A closed state-sensitive example proves the initialized
  physical word and the reached dropped status.
- Instantiated tables now have a separately named authoritative ghost map keyed
  by stable table index. `table.get` returns complete-table ownership unchanged;
  `table.set` updates ghost and physical contents in lockstep. A table-aware
  state-sensitive adequacy entry point and closed set/get regression prove both
  the returned value and reached physical table. Primitive `table.size`,
  32/64-bit `table.grow` success and capacity-failure, and `table.fill` rules
  use persistent runtime metadata where required and update the authoritative
  physical table through growth and filling. Closed grow/fill/read and table64
  success-then-failure regressions prove the resulting three-entry tables and
  the unchanged store on failed growth. Same-table `table.copy` has an
  authoritative rule and a closed overlapping-copy regression that proves the
  source slice is captured before the destination update. Distinct-table copy
  has a framed authoritative rule and closed regression proving the source
  physical table is unchanged while the destination is updated.
- Instantiated element segments now have typed authoritative ghost ownership,
  physical agreement in `StateInterp`, and allocation through the strongest
  adequacy entry point. `table.init` and `elem.drop` have primitive lifting
  rules, plus a closed initialize/drop regression proving the reached table
  contents and dropped physical segment.
- Invalid passive-segment indices, missing memories for `memory.init`, and the
  wasm32/memory64 straight-line operand-type matrix are rejected statically.
  Previously skipped invalid assertions in both `memory_init.wast` variants
  are now accepted as validator passes, while all execution assertions remain
  green.
- Invalid table/element-segment indices and the wasm32/table64
  `table.init` operand-type matrix are rejected statically. All focused
  `table_init` assertions now pass with no remaining skips.
- Ordinary table operations reject missing tables and incorrect
  wasm32/table64 element, index, and mixed-copy operand types.
- Missing memories and mistyped wasm32/memory64 `memory.fill` and
  `memory.copy` operands are rejected statically. All focused fill/copy
  assertions now pass with no remaining skips.
- Straight-line scalar integer/float loads and stores reject missing memories,
  wrong value types, and wrong wasm32/memory64 address types for default and
  indexed memories.
- `memory.size` and `memory.grow` reject missing memories and incorrect
  wasm32/memory64 result or delta types for default and indexed memories.
- Out-of-range function-body `global.get` and `global.set` references are
  rejected before small-step initialization.
- Decoded global mutability and declared types are preserved; immutable
  writes and folded initializer type mismatches are rejected statically.
- Global initializers reject non-constant instructions, empty or multi-value
  results, forward/self references, and reads from mutable globals.
- Direct calls and `ref.func` reject unknown function indices; indirect and
  reference calls reject unknown type indices, and indirect calls reject
  unknown tables while respecting table32/table64 selector widths.
- Blocks, loops, and `if` arms are checked recursively with exact branch-label
  signatures, transfer propagation, and unreachable-stack polymorphism.
- SIMD operations have complete stack signatures, selected-memory validation,
  memory32/memory64 address typing, and lane/shuffle immediate bounds checks.
- Nested `local.get` and `local.set` references must resolve in the function's
  combined parameter/local namespace, even after an unreachable instruction.
- Export indices and cross-kind names are validated, and start functions must
  resolve with the required `[] → []` signature.
- Active data/element targets, offset expressions and types, element function
  references, and table/segment reference-type agreement are validated before
  instantiation.
- Tail calls validate their complete operand signatures and require result
  compatibility with the enclosing function before becoming terminal.
