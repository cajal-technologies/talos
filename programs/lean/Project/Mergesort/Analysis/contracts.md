# Principal contract design

This records the frozen Lean declarations and the review evidence behind them.
Two red-team audits found concrete defects; the corrected consequences are
retained below and in [the call-site matrix](call-site-matrix.md).  Each
contract has passed the two-sided audit: its body can establish the post from
the precondition, and every valid call site can establish that precondition
and continue from every postcondition.

## Canonical logical vocabulary

The implementation should have one definition for each of the following.

- `U32Codec`: the four-byte little-endian `WordCodec UInt32`; public
  serialization, array bytes, decode lemmas, and output bytes derive from it.
- `SortedPermutation input output`: sorted nondecreasing output plus
  `List.Perm input output`; no canonical `mergeSort` equality is required by the
  public theorem.
- `ByteSlice ptr bytes`: owned initialized byte range.
- `OwnedRegion ptr size`: an owned range with existential current contents;
  unlike `ByteSlice`, it does not pretend bytes are logically initialized.
- `WordSlice ptr values`: four-aligned owned `UInt32` range, definitionally or
  provably equivalent to the codec bytes.
- `SortBuffers source scratch original scratchValues`: equal-length disjoint
  `WordSlice`s plus address/no-wrap facts.
- `RawVecHeader header capacity ptr` and
  `VecU8 header capacity ptr initialized`: structured header plus a complete
  live block of `capacity` bytes, split into the named initialized prefix and
  an existential spare suffix.
- `LiveBlock ptr layout bytes`: exclusive ownership of every byte in one live
  allocation, with exact size, alignment, and nonnull facts.
- `BumpDecision frontier layout`: exact pure success `(base,end)` versus OOM
  classification for the allocator's checked i32 arithmetic.
- `BumpHeap cursor frontier history`: cursor word, exclusive frontier token,
  metadata authority, and ownership of retired blocks.  It
  does not own bytes of live blocks.  Its authority is coupled to the sparse
  heap-domain invariant in [decision 0002](decisions/0002-allocator-ownership.md).
- `GeometricVecFacts`: the pure capacity/retained-allocation lineage needed to
  show the public input Vec reaches allocator OOM before RawVec overflow.  It
  owns neither the Vec nor heap.
- `StackRegion`, `StackReserve`, `RawExportRegion`, and `ExportFrame`: entry owns
  one raw 288-byte region.  The body splits it into the lower 16-byte reserve
  and upper raw 272-byte region, then initializes the latter into a disjoint
  Vec/chunk/output composition.  No whole-frame predicate overlaps its slots.
- `Streams input output oom`: the logical Universal host view.

`Spec.encodeWord`, `SortProof.wordBytes`, and example-specific serializers must
not remain independent implementations.  The same applies to duplicate
sorted-permutation predicates.

## Terminal algebra

The semantic core uses two outcomes:

```text
Normal returned-values + returned resources
OOM    exact host trap reason + raised host marker
```

Other finite traps are absent from public-path postconditions and must be ruled
out by preconditions.  The current public entry theorem is partial correctness:
it classifies every finite observable terminal execution but does not rule out
divergence.  The exact Iris/adequacy encoding is the subject of
[decision 0001](decisions/0001-terminal-outcomes.md); contracts below are
written independently of that encoding.

## Required WP shape

Every authoritative generated-function theorem is continuation-passing.  In
encoding-independent notation its shape is:

```text
P(args, incoming resources)
  -* (forall normal result/resources,
        Qnormal(args, result, resources) -* WP resumed-caller K)
  -* (forall exact terminal outcome/resources,
        Qterminal(args, outcome, resources) -* WP terminal K)
  -* WP call-instruction-with-caller-continuation K
```

Success-only functions omit the terminal continuation only by proving that no
terminal case is possible under `P`; they do not switch to a closed execution
theorem.  All specifications quantify over the caller's remaining operand
stack, code, control/call frames, masks, and postcondition.  This is what lets a
recursive call or a caller that may later OOM reuse the callee without reopening
its body.

The selected Lean encoding packages the terminal choice behind the shared
`ObservableOutcome` postcondition described in decision 0001.  Its miniature
non-target acceptance spike now passes.  All in-scope generated-function
signatures have now passed the representation and two-sided call-site review.

## Principal contracts in the public proof closure

### Import 0: `stdio.read`

The direct import call has top-first machine operands `[pointer,length]`; the
host reverses them to source arguments `(length,pointer)`.

Pre: `Streams input output oomRaised`, writable `ByteSlice ptr buffer`, requested
length equals `buffer.length`, nonzero/in bounds.  Normal post: count is
`min requested input.length`; that input prefix replaces the buffer prefix,
host input becomes `input.drop count`, output and OOM are unchanged, and the
whole buffer ownership is returned as
`prefix ++ buffer.drop count`.  No trap under the precondition.

### Import 1: `stdio.write`

The direct import likewise has top-first operands `[pointer,length]` and host
arguments `(length,pointer)`.

Pre: `Streams input output oomRaised`, readable `ByteSlice ptr bytes`, requested
length exactly `bytes.length`, and positive requested length.  The last premise
is required to derive a physical in-bounds witness from byte ownership; it is
always four at the sole reachable call.  Normal post: no return values, output becomes
`output ++ bytes`, input and OOM are unchanged, and buffer ownership is
returned unchanged.  No trap under the precondition.

### Import 2 / `func6`: OOM

Pre: `Streams input output oomRaised`, running-instance/runtime identity, and
arbitrary framed program resources.  Sole
post: structural trap `.host OOM.trapMessage` with `oom.raised = true`.  There
is no normal continuation.  `func6` composes this import once and proves its
following `unreachable` is not executed.  The host trap consumes the exclusive
current-running-instance ownership, so the terminal post does not return
`RuntimeContext`.  Memory, globals, and preexisting heap/block resources that
the caller frames explicitly are returned unchanged; the terminal post owns
`Streams input output true`, so only the mutable host OOM field changes.

### `func4`: allocation marker

Pre and normal post are identical; no parameters, results, memory effects, or
terminal alternative.

### `func5`: alloc

Pre: exact Wasm/logical size and alignment equations, a valid nonzero
`AllocLayout`, `BumpHeap`, `Streams input output oomRaised`, and exact runtime
identity.  Reachable alignments are one or four.  If
`BumpDecision frontier layout = success base end`, the signed page-target
theorem bounds any growth request.  Successful growth returns a nonzero fresh
aligned pointer,
`exists id bytes, LiveBlock heapId id ptr layout bytes`, the updated heap,
frontier, and allocation metadata, and unchanged Streams.  No contents are
promised beyond the existential physical bytes.  If the decision is `oom`,
the sole outcome is exact OOM through `func6`; all heap
state is unchanged and the post owns `Streams input output true`.  The
allocator never returns a null failure pointer.  Physical grow failure is a
second route to the same exact pre-commit OOM post, not a null return and not a
call into excluded allocation-error support.

### `func8`: realloc

Pre: complete `LiveBlock heapId oldId oldPtr oldLayout oldBytes`, exact
equations from the Wasm `(oldPtr,oldSize,alignment,newSize)` arguments to the
old/new layouts, valid positive new layout, `BumpHeap`,
`Streams input output oomRaised`, and any separately named initialized prefix
with length at most `min(oldSize,newSize)`.  The only reachable alignment is
one.  Normal post returns a complete new `LiveBlock`, whose first
`min(oldSize,newSize)` bytes equal the old prefix; it transfers the old bytes
to retired-heap ownership, marks the old metadata entry retired, creates the
new live token, updates the cursor/frontier, and preserves Streams.  Arithmetic
failure is exact OOM before that transfer/commit, so the old live block and
heap are preserved and only Streams changes to `input output true`.  The old
physical bytes remain in linear memory after successful retirement.  Physical
grow failure uses the same exact pre-commit OOM continuation as `func5`.

### `func9`: alloc-zeroed

Same allocation and Streams conditions as `func5`, specialized at the sole
reachable alignment four.  Normal post returns a fresh block of exactly
`size` zero bytes as a complete `LiveBlock`, updates heap metadata, and
preserves Streams; arithmetic failure is exact OOM before cursor/frontier
commit and changes only the OOM field.  The syntactic grow-failure edge is
another in-scope route to that exact OOM continuation.  The
`WordSlice` zero-array corollary is derived only
after establishing size `4*n`, alignment four, and exact/nonwrapping i32
arithmetic.

### `func7`: dealloc

Pre: complete `LiveBlock`, exact equations tying `(pointer,size,alignment)` to
its layout, and `BumpHeap`.  Reachable alignments are one or four.  Normal post returns no values, keeps
linear memory and cursor physically unchanged, consumes the live block, and
transfers its bytes/metadata to the single chosen retired-heap owner.  No trap.

### `func0`: RawVec finish-grow

The authoritative precondition is the sole valid reachable use from `func1`:
a disjoint writable 12-byte result place with named incoming bytes,
`(alignment,elementSize)=(1,1)`, selected `newCapacity >= 8`, exact positive
`newSize=newCapacity`, an exact old-capacity live block or the zero-capacity
dangling variant, valid multiplication/layout facts, `BumpHeap`, and
`Streams input output oomRaised`.  Normal success writes exactly
`(tag=0,pointer,newSize)`, returns the complete new live block and preserved
initialized prefix, updates heap metadata, and preserves Streams.  Arithmetic
or signed-end allocation failure is exact OOM: all twelve result bytes, the old
live block, and `BumpHeap` are unchanged, while Streams becomes
`input output true`.  The dossier documents generic layout-error, zero-size,
and returned-null branches, but the main theorem proves each unreachable from
this positive valid-layout precondition.  Thus `func1` may eliminate tag one
without reopening the body.

### `func1`: RawVec reserve

This generated function has only the public byte-Vec call site, so its main
spec is specialized to `(alignment,elementSize) = (1,1)`.  Its precondition
names `rawVecHeader=driverBase`, `length=initialized.length`,
`additional=readCount` and
`readCount=min(256,readCount+remainingAfter.length)`, the reserve-needed guard
`additional > capacity-length`, `StackPointer driverBase`, `VecU8`, the exact
incoming `StackReserve (driverBase-16) shadowBefore`, `BumpHeap`,
`Streams input output oomRaised`, and pure `GeometricVecFacts`.  Those facts
explicitly imply that `length+additional`, doubling, the selected capacity,
and the byte layout do not wrap or exceed the RawVec guard.  Normal post
restores `StackPointer driverBase`, preserves the reserve's first four bytes
and returns its final twelve bytes exactly as
`serialize [0,newPointer,newCapacity]`, preserves initialized bytes, returns a
complete live block, produces
capacity at least `length+additional`, updates the same structured header,
heap, and geometric facts, and preserves Streams.  Alternative outcome is
exact OOM with `StackPointer = driverBase-16`, all sixteen incoming shadow
bytes (including the result subrange), Vec/header/live block, and heap
unchanged, and `Streams input output true`.  Both `func43` edges are proved
false from named precondition fields rather than omitted informally.

### `func10`: read shim

Pre/post are import 0's contract with Wasm argument order translated from
source parameters `(pointer,length)` to the host ABI `(length,pointer)`.  More
precisely, the call to the shim has top-first list `[length,pointer]`, while its
body creates the direct-import list `[pointer,length]`.  This is the only body
analysis for the shim; callers use the shim contract, never the import directly.

### `func11`: write shim

Pre/post are import 1's contract with the same distinct shim-call/direct-import
operand lists.  The sole driver call supplies the positive length four.

### `func2`: recursive merge sort

Pre: numeric arguments equal the explicit `SortBuffers` source/scratch list
lengths; those lengths are equal, both byte ranges are aligned, in bounds,
nonwrapping and disjoint, and the predicate supplies split/recombine laws for
both buffers.  The main statement is continuation-passing, so all framed
runtime/call-stack resources and the caller's continuation are explicit rather
than summarized as “returned.”  Normal post has some `output` such that source
contains `output` and `SortedPermutation input output`; scratch is unchanged
when the length is zero or one and contains `output` when the length is at
least two.

There is no terminal alternative under the layout precondition.  Recursive
calls use this exact contract; loop invariants and implementation details
remain inside its proof.  This piecewise scratch clause is required at both
recursive and driver call sites; requiring both buffers to agree for length
zero or one would be false.

### `func3`: exported driver

Pre: exact initial module/runtime, initial stack/heap/frontier, one raw
288-byte StackRegion below the initial stack pointer, and
`Streams (U32Codec.serialize input) [] false`.
Normal post: no values, restored initial stack pointer, consumed input, OOM
false, output `U32Codec.serialize output` for some
`SortedPermutation input output`, ownership of one raw 288-byte entry stack
region with existential final bytes, and a final `BumpHeap` whose driver
allocations are all retired.  Alternative post is the exact three-way
`DriverOOMState`: reserve OOM has `StackPointer = driverBase-16`, the original
active shadow bytes, previous Vec/live block, current read chunk, exact
consumed-prefix relation, and pre-attempt heap; values OOM has
`StackPointer = driverBase`, completed input Vec, inactive lower reserve and no
values block; scratch OOM has the same plus the decoded live values block and
no scratch block.  Every OOM arm owns all frame pieces and live blocks, has
empty output, exact trap and raised marker, and changes no other host field.
No other finite terminal trap is permitted.  Divergence is not ruled out by
the currently available Iris adequacy theorem.

After the read loop the proof must derive the exact computation
`byteLength & 0x7ffffffc = byteLength`.  This uses both
`GeometricVecFacts.completed_lt_signed` and codec divisibility via
`align4_signedMask_eq`; a larger lineage reaches allocator OOM before read-loop
completion.  The following branch is the ordinary empty/nonempty split, not a
separate error path.

The public partial `PublicEntrySpecification` theorem is a direct conditional
corollary of this contract plus entry initialization; it does not unfold
`func3` again.  The total `MergesortSpec` is a separate future termination
obligation and must not be inferred from partial adequacy.

## Contract inventory and freeze status

The exact statement details are in
[authoritative-signatures.md](authoritative-signatures.md).  “Semantic pass”
means the post matches the inspected binary assuming the named representation
laws; it does not mean a Lean theorem is frozen.

| Item | Body-side review | Call-site review | Remaining blocker | Status |
| --- | --- | --- | --- | --- |
| import 0 | exact Universal read update checked, including replaced prefix, untouched suffix, and direct-import top-first operands `[pointer,length]` | sole valid caller `func10` supplies a positive exact-size owned buffer through the corrected permutation | none | re-frozen statement; authoritative proof compiled |
| import 1 | exact Universal write update checked; false zero-length generalization removed; direct-import top-first operands are `[pointer,length]` | sole valid caller `func11` supplies a positive exact-size readable slice through the corrected permutation | none | re-frozen statement; authoritative proof compiled |
| import 2 | exact trap reason and marker-only host update checked | sole valid caller `func6` supplies Streams and frames all other program resources; terminal ownership correctly omits the consumed current-instance token | none; outcome-valued host lifting and acceptance spike already pass | re-frozen statement; authoritative proof compiled |
| `func0` | positive-layout branch, exact result writes, fresh/realloc effects, and OOM preservation checked | sole `func1` use supplies the split 12-byte result, exact `GrowSourceOwn`, valid positive byte layout, and both continuations | none at statement level; freshness follows from frontier authority plus the sparse heap domain, rather than an extra pure premise | frozen statement, proof pending |
| `func1` | ABI, exact selected-capacity computation, exact normal/terminal stack states, and both `func43` guards checked | `func3` frames the chunk bytes and supplies the length/read relation, reserve state, and both continuations | none at statement level; `reserveSuccessShadow`, `VecStorage_as_growSource`, and `GeometricVecFacts.reserveSuccess` close the exact normal interface | frozen statement, proof pending |
| `func2` | base identity and nontrivial equal-output effect checked; exact loop inequalities assign every excluded bounds edge to its originating guard | `SortBuffers_append` closes both recursive call directions and the driver consumes the same piecewise post | none; `func2_correct` adapts the generated-body theorem through the canonical word representation and reconstructs the exact scratch post | authoritative proof compiled |
| `func3` | all phases, both exact `0x7ffffffc` uses, decode/output loop invariants, deallocations, and three OOM states checked | exact entry initialization supplies raw stack/heap/Streams; normal and exact-OOM continuations feed outcome adequacy without reopening the body | body proof pending; the conditional partial entry bridge already compiles and accepts only a polymorphic `Func3Spec` theorem | frozen statement, proof pending; conditional adequacy compiled |
| `func4` | exact body is a single return with no state effect | valid callers `func0`,`func3` require only the returned `RuntimeContext` and continuation | none | authoritative proof compiled |
| `func5` | exact checked arithmetic, pre-commit failures, optional growth, cursor commit, and fresh full-block post reviewed | `func0`,`func3` supply valid align-1/4 layouts, Streams, and both normal/exact-OOM continuations; complete-block focus covers subsequent copy | none at statement level; instruction-level cursor/store/domain/metadata composition is proof work | frozen statement, proof pending |
| `func6` | exact body calls import 2, whose trap makes the following `unreachable` dead | valid failure sites in `func5`,`func8`,`func9` supply Streams and retain all explicitly framed allocator resources; terminal ownership omits `RuntimeContext` | none at statement level | re-frozen statement; authoritative proof compiled |
| `func7` | empty physical body permits exactly one logical retirement update | valid `func3` deallocations can reseal complete values, scratch, and input blocks; excluded destructor calls are outside this theorem | none; `BumpHeap_retire` proves the exact token/bytes transfer used by the post | authoritative proof compiled |
| `func8` | exact allocation checks, commit, `min(oldSize,newSize)` copy, retirement, and pre-commit failure preservation reviewed | sole valid `func0` use has align 1, complete old block, and `newSize>oldSize`; copied-prefix post is exactly what grow reassembly consumes | none at statement level; instruction proof must compose allocation, copy, and retirement | frozen statement, proof pending |
| `func9` | exact allocation checks, commit, positive-size zero fill, and pre-commit failure preservation reviewed | sole valid `func3` use has positive `4*n`, align 4; zero/word and token views close its continuation | none at statement level | frozen statement, proof pending |
| `func10` | exact body changes top-first `[length,pointer]` at the shim call into `[pointer,length]` at import 0 | sole driver use supplies the positive 256-byte chunk and consumes the exact read post | none | re-frozen statement; authoritative composition proof compiled |
| `func11` | exact body performs the same shim/direct-import permutation for import 1 | sole driver use supplies a positive canonical four-byte word and consumes the exact write post | none | re-frozen statement; authoritative composition proof compiled |
| `func12`--`func55` | bodies intentionally out of proof scope | every incoming public edge assigned to its caller guard | none: no WP specs by design | excluded |

Every in-scope row has completed both statement reviews, so the global
specification gate is open and bottom-up body proofs are now authorized.
`func2_correct` has completed the rebase onto the stronger frozen contract;
the allocator functions and exported driver remain body-proof work.

## Excluded panic, formatting, bounds-error, and allocation-error component

Functions 12--55 do not receive authoritative WP specifications and their
bodies are not proved.  Their cards, table map, call graph, and incoming-edge
annotations exist only to identify what is being excluded.  The proof
obligation is at each reachable originating guard:

- `func1` proves both edges to `func43` false;
- `func2` proves every edge to `func46`, `func49`, and `func55` false; and
- `func3` proves its edges to `func43` and `func46` false.

No caller may invoke a contract for the excluded body as a substitute for that
guard proof.  Stable identifiers for every root guard are in
[`scope-and-exclusions.md`](scope-and-exclusions.md).  If any edge becomes
reachable under the valid-input invariant, the public closure and
specification plan must be reopened before proof work continues.  The direct
`func6 -> talos.oom` path is not part of this exclusion: it is a valid terminal
outcome and retains its authoritative contract.

## Call-site audit checklist

For each syntactic call site, the frozen matrix must record:

1. operand-stack order and parameter interpretation;
2. resource split and pure facts that establish the precondition;
3. handling of every normal/OOM result;
4. resources needed after normal return;
5. the exact reason each excluded branch is false; and
6. the termination measure for recursive or looping callers.
