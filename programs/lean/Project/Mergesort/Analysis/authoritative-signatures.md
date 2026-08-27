# Authoritative specification statements

Status: **re-frozen statement set. `Contracts.lean` contains one compiling
statement for each import 0--2 and reachable local function 0--11, and no
statement for functions 12--55.  Every statement has completed its two-sided
review.  The corrections remove running-instance ownership from terminal
host-trap posts and distinguish shim-call stack order from direct-import stack
order; both boundaries are now validated by compiled composition proofs.
These are contract definitions, not body proofs**.

This file describes the statement family implemented in `Contracts.lean` on
top of the successful outcome-valued language spike.  It deliberately contains
no contract for local functions 12--55.  Those functions remain exclusion
evidence only.

## Common continuation-passing shape

`args` below are in source parameter order.  Immediately before a Wasm call,
the interpreter's operand list contains `args.reverse ++ callerStack` because
the head is the top of the operand stack.  Every theorem quantifies over the
caller's locals, `callerStack`, remaining code `K`, result arity, caller
remainder, control frames, call frames, mask, stuckness, and
`Φ : ObservableOutcome -> IProp`.

For a function with normal and OOM outcomes, its sole theorem has this shape:

```text
RuntimeContext * P(args) *
  (forall normalData,
     RuntimeContext -* Qnormal(args, normalData) -*
       WP resumeCaller(K, normalValues)) *
  (Qoom(args) -* Φ (.trapped (.host OOM.trapMessage)))
  -∗ WP call(absIndex, args, K) [{ Φ }]
```

`RuntimeContext` contains the exclusive current-running-instance token as well
as host-environment identity.  Normal returns restore it.  A host trap ends the
running expression and consumes that current-instance ownership, so terminal
continuations must not request `RuntimeContext`.  It owns no `Streams`,
`StackPointer`, or mutable memory object; all such explicitly framed resources
remain available at the terminal post.  Success-only functions omit the OOM
continuation after proving all reachable trapping edges false.  `func6` and
import 2 omit the normal continuation.  OOM-capable functions always own
`Streams input output raised`: normal return preserves it, while exact OOM
returns `Streams input output true` and otherwise preserves input/output.

The pure allocator result is never an unconstrained disjunction.  It is fixed
by `BumpDecision frontier layout`: `.success base end` selects the normal arm;
`.oom` selects the terminal arm.  A `.success` decision additionally offers
the exact OOM continuation for physical `memory.grow` failure.  Exact module
identity alone cannot exclude that branch because instantiated
`Store.memoryCaps` metadata takes precedence.

## Imports

### Import 0 — `stdio.read`, absolute index 0

Its source/host arguments are `(requested,ptr)`, so the interpreter's
top-first operand list at the direct import call is `[ptr,requested]`.  This is
different from the top-first list at the call to the Rust-order shim.

Precondition:

```text
requested.toNat = buffer.length
requested > 0
Streams input output raised
ByteSlice ptr buffer
```

Normal result only.  Let `count = min(buffer.length,input.length)` and
`prefix = input.take count`.  It returns operand `.i32 count`,

```text
Streams (input.drop count) output raised
ByteSlice ptr (prefix ++ buffer.drop count)
```

and `count <= requested`.  There is no terminal arm.

### Import 1 — `stdio.write`, absolute index 1

Its source/host arguments are `(requested,ptr)`, hence the direct import's
top-first operand list is `[ptr,requested]`.

Precondition: `requested.toNat = bytes.length`, `requested > 0`,
`Streams input output raised`, and `ByteSlice ptr bytes`.  Positivity is needed
because an empty logical slice alone does not prove that its pointer lies in
physical memory.  It returns no operands and owns

```text
Streams input (output ++ bytes) raised * ByteSlice ptr bytes.
```

There is no terminal arm.

### Import 2 — `talos.oom`, absolute index 2

Precondition: `Streams input output raised`.  There is no normal arm.  The sole
post is

```text
Streams input output true * all framed resources
```

at exactly `ObservableOutcome.trapped (.host OOM.trapMessage)`.

## Reachable generated functions

### `func0` — finish-grow, absolute index 3

Parameters are `(result,oldCap,oldPtr,newCap,alignment,elementSize)`.  Its
authoritative theorem is specialized to the sole reachable caller:

```text
alignment = 1
elementSize = 1
newCap >= 8
newSize = newCap > 0
result owns exactly twelve incoming bytes growBefore
result range is disjoint from heap blocks
oldCap = 0, oldPtr = 1, initialized = [], no old LiveBlock
  OR
oldCap > 0 and LiveBlock oldId oldPtr (size=oldCap,align=1) oldBytes
  with initialized a prefix of oldBytes
BumpHeap heap cursor frontier history
Streams input output raised
```

All multiplication and RawVec signed-layout guards are named pure facts.  On
`BumpDecision frontier (newSize,1) = success newPtr end`, normal return has no
Wasm result and writes exactly `(tag=0,newPtr,newSize)` to `result`.  It returns
a complete new live block, preserves `initialized`, updates cursor/frontier and
metadata, retires the old block when present, and preserves Streams.  In the
realloc case the new block's first `oldCap` bytes equal `oldBytes`.

On decision `.oom`, all twelve `growBefore` bytes, the old Vec/block, and the
entire incoming `BumpHeap` are unchanged; only Streams becomes
`input output true`.  The positive valid-layout premises prove the internal
layout-error, zero-size dangling, and returned-null branches unreachable.

### `func1` — byte-Vec reserve, absolute index 4

Parameters are `(header,length,additional,1,1)`.  The sole reachable theorem
names:

```text
header = driverBase
length.toNat = initialized.length
additional.toNat = count = currentChunk.length
currentChunk.length = min(256,currentChunk.length + remainingAfter.length)
0 < count and count % 4 = 0
count > capacity - initialized.length
StackPointer driverBase
StackReserve (driverBase-16) shadowBefore
VecU8 header capacity ptr initialized
BumpHeap heap cursor frontier history
GeometricVecFacts totalBytes initialized.length
  (currentChunk.length + remainingAfter.length) capacity ptr frontier history
Streams remainingAfter output raised
```

`func1` neither owns nor examines the chunk bytes or the pre-read host stream;
the caller frames the chunk region.  The stronger byte equations
`remainingBefore = currentChunk ++ remainingAfter`, `take`, and `drop` belong
to the `func10 -> func3` read-loop invariant, where those resources are
actually transformed.  The reserve contract needs only their lengths.

The facts compute `newCap = max(length+count,2*capacity,8)`, prove exact i32
addition/doubling, `newCap > capacity`, and a positive valid RawVec layout.  On
a successful `BumpDecision`, normal return has no operands, restores
`StackPointer driverBase`, returns the exact 16-byte reserve
`shadowBefore.take 4 ++ serialize [0,newPtr,newCap]`,
updates the same Vec header to `(newCap,newPtr)`, preserves `initialized`, owns
the complete new-capacity block, advances heap/facts, and preserves Streams.

On `.oom`, the exact terminal resources are:

```text
StackPointer (driverBase-16)
StackReserve (driverBase-16) shadowBefore
the unchanged Vec header, complete old live block, BumpHeap, and geometric facts
Streams remainingAfter output true
```

Thus the twelve-byte result subrange is unchanged.  Both edges to `func43` are
proved false inside this theorem.

### `func2` — recursive merge sort, absolute index 5

Parameters are `(source,n,scratch,scratchN)`.  Precondition:

```text
n.toNat = input.length
scratchN.toNat = scratchInput.length = input.length
SortBuffers source scratch input scratchInput
```

`SortBuffers` owns disjoint, aligned, in-bounds, nonwrapping `WordSlice`s and
supports exact two-buffer split/recombine at `mid`.  Normal return has no
operands and some `sorted` with:

```text
WordSlice source sorted
SortedPermutation input sorted
if input.length <= 1
  then WordSlice scratch scratchInput
  else WordSlice scratch sorted
```

There is no terminal arm.  Recursive calls use this same theorem.  The theorem
proves all edges to `func46`, `func49`, and `func55` false from its entry and
loop invariants.

### `func3` — exported driver, absolute index 6

It has no parameters or results.  Precondition:

```text
exact RuntimeContext for the frozen module/Universal host
StackPointer entrySp, where entrySp = 1048576
StackRegion (entrySp-288) entryBytes, entryBytes.length = 288
BumpHeap heap storedCursor=0 frontier=heapBase history=[]
Streams (U32Codec.serialize original) [] false
```

Normal return owns `StackPointer entrySp`, one raw 288-byte `StackRegion` with
existential final bytes, a `BumpHeap` in which every driver allocation is
retired, and

```text
Streams [] (U32Codec.serialize sorted) false
SortedPermutation original sorted.
```

The only terminal outcome is exact OOM, represented by one of three disjoint
constructors:

```text
reserve:
  serialize original = appended ++ currentChunk ++ remaining
  currentChunk is nonempty and is the just-read chunk
  StackPointer (driverBase-16), original shadow bytes active
  VecU8 contains appended; frame chunk contains currentChunk
  pre-reserve BumpHeap/Vec unchanged; Streams remaining [] true

values:
  read loop complete; VecU8 contains serialize original
  StackPointer driverBase; lower reserve inactive; no values block
  pre-values-attempt BumpHeap unchanged; Streams [] [] true

scratch:
  read/decode complete; VecU8 contains serialize original
  a live values block contains original; no scratch block
  StackPointer driverBase; pre-scratch-attempt BumpHeap unchanged
  Streams [] [] true
```

Every constructor owns all other frame pieces and all still-live allocation
tokens/bytes.  Successful read-loop completion derives
`byteLength < 2^31`; together with four-byte divisibility this proves the
implementation equation `byteLength & 0x7ffffffc = byteLength`.  The following
branch is the valid empty/nonempty split, not an excluded high-bit path.  The
second use of the same mask computes the exact four-word decode prefix
`4*(n/4)`; the remaining `n%4` words form a tail of length below four.  The
decode destination starts as the canonical view of arbitrary fresh bytes and
advances through `overwritePrefix original initial copied`, so the statement
does not assume fabricated allocation contents.  The theorem also proves its
`func43` and `func46` edges false.  Public adequacy may hide terminal resource
details, but is derived only from this theorem plus entry initialization.

### `func4` — allocation marker, absolute index 7

No parameters/results.  Identity on all resources, arbitrary `Φ`, and caller
continuation.  Reachable direct callers are only `func0` and `func3`.

### `func5` — allocation, absolute index 8

Parameters `(size,alignment)`, with reachable `alignment` one or four.  Pre:
exact Wasm/logical layout equations, positive valid layout,
`BumpHeap heap cursor frontier history`, and `Streams input output raised`.

On `BumpDecision frontier layout = success base end`, it returns `.i32 base`,
an updated heap/metadata and

```text
exists id bytes, LiveBlock heap id base layout bytes
```

with freshness, alignment and nonnull facts, preserving Streams.  On `.oom`,
the incoming heap is unchanged and it terminates with
`Streams input output true`.  The `memory.grow=-1` branch is false from the
initial-store cap arithmetic, but remains an accepted exact-OOM branch of the
modular main spec because its precondition intentionally does not own physical
cap metadata.

### `func6` — OOM shim, absolute index 9

No parameters.  Precondition `Streams input output raised`.  No normal arm.
It composes import 2, returns `Streams input output true` and all framed
resources at exact OOM, and proves its following `unreachable` is never stepped.

### `func7` — no-op deallocation, absolute index 10

Parameters `(ptr,size,alignment)` with exact equations to a complete
`LiveBlock`; reachable alignments are one/four.  It has no Wasm result and no
terminal arm.  Physical bytes and cursor/frontier are unchanged, while the
ghost transition consumes the allocation token, marks its unique metadata
entry retired, and transfers the bytes exactly once into `BumpHeap`.

### `func8` — reallocation, absolute index 11

Parameters `(oldPtr,oldSize,1,newSize)` in the sole reachable use, with
`0 < oldSize < newSize`, exact old/new layout equations, a complete old
`LiveBlock`, `BumpHeap`, and `Streams`.  On a successful `BumpDecision`, it
returns `.i32 newPtr`, retires the old token/bytes, creates a complete new live
block whose first `oldSize` bytes equal all old bytes, updates heap metadata,
and preserves Streams.  On `.oom`, old block and heap are exactly unchanged and
only the Streams marker changes.  Grow failure is unreachable.

### `func9` — zeroed allocation, absolute index 12

Parameters `(size,4)` with exact positive layout equations, `BumpHeap`, and
`Streams`.  It follows `func5`'s deterministic decision.  Normal return is
`.i32 ptr` plus a fresh complete live block whose byte list is exactly
`List.replicate size 0`, updated heap metadata, and unchanged Streams.  OOM
preserves the heap and changes only the Streams marker.  The scratch corollary
uses `size=4*n` to expose `WordSlice ptr (List.replicate n 0)`.

### `func10` — read shim, absolute index 13

Parameters `(ptr,requested)`.  It has import 0's exact pre/post but proves the
ABI permutation to host `(requested,ptr)`.  The call to `func10` has top-first
operands `[requested,ptr]`; after entering the shim, its two `local.get`s leave
the direct-import top-first list `[ptr,requested]`, which host invocation
reverses to `(requested,ptr)`.  It returns `.i32 count`.  The driver instantiates
it only with requested length 256.

### `func11` — write shim, absolute index 14

Parameters `(ptr,requested)`.  It has import 1's exact pre/post and proves the
same two-level operand permutation: shim call `[requested,ptr]`, direct import
`[ptr,requested]`, host arguments `(requested,ptr)`.  It returns no operands.
The driver instantiates it only with requested length four.

## Exclusion obligations, not callee contracts

The reachable theorems must prove these guards false at their origin:

- `func1`: both calls to `func43`;
- `func2`: the call to `func46`, four calls to `func49`, and the call to
  `func55`;
- `func3`: the call to `func46` and both calls to `func43`; and
- no allocator grow-failure exclusion: `func5`, `func8`, and `func9` route
  `memory.grow=-1` through the in-scope exact `talos.oom` continuation.

No theorem for an excluded callee may be introduced to discharge one of these
obligations.  The direct `func6 -> import2` OOM path remains an ordinary,
in-scope contract composition.  Stable obligation identifiers and the
transitive exclusion boundary are recorded in
[`scope-and-exclusions.md`](scope-and-exclusions.md).
