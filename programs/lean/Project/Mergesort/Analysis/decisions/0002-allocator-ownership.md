# Decision 0002: sparse allocator ownership and freshness

Status: **token/metadata/retired-byte model, sparse fresh-range primitive, and
reachable align-1/4 classification arithmetic implemented and proved;
target-function contracts and the allocator commit composition remain under
review and are not frozen**.

## Problem

`func5`, `func8`, and `func9` allocate from a monotonically increasing bump
cursor.  A logical allocation must return exclusive ownership of exactly its
requested bytes.  It must work both after `memory.grow` and in slack already
present in existing pages, without materializing every byte in a page.

The current `heapAddressesInBounds` invariant proves only that authoritative
ghost keys refer to physical memory.  It does not prove a requested range is
absent.  Allocation history alone is also insufficient because stack, static,
header, host-buffer, and other client-owned bytes are represented in the same
authoritative memory map.

## Required domain/frontier invariant

The sparse authoritative heap must be coupled to a monotone logical frontier:

```text
HeapBelow sigma frontier :=
  every authoritative memory-0 key in sigma has address < frontier

StateInterp :=
  exists sigma frontier,
    genHeapInterp sigma *
    frontierAuth frontier *
    pure(HeapBelow sigma frontier) *
    existing state resources

BumpHeap heapId storedCursor frontier history :=
  cursorWord |->u32 storedCursor *
  frontierOwn frontier *
  AllocMetaAuth heapId history *
  RetiredBytes heapId history *
  pure(heapBase <= frontier and frontier < 2^31) *
  pure(storedCursor = 0 iff history is empty and frontier = heapBase) *
  pure(storedCursor != 0 -> storedCursor.toNat = frontier) *
  pure(nonempty history -> the last allocation ends at frontier) *
  pure(history covers every committed allocation and is ordered, aligned,
       nonoverlapping, and status-complete)
```

`frontierAuth` and `frontierOwn` must agree and the client fragment must be
exclusive.  The metadata authority is the map stored directly in
`AllocationHistory`, with `nextId` naming the next fresh sequential key.  It
records live/retired status but cannot duplicate physical byte ownership.
`RetiredBytes` is a separating map over the same metadata map: live entries
contribute `emp`; retired entries own both their exclusive retired ghost
fragment and their complete bytes.  These equations rule out a zero cursor or
frontier inside reserved static memory after an allocation, and make double
retirement structurally invalid.

The Mergesort initial state exposes `frontierOwn heapBase`; every initially
materialized memory-0 key is below heap base.  Downward stack writes and static
data stay below it.  Ordinary loads/stores, fills, copies, host transfers, and
memory growth preserve the key domain and therefore preserve `HeapBelow`.

## Live versus retired blocks

A live block is separate from `BumpHeap`, but its exclusive fragment agrees
with the heap's metadata authority:

```text
LiveBlock heapId allocationId ptr layout bytes :=
  AllocToken heapId allocationId ptr layout *
  ByteSlice ptr bytes *
  pure(bytes.length = layout.size) *
  pure(ptr != 0 and ptr is layout-aligned)
```

The frozen interface includes the open/reseal equivalence

```text
LiveBlock heapId id ptr layout bytes
  <-> AllocToken heapId id ptr layout * ByteSlice ptr bytes * layout facts.
```

The token agrees with a unique `live` history entry.  Allocation creates one
new live entry/token.  Reallocation atomically marks the old entry retired and
creates the new live entry/token after the machine copy has succeeded.
Deallocation consumes the token and marks its entry retired.  The corresponding
bytes move into `RetiredBytes` exactly once.

`VecU8` owns its header and one complete live block of `capacity` bytes.  It
relates its initialized logical prefix to the corresponding byte prefix and
keeps the spare suffix existential.  Owning only the initialized prefix is not
enough: `func8` copies `min(oldSize,newSize)`, which is normally the complete
old capacity.

Reallocation and deallocation consume a live block.  Its old physical bytes
are transferred to the retired portion of `BumpHeap`; no separate
retired-block owner is used.  They may never remain owned by both caller and
heap.

## Allocation commit point

`memory.grow` is not the allocation event.  A requested block can straddle the
old page boundary, and later allocations can use already-grown slack.  Growth
only changes the physical in-bounds relation and preserves the frontier.

The logical commit is the allocator's final store to the cursor word, common
to grow and no-grow paths.  The proved generic rule
`stateInterp_alloc_freshRange` already performs the sparse-domain portion: it
uses the authoritative frontier to insert exactly the current physical bytes,
returns their `pointsToBytes`, and advances the exclusive frontier fragment.
The specialized `func5` proof must compose that rule with the cursor store and
the proved map-native metadata transition.  The complete commit must:

1. consume the cursor word and `frontierOwn oldFrontier`;
2. establish `oldFrontier <= base`, `end = base + size`, no wrap, signed bound,
   and physical in-bounds facts;
3. use `HeapBelow` to prove `[base,end)` is fresh;
4. insert exactly the current physical bytes of `[base,end)` into the sparse
   authoritative map (proved generically);
5. update cursor and frontier to `end` (frontier update proved generically;
   cursor update remains the ordinary Wasm store in the body proof);
6. extend `AllocMetaAuth` with one fresh live allocation identifier; and
7. return `exists allocationId bytes,
   LiveBlock heapId allocationId base layout bytes`.

Step 2 and the pure metadata-validity part of step 7 are now provided by
`classifyBump_success_reachable` for the only reachable alignments, one and
four.  The specialized body proof must consume that law; it must not restate
those arithmetic properties as unproved caller assumptions.

Alignment gaps and unused page slack remain unowned.  `memory.grow` is
deterministic in the pinned interpreter.  For this module the effective cap is
65536 pages, while an allocator end below `2^31` requires at most 32768 pages;
therefore the grow-failure branch is unreachable from the frozen initial
store.  A later contract audit found that exact module identity alone does not
fix `Store.memoryCap`, since instantiated metadata takes precedence.  The
authoritative modular allocator specs consequently accept grow failure as an
exact pre-commit `talos.oom` outcome.  The proved hard-cap fact is a possible
initial-store strengthening, not an uncoupled assertion in `BumpHeap`.

## Rejected helper shape

The rejected `byteHeapAux_pointsTo` required point fragments for the entire old
authoritative map.  Those fragments are distributed among clients while
`StateInterp` owns only the authority, so it cannot implement this commit.  A
range-insertion update instead starts from `genHeapInterp sigma`, the
authoritative `HeapBelow` fact, and physical byte bounds, returning authority
plus fragments for only the inserted range.  That replacement is now the
proved `genHeap_alloc_freshBytes`/`stateInterp_alloc_freshRange` path.

## Consequences for authoritative contracts

- `func5` returns `exists id bytes, LiveBlock heapId id ptr layout bytes`, plus exact
  nonnull/alignment/freshness facts; “uninitialized ByteSlice” is invalid.
- `func8` consumes the complete `oldSize` block and returns a complete
  `newSize` block whose prefix of length `min(oldSize,newSize)` equals the old
  prefix.  Any separately named initialized prefix must fit in that minimum.
- `func9` returns a complete zero byte block.  Its zero `WordSlice` corollary
  additionally requires `size = 4*n`, alignment four, and no arithmetic wrap.
- `func0` transfers live-block ownership through the grow-result abstraction,
  not merely the returned pointer words.
- `func1`'s Vec predicate owns initialized and spare bytes, and its geometric
  lineage proves all layout/capacity panic edges false.

## Later acceptance test

After the specifications freeze, test a 64-byte allocation crossing an old
page boundary followed by a 32-byte allocation in already-grown slack.  The
postcondition must own only those 96 requested bytes, preserve an old sentinel,
and expose the updated cursor/frontier.  This distinguishes the required
interface from both rejected page-materialization and grow-only ownership
schemes.
