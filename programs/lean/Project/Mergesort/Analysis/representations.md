# Canonical representation design

Status: **frozen for the authoritative contracts.  The canonical vocabulary,
including the `func3` decode and mask laws, compiles and has passed call-site
review.  This does not claim that any generated body has been proved**.

The purpose of these predicates is to make ownership transfers explicit and
prevent function contracts from passing raw byte lists with no semantic role.
Addresses used by Wasm are `UInt32`; logical lengths and sizes are `Nat`, with
explicit equations to the i32 arguments at every function boundary.

## Codec and arrays

### `U32Codec`

The single canonical codec maps a `UInt32` to its four little-endian bytes.
Public stream encoding, `WordSlice`, decode-loop facts, output-slot bytes, and
all array lemmas use this definition.  `Spec.encodeWord`,
`SortProof.wordBytes`, and example-specific serializers must be replaced by or
proved definitionally equal to it before contracts freeze.

Required pure laws:

- encoded word length is four;
- encoded list length is `4 * values.length`;
- encode/decode round trip;
- encoding commutes with list append/take/drop; and
- byte-offset `4*i` identifies logical element `i` without i32 wrap under the
  array layout facts.

Fresh ordinary allocation bytes are not assumed to contain zeros or input
data.  `decodeWords` assigns any exact `4*n` byte list its canonical initial
word view; `serialize_decodeWords_of_length`,
`ByteSlice_as_decodedWordSlice`, and `LiveBlock_as_decodedWordBlock` prove that
this is the same physical ownership with exactly `n` words.  During the driver
copy, `overwritePrefix source initial copied` records the exact mixture of
already-decoded source words and untouched arbitrary destination words.
`overwritePrefix_set_next` advances one store, and `overwritePrefix_all`
identifies the completed destination with the source.

### `ByteSlice ptr bytes`

Exclusive initialized ownership of exactly `bytes.length` consecutive memory-0
bytes beginning at `ptr`, with the no-wrap/in-bounds facts needed by loads,
stores, memory copy, and host calls.

### `OwnedRegion ptr size`

Exclusive ownership of a region whose physical contents are not logically
specified:

```text
exists bytes, bytes.length = size and ByteSlice ptr bytes
```

This is the correct result of ordinary allocation.  Calling it an
“uninitialized ByteSlice” is contradictory because `ByteSlice` names concrete
bytes.

### `WordSlice ptr values`

Four-aligned ownership of `U32Codec.serialize values` at `ptr`, with exact byte
length `4*values.length`, no wrap, and in-bounds facts.  It is a semantic view
of `ByteSlice`, not a second serializer.

### `SortBuffers source scratch input scratchValues`

Owns two disjoint `WordSlice`s of equal logical and numeric length.  It exposes
alignment and no-wrap facts and must support splitting at `mid` and recombining
both source and scratch without losing disjointness.  The numeric Wasm
arguments are included in the function contract and equated to the list
lengths; they are not inferred silently.

`WordSlice_append` now provides the reversible split/recombine operation used
by both recursive call sites, including the exact generated suffix address
`base + 4 * prefix.length`.  `SortBuffers_append` packages the two source and
scratch splits, independently callable left/right `SortBuffers`, and the
retained full cross-buffer `MemRegion.Disjoint` fact needed for recombination.
`WordSlice_get` and `WordSlice_set` focus an exact cell and return a linear
reassembly continuation; `SortBuffers_copyFocus` combines one source read and
one scratch write while preserving equal lengths and full disjointness.  Each
law requires the exact logical index bound, so it supports proving the four
`func49` edges false at their originating loop guards rather than hiding those
edges in the representation.  `SortBuffers_copyBackFocus` exposes both full
serialized ranges for the final `memory.copy` and reseals the exact nontrivial
post in which both arrays contain the same output.  The loop-invariant
arithmetic using these laws is frozen in the `func2` dossier; its body proof
remains pending.

The driver obtains a four-aligned word view of its completed input Vec from
`GeometricVecFacts.completed_ptr_align4`; this follows from the concrete
short/geometric pointer lineage, not from changing the Rust Vec's requested
alignment of one.  `align4_signedMask_eq` proves the completed byte-length
mask.  `bulk4_signedMask_eq`, `bulk4_add_tail`, `bulk4_tail_lt`, and
`bulk4_step_bounds` describe the four-word unrolled decode loop and its
zero-to-three-word tail exactly.

## Allocator ownership

### `AllocLayout wasmSize wasmAlignment size alignment`

A pure descriptor tying the Wasm arguments to the logical layout by the exact
unsigned equations `wasmSize.toNat = size` and
`wasmAlignment.toNat = alignment`.  It includes `size > 0`, `alignment > 0`,
power-of-two alignment, the exact RawVec signed-layout guard where required,
and i32-representability.  Every allocator contract names these equations; it
may not rely on an implicit coercion between Wasm words and logical sizes.  The
zero-size dangling-pointer case of `func0` is a separate variant rather than a
fake live allocation.

### `BumpDecision frontier layout`

A pure, executable classification matching the allocator instructions exactly:

```text
sum  := frontier + (alignment - 1)       -- unsigned i32 checked
base := sum & -alignment
end  := base + size                      -- unsigned i32 checked

success base end  iff both additions are exact and end < 2^31
oom               otherwise
```

`BumpHeap` has already normalized a stored cursor of zero to `heapBase`, so the
decision takes the logical frontier rather than the raw cursor word.  For
reachable alignments one/four and valid layouts this is deterministic.  The
proved `classifyBump_success_reachable` law derives freshness relative to the
old frontier, nonnullness, alignment, both end bounds, exact finish arithmetic,
and valid live metadata from every successful classification.
`allocatorRequiredPages_le_signedLimit` and
`allocatorMemoryGrow_succeeds` prove the pure page-target and hard-cap facts.
The authoritative allocator continuations do not pretend that exact module
identity determines the current physical store's instantiated cap: even in a
`.success` classification they offer both normal allocation and exact
`talos.oom` continuations.  The hard-cap theorem is retained for a later
initial-store strengthening corollary, not assumed by the main contracts.

### `LiveBlock heapId allocationId ptr layout bytes`

Owns all `layout.size` physical bytes, not only a logical initialized prefix,
plus an exclusive live-allocation handle agreeing with allocator metadata.
It exposes exact length, nonnull pointer, alignment, range end, and provenance
from the named bump heap.  Its allocation identifier is a member of the named
heap history with exactly the same pointer, layout, and `live` status.

### `BumpHeap heapId storedCursor frontier history`

Owns:

- the cursor word at `1049492`;
- the exclusive client half of the frontier authority coupled to StateInterp;
- authoritative allocation metadata; and
- physical bytes of retired blocks.

It does not own live-block bytes.  Metadata may mention live blocks but cannot
duplicate their physical ownership.  Realloc/dealloc consume the live handle
and bytes and move them into the retired part exactly once.  The sparse domain
and allocation-commit rules are specified in decision 0002.  Its pure
invariants include `heapBase <= frontier < 2^31`, the exact zero-cursor/empty-
history equivalence, cursor/frontier agreement when nonempty, and complete
ordered metadata for every committed allocation.  Page count remains physical
machine state under StateInterp.  Module identity alone does not determine
`Store.memoryCap`, because instantiated `memoryCaps` metadata takes precedence;
the main allocator specs therefore treat `memory.grow` failure as another
in-scope route to the exact `talos.oom` terminal.

`AllocationHistory` is map-native: `records` is exactly the authoritative
ghost-map value and `nextId` is its fresh sequential key.  Its proved pure
invariant is complete below `nextId`, empty at and above it, layout-valid,
ordered, nonoverlapping, and frontier-exact at the last entry.  Allocation
inserts one live entry at `nextId`; retirement changes only that entry's
status, preserving every range fact.

### `GeometricVecFacts`

A pure relation over the current Vec fields, remaining-input length, allocator
cursor/frontier, and allocation-history descriptors.  It states the
short-final or power-of-two capacity/retained-block lineage in
`capacity-growth.md` and supplies concrete no-wrap, layout-validity, and
pre-overflow-OOM facts to `func1`; “valid arithmetic” is not an opaque
assumption.  It owns neither `VecU8` nor `BumpHeap`; contracts list those two
spatial predicates separately without duplicating ownership.

The canonical map has proved lookup and transition laws: its current block is
the unique live record, reallocating that block produces exactly the next
geometric history, and `GeometricVecFacts.reserveSuccess` combines those laws
with the exact alignment-one bump result.  These are representation theorems,
not assumptions added to `func1`'s contract.

## RawVec and Vec

### `RawVecHeader header capacity ptr`

Owns the two little-endian words `[capacity,pointer]` at `header`.  It contains
no allocation bytes by itself.

### `VecU8 heapId header capacity ptr initialized`

There are exactly two variants:

```text
empty:
  three-word Vec record = [capacity 0, ptr 1, length 0],
  initialized = [], no LiveBlock

allocated:
  capacity > 0,
  RawVecHeader header capacity ptr,
  length word at header+8 = initialized.length,
  exists allocationId allBytes spare,
    LiveBlock heapId allocationId ptr (capacity, align=1) allBytes,
    allBytes = initialized ++ spare,
    spare.length = capacity - initialized.length
```

Thus `initialized.length <= capacity`, while reserve/realloc/dealloc retain
ownership of the complete capacity.

## Stack and driver frame

### `StackPointer sp`

Owns global zero and states its current i32 value.

### `StackRegion low bytes`

Owns a contiguous downward-stack region.  It supports exact append/split laws.

### `RawExportRegion base`

Owns the 272 bytes `[base,base+272)` with existential current contents.  This
is the resource obtained by splitting the raw entry StackRegion immediately
after the driver's stack-pointer subtraction; it does not also own any
structured subpredicate.

### `ExportFrame heapId base vec chunkBytes outputBytes`

After the body initializes the frame, this is a disjoint composition—not an
additional owner—of:

```text
VecU8 heapId base ... vec              owns +0..11
ByteSlice (base+12) chunkBytes          owns +12..267, length 256
ByteSlice (base+268) outputBytes        owns +268..271, length 4
```

The Vec length word at `+8` belongs to `VecU8`; `RawVecHeader` is only the
two-word view temporarily passed to `func1`.  Exact split/recombine laws let
the caller frame the length word and chunk/output slots while `func1` updates
the first two words.

### `StackReserve low bytes`

Owns `[base-16,base)`, immediately below the raw/structured export region,
with `bytes.length = 16`.  `func1` consumes it while its shadow stack pointer
is active and returns the exact reserve-prefix/result bytes on normal success.  If
allocation terminates in OOM before `func0` returns, all sixteen original
bytes are preserved and the active stack pointer is exactly `base-16`.
The entry contract therefore needs 288 bytes below the initial stack top, not
merely the driver's visible 272 bytes.

## Host and runtime

### `Streams input output oomRaised`

Owns the complete Universal host state, not independent overlapping fragments.
Read changes only input and the written buffer; write changes only output; OOM
changes only the marker and terminates with the exact host trap reason.

### `RuntimeContext`

The current Lean definition packages module identity, the exclusive
current-running-instance token, and Universal host-environment identity.  It
owns neither mutable global zero (`StackPointer`) nor mutable host state
(`Streams`) and does not hide live heap, stack, or call-frame resources.
Normal function returns restore this context.  A host trap terminates the
running expression and consumes the current-instance token, so exact terminal
OOM posts intentionally omit `RuntimeContext`; every separately owned program
resource remains available there.

The proved `module_memoryCap`, `initialStore_memoryCaps`, and
`initialStore_memoryCap` lemmas establish the declaration and initial-store
endpoints.  They are deliberately not smuggled into `RuntimeContext`: exact
module identity is insufficient because `Store.memoryCap` consults
instantiated metadata first.

## Driver terminal resources

### `DriverSuccess input output`

States empty host input, encoded sorted output, OOM false, restored initial
stack pointer and ownership of the single raw 288-byte entry StackRegion (with
final existential contents), and a final `BumpHeap` in which all driver
allocations are retired.

### `DriverOOMState phase`

Records exact OOM reason and raised marker plus phase-specific resources:

- reserve OOM: output is empty; the host input has already lost the current
  nonzero read chunk; the Vec contains exactly the earlier appended prefix;
  that current chunk remains in the frame; `StackPointer` is exactly
  `driverBase-16`; the original sixteen reserve bytes, Vec/header/live block,
  allocator state, and twelve-byte grow-result area are unchanged by the
  failed reserve attempt; and the geometric facts still describe that state;
- values-allocation OOM: input is empty and output is empty;
  `StackPointer = driverBase`; the initialized driver frame, complete input
  Vec, and allocator state immediately before the values allocation are
  returned unchanged; no values block exists; and
- scratch-allocation OOM: input and output are empty;
  `StackPointer = driverBase`; the initialized driver frame, complete input
  Vec, decoded live values block, and allocator state immediately before the
  scratch allocation are returned unchanged; no scratch block exists.

All three variants own the exact still-live blocks and an exact `BumpHeap`
whose history agrees with them.  They also preserve every unrelated runtime
resource and differ from their pre-OOM host state only by the exact trap and
raised OOM marker.

It does not falsely promise stack restoration or full input consumption in
all OOM states.  The public theorem may existentially hide this resource state
after adequacy, but the principal function contract may not discard it.

## Laws required before contract freeze

Implemented and checked so far are the canonical serialization laws,
`arrayAt`/canonical-byte equivalence, `LiveBlock` open/reseal, empty allocator
initialization, metadata/token agreement, fresh live insertion, retirement,
retired-resource transfer, pure history preservation for both transitions,
and the authoritative sparse fresh-range state update.  These laws remain
reviewable draft infrastructure until the two-sided contract audit completes.

1. Additional ByteSlice take/drop views as needed; exact append/split and
   no-wrap recombination are implemented by `ByteSlice_append`.
2. Additional WordSlice/ByteSlice conversions needed by the driver; aligned
   canonical bytes are identified by `ByteSlice_serialize_as_WordSlice`,
   zero-filled allocations by `serialize_replicate_zero` and
   `zeroLiveBlock_as_liveWordBlock`, the empty dangling-pointer path by
   `WordSlice_nil`/`SortBuffers_empty`, arbitrary four-byte output-slot stores
   by `ByteSlice_four_as_word`/`ByteSlice_storeWordFocus`, and element
   focus/update by `WordSlice_get`/`WordSlice_set`.  Arbitrary fresh values
   bytes use the `decodeWords` and `overwritePrefix` laws above; no fabricated
   initialization premise is introduced.
3. Freeze the merge-loop invariant arithmetic on top of the implemented
   `SortBuffers_append` and `SortBuffers_copyFocus` laws.
4. Additional LiveBlock views as needed; fresh-block-to-Vec packaging and
   spare-capacity focus preserve the allocation handle in
   `LiveBlock_to_VecStorage` and `VecStorage_appendFocus`.  Whole-block
   overwrite through copy/fill retains the token via `LiveBlock_bytesFocus`,
   while `VecStorage_initializedFocus`/`VecU8_initializedFocus` expose only the
   nonempty logical prefix as the driver's copy source.
5. LiveBlock open/reseal into `AllocToken * ByteSlice`, plus exact
   ByteSlice/WordSlice codec conversions that frame the token.
   `LiveWordBlocks_sortFocus` now packages both word arrays for `func2`, keeps
   their tokens out of the callee footprint, and reseals equal-length results;
   `wordRegions_disjoint_of_order` connects chronological allocation order to
   the required cross-buffer disjointness.
6. Complete the remaining VecU8 reserve/realloc/dealloc compositions;
   transparent decomposition and exact driver append reconstruction are
   implemented by `VecU8_open` and `VecU8_appendFocus`.
7. Additional instruction-facing allocator conveniences as needed; exact
   post-store allocation assembly is implemented by `BumpHeap_commit`, and
   complete live-to-retired transfer by `BumpHeap_retire`.
8. Compose both physical `memory.grow` branches with the normal/exact-OOM
   continuations selected by the allocator contracts; use the hard-cap theorem
   only for an optional initial-store strengthening.
9. Raw 288-byte StackRegion split into StackReserve/RawExportRegion, one-way
   initialization into the disjoint ExportFrame composition, frame slot
   splits, and normal consume/restore laws.  `EntryStack_split`,
   `DriverFrame_split`, `emptyVecHeaderBytes_to_VecU8`, and
   `ExportFrame_empty` implement the raw split and initialized frame assembly;
   the active 16-byte reserve has exact 4+12 decomposition through
   `StackReserve_split`.  `VecU8_as_headerBytes_storage` and
   `ExportFrame_releaseStorage` separate the deallocated Vec storage from the
   still-owned stack bytes, and `StackReserve_combineFrame` performs the final
   raw 288-byte recombination.
10. Exact read, write, and OOM host-state transitions.

The numbered items record reusable proof interfaces and possible convenience
lemmas, not unresolved contract assumptions.  The representations and
contracts have passed review, so subsequent additions must preserve these
frozen meanings while body proofs proceed bottom-up.
