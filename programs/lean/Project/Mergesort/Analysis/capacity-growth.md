# Input Vec growth and pre-overflow OOM analysis

Status: **binary arithmetic, reserve layout, no-reserve append, successful
reserve lineage, allocator continuations, and whole-loop control/spatial
composition are implemented and used by the completed `func1`/`func3` proofs**.

This analysis supplies the named lineage required by the `func1` and `func3`
contracts.  It is not an informal excuse to omit the RawVec error edges.

## Read-loop facts

The driver requests 256 bytes on every `func10` call.  At each call the read
contract gives `count = min(256, remaining)`.  Public encoded input begins with
`remaining % 4 = 0`; because 256 is also a multiple of four, induction shows
that every returned count and every new remainder is a multiple of four.  A
nonempty result therefore has `4 <= count <= 256`.

The input Vec starts as `(capacity=0,pointer=1,length=0)`.  Reserve is called
exactly when `count > capacity-length`, with `(alignment,elementSize)=(1,1)`.
The selected capacity is

```text
max(length + count, 2 * oldCapacity, 8).
```

The first nonempty read has `count=min(256,totalByteLength)`:

- if `count<256`, the host input is now empty and reserve selects
  `max(count,8)`; there can be no later nonzero read or reserve;
- if `count=256`, reserve selects capacity `2^8=256`.

Thereafter, if capacity is `2^k` for `k>=8`, a reserve call has
`length<=capacity`, `length+count<=capacity+256<=2*capacity`, and is triggered
only because the required length exceeds capacity.  Hence the next capacity is
exactly `2^(k+1)`.  Between reserves the capacity is unchanged.  A final
partial chunk either fits or triggers that same doubling, after which input is
empty.

The intended pure `GeometricVecFacts` relation consequently has three
variants:

- the initial zero-capacity state;
- a completed short-input state with empty host remainder, byte length below
  256, and capacity `max(byteLength,8)`; or
- the large-input lineage:

  - capacity `2^k` for `8<=k<=29` on every normally reachable public state;
  - `length<=capacity`;
  - current live block size `capacity`;
  - retired blocks of sizes `2^8,...,2^(k-1)`; and
  - exact read-loop cursor contribution equal to the sum of all those block
    sizes, before the values/scratch allocations begin.

The short-input variant is not part of the geometric sum and never invokes
reserve again.  It still supplies the valid layout and full live-block facts
needed by later decode/deallocation.

## Exact retained-allocation sum

With alignment one, the input Vec allocations introduce no padding.  After a
successful `2^k` allocation the cursor is

```text
heapBase + sum(i=8..k, 2^i)
= 1,049,536 + (2^(k+1) - 256).
```

For `k=29`, this is

```text
1,049,536 + (2^30 - 256) = 1,074,791,104 < 2^31.
```

Thus all allocations through capacity `2^29` pass the allocator's signed-end
test.  In the pinned interpreter, this module's undeclared maximum gives the
hard cap of 65536 pages.  Any end below `2^31` needs at most 32768 pages, so
the allocator's requested growth succeeds deterministically from the frozen
initial store.  The modular main specs do not own physical cap metadata, so
their continuations still accept the syntactic `memory.grow = -1` edge as the
same exact `talos.oom` terminal.

The next reserve selects `2^30`.  Its RawVec layout is still valid because

```text
2^30 <= 2^31 - alignment = 2^31 - 1.
```

But the bump allocator would compute

```text
1,074,791,104 + 2^30 = 2,148,532,928 > 2^31 - 1,
```

so `func5`/`func8` calls `func6` and reaches exact OOM before committing the
cursor.  A later capacity `2^31`, which would fail RawVec's layout guard and
reach `func43`, is never requested on a normal public execution.

At the failing `2^30` reserve, `length <= 2^29` and `count <= 256`; therefore
`length+count` and `2*oldCapacity` are also exact unsigned i32 computations.
This rules out the earlier addition-overflow `func43` edge.

## Implemented transition and completed loop composition

`GeometricVecFacts.reserveLayout` now proves the exact addition, selected
capacity bound, and valid alignment-one layout needed at an active reserve.
`GeometricVecFacts.reserveSuccess` proves the exact normal transition: an
initial allocation establishes either the completed short form or exponent-8
form, while a large allocation doubles the capacity, retires the unique old
live geometric record, and advances the canonical history by one exponent.
Its signed-end premise also proves that normal success cannot advance beyond
exponent 29; the attempted exponent-30 allocation is therefore an OOM outcome,
not a later RawVec layout-error call.
`GeometricVecFacts.appendWithoutReserve` proves the other nonempty-read arm:
the exact generated free-capacity test preserves the current large lineage
without changing its block or history.  Its premises are inconsistent with
both the empty and completed-short variants.
`allocatorRequiredPages_le_signedLimit` proves the 32768-page bound and
`allocatorMemoryGrow_succeeds` proves success at the 65536-page hard cap.
Because `RuntimeContext` does not own the physical store's instantiated cap
metadata, the authoritative contracts accept exact `talos.oom` on
`memory.grow=-1` even in a successful arithmetic classification.  The hard-cap
result supports an optional initial-store strengthening; it is not an unlinked
precondition of the modular specs.

The completed read-loop proof in `DriverProof` phrases the loop invariant as a
preservation/progress statement for `GeometricVecFacts`, not merely the closed-
form arithmetic above.  Its premise names a remaining byte count divisible by
four and the exact read equation `count = min(256, remaining)`; the weaker fact
`count <= 256` is used only for the separate oversized-read guard.  Given those
facts and the current Vec/heap descriptors, the proof establishes exactly one
of:

1. `GeometricVecFacts.appendWithoutReserve` supplies the no-reserve arm;
2. reserve layout is valid and `GeometricVecFacts.reserveSuccess` supplies the
   normal continuation; or
3. the allocator reaches exact OOM before either call to `func43` is reachable.

The zero final read is covered without changing the lineage.  These cases feed
`Func1Proof.func1_correct_of`, then `DriverProof.func3_correct_of`, and finally
the closed `Proof.func3_correct` composition.
