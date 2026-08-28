# Mergesort `func1` (absolute 4, `RawVecInner<A>::reserve`)

## Interface and memory input

Parameters are `(rawVecHeader, length, additional, alignment, elementSize)`.
`rawVecHeader` owns two words `[capacity, pointer]`.  The initialized logical
elements live separately at `pointer`; spare capacity follows them.  The
function also temporarily owns a 16-byte shadow-stack frame; its 12-byte grow
result begins at frame offset four.

## Behavior

It first checks unsigned wraparound of `required = length + additional`; the
failure edge calls `func43(0,0)` and is terminal.  It then chooses

```text
max(length + additional,
    2 * oldCapacity,
    elementSize == 1 ? 8 : 4)
```

as the new capacity.  (`elementSize`, not alignment, selects the 8-versus-4
minimum.)  It calls
`func0(sp+4,oldCapacity,oldPointer,newCapacity,alignment,elementSize)`.
Success updates capacity to the already chosen `newCapacity` and pointer to the
returned pointer.  A tag-one grow result is forwarded to `func43` using the two
error words and does not return normally.  Allocator OOM traps inside `func0`.
The stack pointer is restored only on normal success.

## Entry call site

`func3` calls it as `(inputVecHeader, inputLength, readCount, 1, 1)` only when
the new bytes do not fit.  The Vec invariant supplies `length <= capacity` and
the read contract supplies `readCount = min(256,remaining)`; on encoded input
this is a positive multiple of four at a reserve call.  `GeometricVecFacts` supplies
the stronger facts: exact addition/doubling, selected layout validity, complete
live-capacity ownership, and the retained-allocation cursor lineage.

## Contract and complexity

The public main spec names the exact equations
`rawVecHeader=driverBase`, `length=initialized.length`,
`additional=readCount`,
`readCount=min(256,readCount+remainingAfter.length)`,
`(alignment,elementSize)=(1,1)`,
and the reserve-needed guard `additional > capacity-length`.  It should
own `StackPointer`, `BumpHeap`, and `Streams`, and transform one `VecU8`
predicate into a larger-capacity one with a complete live block while
preserving initialized bytes, or produce exact OOM.
The caller frames the actual chunk bytes, so the pre-read `take`/`drop` and
byte-concatenation equations remain in `func3`'s loop invariant rather than in
this callee contract.
Its precondition must make both calls to `func43` unreachable: addition does
not wrap and the selected capacity produces a valid RawVec layout.  It must
also justify the old-allocation byte-size product consumed by `func0`.
The exact pre-overflow allocator arithmetic is recorded in
`../capacity-growth.md`: a first short read uses `max(count,8)` and has no later
reserve, while the multi-chunk path uses powers of two and retained blocks
force OOM on the attempted `2^30` allocation while that layout is still valid.
`GeometricVecFacts.reserveSuccess`, `VecStorage_as_growSource`, and the exact
shadow-frame reconstruction have now passed the renewed two-sided statement
audit.  On normal success the first four stack-reserve bytes are unchanged,
the remaining twelve are exactly `serialize [0,newPointer,newCapacity]`, and
the global stack pointer is restored to
`driverBase`.  On OOM inside `func0`, the exact post has
`StackPointer = driverBase-16`; all sixteen incoming shadow bytes (including
the twelve-byte result subregion), the Vec header and complete live block, the
`BumpHeap`, and all unrelated framed resources are unchanged, while
`Streams input output raised` becomes `Streams input output true` with the
exact terminal reason.  Local work is
constant; realloc copying is linear in old allocation size.
