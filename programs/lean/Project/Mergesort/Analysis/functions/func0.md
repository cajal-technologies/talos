# Mergesort `func0` (absolute 3, `RawVecInner<A>::finish_grow`)

## Interface

Parameters are `(resultPlace, oldCapacity, oldPointer, newCapacity, alignment,
elementSize)`; there is no direct Wasm result.  The caller provides a writable
12-byte result object at `resultPlace`.  If `oldCapacity != 0`, `oldPointer`
must designate the retained allocation of `oldCapacity * elementSize` bytes.

## Behavior

It computes `newSize = newCapacity * elementSize` in i64 and rejects a nonzero
high word.  It then rejects `newSize > 2^31 - alignment`, the guard used by this
compiled RawVec layout path.  For an existing allocation it calls
`func8(oldPointer, oldCapacity*elementSize, alignment,newSize)`.  With no old
allocation and nonzero size it calls `func4` then `func5`; with neither an old
allocation nor a nonzero new size it uses `alignment` as Rust's aligned
dangling pointer without allocating.

```text
success: +0 tag=0, +4 pointer, +8 newSize-in-bytes
layout overflow: +0 tag=1, +4=0, +8 is unchanged
generic null-allocation record: +0 tag=1, +4 alignment, +8 newSize-in-bytes
```

The Talos allocator traps on allocation failure and a valid bump-heap state
cannot make it return address zero, so the generic null-allocation record is
unreachable under the intended precondition.  It remains part of the binary's
control-flow analysis because `func1` tests the tag.

On layout overflow the old live block, BumpHeap, and result word at `+8` are
unchanged.  If both old capacity and new size are zero, success returns the
aligned dangling pointer and no `LiveBlock`; this branch is excluded at the
only reachable call because `func1` selects a positive capacity.  A nonzero
old capacity with zero new size would use `func8` and needs a separate
realloc-zero contract if it ever becomes reachable; it is also excluded by
that caller invariant.  On successful positive-size realloc the complete old
block is consumed and retired, a complete new block is returned, and its
copied prefix is exposed.  On successful fresh allocation a complete new block
with existential contents is returned.  On allocator OOM the result record
and old allocation state are unchanged apart from the host marker because the
cursor commit never occurs: all twelve result bytes retain their incoming
values.

## Call sites and contract implications

`func1` is the only public-path caller.  It passes its 12-byte shadow-stack
result region, the two RawVec header words, its chosen capacity, then
`(alignment,elementSize)`.  It consumes only the tag and returned pointer;
`func1` already knows the capacity it selected.  The authoritative spec is
specialized to this valid call site: alignment and element size are one,
selected `newCapacity >= 8`, `newSize = newCapacity > 0`, and the old block
(when present) has size exactly `oldCapacity`.  Its only outcomes are
positive-size success or exact OOM.  The internal layout-error, zero-size, and
allocator-returned-null branches are documented above but proved unreachable
from these named premises.  The spec therefore needs a structured
`RawVecGrowResult`, `AllocLayout`, and `BumpHeap`; the caller must not
manipulate these three words separately.  It also threads
`Streams input output raised`: success preserves it and exact OOM returns
`Streams input output true`.  Constant instruction count
aside from allocator copy and possible memory growth; realloc copies
`min(oldCapacity*elementSize,newSize)` bytes.

The generic control-flow dossier records that a layout-overflow result would
preserve the caller's previous third word, matching the partial write, but that
variant is intentionally absent from the valid-input main spec.  The frozen
specialization supplies the exact old-allocation invariant making
`oldCapacity*elementSize` exact and the valid-layout facts eliminating tag
one.  Result-place/old-block/new-range disjointness is derived from separating
ownership plus `BumpHeap`'s exclusive frontier and `StateInterp`'s below-
frontier heap domain; it is not an additional uncoupled address assumption.
