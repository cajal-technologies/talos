# Mergesort `func3` (absolute 6, exported `mergesort`)

Status: **authoritative `Func3Spec`, generated body proof, modular composition,
and public partial-adequacy theorem complete**.

## Interface

No explicit parameters or results.  Inputs are the Universal host stream, the
initial stack pointer, allocator/Vec state, linear memory, runtime module, and
host-operation capabilities.  It reserves the structured 272-byte
`ExportFrame` described in the directory README.  Because `func1` reserves a
further 16 bytes, entry owns one raw 288-byte region below the initial stack
top—not a pre-initialized Vec or an overlapping structured frame.

After subtracting 272 from the stack pointer, the body partitions and
initializes the raw region.  The frame becomes
`(capacity=0,pointer=1,length=0)`, the 256-byte
chunk is zero-filled, and the output slot is reused later.  The input Vec owns
its complete capacity, including spare bytes; retired buffers from geometric
reallocations move into the bump heap.

## Read loop

It repeatedly calls `func10(frame+12, 256)`.  For nonzero count it calls
`func1` if the Vec lacks spare capacity, copies the chunk to
`input.pointer + input.length`, updates length, and repeats.  Count above 256
calls `func46`; the host contract excludes it.

Immediately before a read, the invariant has
`serialize original = appended ++ remainingBefore`; the Vec contains exactly
`appended`.  Immediately after it, the read contract gives
`remainingBefore = current ++ remainingAfter`,
`current.length = min 256 remainingBefore.length`, and the chunk region is
`current ++ chunkTail` of length 256.  Hence every nonzero `current` is a
multiple of four for public input.  The invariant also retains the
short-final or power-of-two `GeometricVecFacts` lineage, the complete live Vec
allocation (including spare capacity), the output slot, and the exact bump
frontier/history.

If spare capacity is insufficient, these facts and the untouched sixteen-byte
lower stack reserve establish the sole `func1` precondition.  On success the
exact returned shadow bytes are framed back below the driver, then
`VecU8_appendFocus` replaces precisely the next `current.length` spare bytes
and the length word.  On OOM the current chunk has been consumed from the host
but has not been appended, which is exactly `DriverReserveOOM`.  The
termination measure is `remainingBefore.length`: a nonzero read strictly
decreases it, and the final read returns zero.

## Decode, sort, and output

Let `B = (serialize original).length = 4*n`, where `n = original.length`.
Byte length not divisible by four returns without output; canonical public
input excludes this branch at its originating test.  Successful read-loop
completion gives `B < 2^31`, and canonical serialization gives `B % 4 = 0`,
so `align4_signedMask_eq` proves the implementation equation
`B & 0x7ffffffc = B`.  The following branch is the ordinary empty/nonempty
split, not a high-bit failure branch.

For `n=0`, the body uses aligned dangling pointer four for both buffers and
still calls `func2(4,0,4,0)`; `SortBuffers_empty` supplies exactly this call.
No allocator or deallocator call occurs on that path.

For `n>0`, `func5(B,4)` first returns an arbitrary fresh `B`-byte values
allocation.  `decodeWords` gives that allocation a canonical initial
`n`-word view.  The source Vec is simultaneously exposed as the canonical
`WordSlice` for `original`; `GeometricVecFacts.completed_ptr_align4` supplies
the concrete alignment even though the Vec requested allocation alignment
one.  If `initial` denotes the arbitrary destination words, the decode-loop
invariant after `copied` stores is

```text
source      = WordSlice inputPtr original
destination = LiveWordBlock valuesPtr
                (overwritePrefix original initial copied)
0 <= copied <= n
```

The second mask is exact data arithmetic:
`bulk4_signedMask_eq` gives `bulk = 4*(n/4)`, while
`bulk4_add_tail` gives `bulk + n%4 = n`.  The unrolled loop has
`copied = 4*iteration < bulk`; `bulk4_step_bounds` proves that all four indices
`copied..copied+3` are below `n`, and four applications of
`overwritePrefix_set_next` advance it.  The tail loop starts at `bulk`, copies
exactly `n%4 < 4` words, and ends at `copied=n`; `overwritePrefix_all` then
reseals `LiveWordBlock valuesPtr original`.  This assigns every decode load and
store bound to the loop guard that justifies it.

Next `func9(B,4)` returns a disjoint zeroed scratch allocation.
`zeroLiveBlock_as_liveWordBlock`, allocation order, and the two live tokens
establish `SortBuffers valuesPtr scratchPtr original (replicate n 0)` for the
single `func2` call.  Its frozen post returns the sorted source and the exact
piecewise scratch content needed to reseal both live blocks.

The output loop invariant after `emitted` iterations is that the host output
is `serialize (sorted.take emitted)`, the source pointer is
`valuesPtr + 4*emitted`, and the byte counter is `4*(n-emitted)`.  Each store to
the four-byte frame slot plus `func11(frame+268,4)` appends exactly the next
canonical word.  Thus the loop performs exactly `n` writes and ends with
`serialize sorted`.

The body then calls no-op `func7` in the exact order values, scratch, input
Vec.  Each call transfers the whole live block/token into the retired portion
of `BumpHeap`; the frame-header bytes remain owned separately.  Finally the
sixteen-byte reserve and 272-byte frame recombine into one raw 288-byte entry
region and the original stack pointer is restored.

Allocator OOM can occur in three phases: input-Vec reserve (with `func1`'s
16-byte shadow frame still active and only an input prefix consumed), values
allocation, or scratch allocation.  No allocation occurs after output starts,
so an OOM execution has produced no output, but its resource post must still
classify the phase rather than promise universal stack restoration.

The reserve-OOM post has the stack pointer exactly at `frame-16` and preserves
the original sixteen shadow bytes, previous Vec/live block and allocator state;
the current nonzero chunk has already been consumed from the host stream but
not appended.  Values OOM has stack pointer `frame`, completed input Vec, and
no values block.  Scratch OOM has stack pointer `frame`, completed input Vec,
decoded live values block, and no scratch block.  Every variant owns all frame
pieces/live blocks and `Streams remaining [] true`.

## Main contract and adequacy boundary

The principal entry WP spec assumes `encodeValues input`, the exact initial
runtime/stack/heap/host predicates, and concludes either exact sorted encoded
output with restored stack or the distinguished OOM terminal outcome.
`DriverProof.func3_correct_of` proves the generated body conditionally from the
three reachable Vec/allocation contracts.  `Proof.func3_correct` closes that
composition using the completed `func1`, `func5`, and `func9` theorems (and,
transitively, `func0` and `func8`).

The theorem `entry_adequacy_of_func3` constructs the initial resources at a
genuine `call 6` configuration and derives the public partial entry
specification solely from the polymorphic `Func3Spec` theorem.
`Proof.mergesort_correct` applies that bridge to the completed theorem.  It
classifies every finite terminal execution and intentionally does not claim
termination.  The obsolete total entry statement was removed to avoid
presenting partial adequacy as termination.  Wrapper work is `Theta(B)` for
`B=4n`, excluding the `Theta(n log n)` sort.

## Failure-edge audit

- `count>256` is false by `func10`.
- `length+count`/RawVec layout failures are false by `GeometricVecFacts`; the
  exact pre-overflow OOM arithmetic is in `capacity-growth.md`.
- allocator-returned-null branches are false from the normal allocator post.
- partial-word return is false because the public byte length is `4*n`.
- the post-read `0x7ffffffc` mask equals the full byte length because
  `GeometricVecFacts.completed_lt_signed` supplies the signed bound and the
  codec supplies the two zero low bits; the subsequent branch is exactly the
  valid empty/nonempty split, not an excluded error path.
- every decode-loop load/store is in range by the bulk/tail invariants above;
- sort panic edges are false from `SortBuffers` and its internal invariants;
- imported read/write do not trap under owned in-bounds buffers.

The first contract audit failed on stack reserve, allocation ownership, and OOM
post-state precision.  Those defects are repaired in the authoritative
contract.  The completed body proof and sole public-entry caller/adequacy
composition preserve that statement without weakening its resource or outcome
claims.  Future maintenance must retain the same boundary.
