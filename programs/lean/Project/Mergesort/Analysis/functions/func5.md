# Mergesort `func5` (absolute 8, `__rust_alloc`)

## Interface and behavior

Parameters `(size,alignment)`; result is a fresh aligned pointer.  The
authoritative precondition uses a nonzero power-of-two layout.  It loads the
cursor word, selecting heap base `1049536` when zero; computes
`sum=frontier+(alignment-1)` with unsigned wrap check; computes
`base=sum & -alignment`; computes `end=base+size` with unsigned wrap check; and
rejects a negative signed i32 end, equivalently `end>=2^31`.

It computes `requiredPages=ceil(end/65536)`.  If that exceeds current
`memory.size`, it requests exactly the difference and syntactically treats
`-1` as failure.  In the pinned interpreter this module's cap is 65536 pages;
after `end<2^31`, at most 32768 pages are required, so this failure edge is
unreachable in the frozen initial-store execution.  The pure page and hard-cap
theorems are proved.  The modular WP precondition intentionally does not own
physical cap metadata, so it accepts this edge as another exact pre-commit
`talos.oom` outcome.
Only after all checks/growth succeed does it store `end` into cursor word
`1049492` and return `base`.  Any earlier failure calls `func6`; it never
returns a null failure result.

## Call sites

The reachable direct callers are `func0`, for a byte-Vec allocation at
alignment one, and `func3`, for decoded values at alignment four.  Other calls
belong to the excluded runtime and receive no proof.  Each reachable caller
supplies exact Wasm/logical size and alignment equations, complete
BumpHeap/frontier ownership, `Streams`, and a result continuation that accepts
an existential allocation id and physical bytes.

## Contract and complexity

The main contract transforms `BumpHeap` into an updated heap/metadata plus
`exists id bytes, LiveBlock heapId id ptr layout bytes`, explicitly proving
`ptr!=0`, and preserves `Streams` on success.  Arithmetic or signed-end failure
produces exact OOM with no cursor/frontier/metadata commit and with only the
Streams OOM field changed.  Freshness comes from the sparse
heap-domain frontier, not from `memory.grow`; allocations may use existing page
slack.  Exact runtime identity alone does not fix `Store.memoryCap`; both
physical growth outcomes therefore appear in the authoritative continuation.
Constant instruction count apart from one possible successful `memory.grow`.

The first contract audit failed because “uninitialized ByteSlice” was
ill-formed and freshness was unprovable from page bounds.  Decision 0002 records
the revised interface.  The corrected full-block/outcome statement now passes
both body and valid-caller reviews and is frozen; its instruction proof remains
behind the global phase gate.
