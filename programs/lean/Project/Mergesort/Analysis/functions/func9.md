# Mergesort `func9` (absolute 12, `__rust_alloc_zeroed`)

Parameters `(size, alignment)`; result is a fresh aligned pointer.  It performs
the same bump allocation checks and cursor commit as `func5`, then fills exactly
`size` bytes with zero when size and pointer are nonzero.  Failure occurs only
before commit, calls `func6`, and never returns null normally.

`func3` is its only reachable caller and uses it for `4*n` scratch bytes at
alignment four.  The main contract owns exact Wasm/logical layout equations,
`BumpHeap`, and `Streams`; it returns a complete zero-byte LiveBlock with a new
allocation token and updated heap metadata while preserving Streams, or exact
OOM with unchanged allocator state and only the Streams OOM field raised.  The
signed-end bound and initial-store cap make the syntactic grow-failure edge
unreachable in the frozen entry execution.  The modular contract still
accepts it as the same exact OOM terminal, and the pure page bound and
grow-at-hard-cap theorem are already proved.  The
zero-valued `WordSlice` of length `n` is a
codec corollary requiring the caller's exact facts `size=4*n`, alignment four,
and no wrap.  Time is linear in `size` due to `memory.fill`.  With the canonical
zero/live-word conversion proved, the statement passes both review directions,
is frozen, and is proved by `Func9Proof.func9_correct`, including tracked
growth, exact zero fill, and all pre-commit OOM arms.
