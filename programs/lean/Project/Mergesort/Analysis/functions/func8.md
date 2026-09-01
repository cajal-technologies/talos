# Mergesort `func8` (absolute 11, `__rust_realloc`)

## Interface and behavior

Parameters `(oldPointer, oldSize, alignment, newSize)`; result is a fresh
aligned pointer.  It runs the same cursor selection, alignment, unsigned-wrap,
signed-end, page-rounding, and optional-growth checks as `func5`.  On success it
stores the new cursor, then copies exactly `min(oldSize,newSize)` bytes from old
to new storage when that minimum is nonzero.  The old block is retained
physically.  Every arithmetic/signed-end failure occurs before the cursor
commit and calls `func6`.  The syntactic `memory.grow=-1` edge is unreachable:
the signed-end check bounds required pages by 32768 and the exact module cap is
65536 for the frozen initial store.  The pure facts are proved; the modular
contract nevertheless accepts physical grow failure as the same exact
pre-commit `talos.oom` outcome because it does not own cap metadata.

## Call sites and contract

The only reachable caller is `func0`, at alignment one; `func21` is excluded
runtime documentation.  The main spec owns `Streams`, exact equations tying
all four Wasm arguments to the old/new layouts, and consumes a complete
`oldSize` LiveBlock and allocation token, not merely an initialized prefix.  It
returns a complete `newSize` LiveBlock whose first `min(oldSize,newSize)` bytes
equal the old prefix, transfers the old block once to retired heap ownership,
and updates the frontier/metadata.  Normal success preserves Streams.  On OOM
it returns the old live block and unchanged allocator state with only the
Streams OOM field raised.  Any logical initialized prefix a
caller wants preserved must fit within the copied minimum.  Time is linear in
the copied minimum; allocation arithmetic is constant-time.  The statement
passes the exact body-effect and sole valid-caller reviews, is frozen, and is
proved by `Func8Proof.func8_correct`, including allocation, tracked growth,
copy, retirement, and all exact pre-commit OOM arms.
