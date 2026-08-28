# Mergesort `func46` (absolute 49, `slice_index_fail`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters describe requested range start/end, actual slice length, and source
location.  It reserves a 32-byte frame, compares the bounds, selects one of
four static diagnostic formats (start after end, index out of bounds, start out
of range, or end out of range), builds the corresponding formatter arguments,
and calls `func47`; every branch is terminal.

Called from reachable `func2` and `func3`, but only behind guards
`X-F2-SLICE` and `X-F3-READ`.  Those guards are proved false from equal buffer
lengths and `readCount <= 256`, respectively.  No `SliceIndexError` predicate
or terminal WP theorem is introduced; local work is constant.
