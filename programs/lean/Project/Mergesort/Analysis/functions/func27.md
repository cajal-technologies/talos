# Mergesort `func27` (absolute 30, `__rust_alloc_error_handler`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are `(size,alignment)`.  It reverses them for
`func28(alignment,size)` and then executes `unreachable`.  `func44` is its only
direct caller.

Its only incoming edge is from excluded `func44`.  The operand reversal is
recorded as ABI evidence only; no Layout predicate or terminal adapter theorem
is introduced.  Time and space are constant.
