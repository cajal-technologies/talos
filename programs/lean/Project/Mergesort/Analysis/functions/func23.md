# Mergesort `func23` (absolute 26, `default_alloc_error_hook`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters `(alignment,size)` are ignored.  The function stores byte one at
address `1049524` and returns.  It is installed at table slot one and is the
initial target selected by `func18`.

Its direct use is an indirect call from excluded `func18`; no valid-input path
reaches the allocation-error selector.  The marker store is documentation only
and receives no state predicate or WP theorem.  Time and space are constant.
