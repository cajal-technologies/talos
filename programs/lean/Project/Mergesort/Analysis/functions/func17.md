# Mergesort `func17` (absolute 20, `end_short_backtrace<rust_oom>`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Its sole parameter points to an allocation `Layout`.  It calls `func18` with
that pointer and then executes `unreachable`.  `func28` is its only direct
caller.

Its sole incoming edge is from excluded `func28`, so it is transitively
unreachable after the allocation-error roots are closed.  The Layout forwarding
is documentation only; no terminal contract is introduced.  Wrapper overhead
is constant.
