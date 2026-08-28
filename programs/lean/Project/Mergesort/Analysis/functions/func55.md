# Mergesort `func55` (absolute 58, `copy_from_slice::len_mismatch_fail`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are source length, destination length, and source-location pointer.
It reserves a 32-byte frame, constructs formatter arguments for both lengths
and the static mismatch message, calls `func47`, and never returns.

Its only call site is `func2` immediately before the final `memory.copy`.
Obligation `X-F2-COPY` proves that guard false from equal source/scratch
lengths.  No length-mismatch predicate or terminal WP theorem is introduced.
Local work before formatting is constant.
