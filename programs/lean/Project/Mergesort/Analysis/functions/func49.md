# Mergesort `func49` (absolute 52, `panic_bounds_check`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are `(badIndex, length, sourceLocation)`.  It reserves a 32-byte
frame, creates formatting arguments for the two numbers and the static bounds
message, calls `func47`, and never returns.

All four call sites are the `X-F2-INDEX-1` through `X-F2-INDEX-4` guards in
reachable `func2`.
Each is proved false by its phase-specific loop invariant.  No `BoundsError`
predicate or terminal WP theorem is introduced.  Local work before formatting
is constant.
