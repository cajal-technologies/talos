# Mergesort `func13` (absolute 16, specialized `RawVec::reserve`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Specialized reserve implementation used for `String`/panic formatting.  Its
five parameters have the same logical roles as `func1`; it computes required
and geometric capacity in a 16-byte frame, calls specialized grow `func21`,
updates the header on success, and calls `func43` on capacity/allocation error.

Its only calls originate from excluded `func37` and `func38` in panic
formatting.  Once the reachable roots into that subgraph are false, this
specialized reserve is unreachable and needs no allocator contract.  Local
arithmetic is constant; reallocation copy would be linear in old size.
