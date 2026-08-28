# Mergesort `func15` (absolute 18, drop `String`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 points to a three-word String/RawVec representation.  It loads the
capacity word; when nonzero it loads the allocation pointer at offset four and
calls `func7(pointer, capacity, 1)`.  With zero capacity it returns directly.

The only executable incoming edge is table slot two from excluded panic
formatting.  Its body would pass a present allocation to `func7`, but that
effect is documentation only.  No String predicate or WP specification is
needed; time and space are constant.
