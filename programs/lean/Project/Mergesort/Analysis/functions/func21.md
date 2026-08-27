# Mergesort `func21` (absolute 24, specialized `RawVecInner::finish_grow`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

This is the monomorphized String/panic-formatting analogue of `func0`, with the
same six-parameter result-place ABI and three-word success/error result.  It
checks `newCapacity * elementSize`, uses `func8` for an old allocation or
`func4`/`func5` for a fresh allocation, and writes the result object.

Only excluded `func13` calls it.  This duplicate grow implementation is not
specialized or proved because its entire String/panic-formatting caller chain
is unreachable.  Reallocation time would be linear in copied size.
