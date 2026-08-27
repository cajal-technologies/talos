# Mergesort `func29` (absolute 32, `panic_count::increase`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 is a byte flag stored into global panic state.  The function:

1. increments the i32 counter at `1049520`;
2. returns classification zero if the old count was negative;
3. if the old count was nonnegative and byte `1049500` was already nonzero,
   returns classification one;
4. otherwise stores the low byte of the parameter at `1049500`, increments the
   i32 counter at `1049496`, and returns classification two.

Both i32 counter increments use wrapping Wasm addition.  The negative-old-count
branch changes only the primary counter; the class-one branch also changes only
that counter; the class-two branch changes all three named cells.

Excluded `func22` is its only caller and passes one.  The exact truth table is
retained to understand that caller; no `PanicCount` predicate or WP theorem is
introduced.  Time and space are constant.
