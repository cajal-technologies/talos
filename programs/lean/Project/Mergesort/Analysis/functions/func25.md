# Mergesort `func25` (absolute 28, `__rust_abort`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

No parameters or results.  Its only instruction is `unreachable`, so it traps
immediately.  `func12` calls it.

Its sole incoming edge is from excluded `func12`.  Although the body would
produce a Wasm `unreachable` trap, that outcome is outside the valid-input
theorem and is not specified.  Time and space are constant.
