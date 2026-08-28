# Mergesort `func24` (absolute 27, `rust_panic`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a panic payload pointer and vtable pointer.  It forwards them to
`func12` (`__rust_start_panic`), discards the nominal i32 result, and executes
`unreachable`.  `func22` is its only caller.

Its sole incoming edge is from excluded `func22`.  Forwarding to `func12` is
recorded to close the panic call graph, but neither function receives a
terminal contract.  Wrapper overhead is constant.
