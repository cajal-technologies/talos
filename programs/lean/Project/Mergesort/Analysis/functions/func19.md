# Mergesort `func19` (absolute 22, `end_short_backtrace<panic_handler>`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Receives a pointer to panic information, calls `func20`, and executes
`unreachable`.  It is called only by `func26` (`rust_begin_unwind`).

Its only incoming edge is from excluded `func26`.  The forwarding behavior is
recorded to identify the panic chain, but no panic-info predicate or terminal
composition theorem is introduced.  Local work is constant.
