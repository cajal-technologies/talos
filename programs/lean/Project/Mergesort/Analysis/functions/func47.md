# Mergesort `func47` (absolute 50, `core::panicking::panic_fmt`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are formatting-arguments pointer/count and source-location pointer.
It reserves 32 stack bytes, constructs the panic-info/payload record expected
by the runtime, calls `func26` (`rust_begin_unwind`), and never returns.

All callers are excluded error-reporting helpers.  `FormatArguments`, source
location, and the fixed frame are recorded to map the panic chain; no
structured predicate or terminal WP theorem is introduced.  Local work is
constant and the frame is 32 bytes, excluding later formatting.
