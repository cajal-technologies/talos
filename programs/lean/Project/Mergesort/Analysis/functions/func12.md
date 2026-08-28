# Mergesort `func12` (absolute 15, `__rust_start_panic`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are an opaque panic payload pointer and vtable pointer; result type
is i32 but normal return is impossible.  It calls `func25` (`__rust_abort`) and
then executes `unreachable`.  Called by `func24` (`rust_panic`).

Its only incoming edge is from excluded `func24`.  With every root into the
panic/error subgraph proved false, this abort wrapper is unreachable.  Its
local work is constant; no terminal contract is introduced.
