# Mergesort `func22` (absolute 25, `std::panicking::panic_with_hook`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

## Low-level behavior

Five parameters describe a panic payload, payload vtable, location, and two
flags.  It reserves a 32-byte frame and calls `func29(1)` to increment/classify
the panic count.  Depending on that result and global hook cells, it may:

- obtain payload text through a vtable call at offset 20;
- construct a hook argument in frame offsets 8--29;
- invoke a configured hook through its vtable;
- invoke the payload's display/as-string method through offset 24;
- drop an optional temporary Vec with `func14`;
- finish with `func24` (`rust_panic`).

Every path is non-returning.  Invalid nested-panic states jump directly to the
terminal branch.

## Exclusion evidence

Called only by excluded `func20`.  Panic count, hook, payload-vtable, temporary
buffer, and stack-frame details are recorded only to identify its non-returning
subgraph.  No predicates or terminal WP specification are introduced.
Complexity would depend on hook/payload formatting; local control flow is
fixed.
