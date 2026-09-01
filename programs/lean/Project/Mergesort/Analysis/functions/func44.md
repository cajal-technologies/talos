# Mergesort `func44` (absolute 47, `alloc::alloc::handle_alloc_error`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are `(alignment,size)`.  It reverses them for
`func27(size,alignment)` and never returns.  It is called by `func35`,
`func40`, and `func43`.

All incoming edges are from excluded `func35`, `func40`, and `func43`.  The ABI
reversal documents their transitive allocation-error chain; no `AllocLayout`
predicate or terminal WP bridge is introduced.  Local work is constant.
