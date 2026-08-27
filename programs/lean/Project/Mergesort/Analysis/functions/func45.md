# Mergesort `func45` (absolute 48, `alloc::raw_vec::capacity_overflow`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

No parameters.  It passes the static `"capacity overflow"` formatting record
to `func47` (`panic_fmt`) and never returns.  Only `func43` calls it.

Its sole incoming edge is from excluded `func43`.  The capacity arithmetic
that makes this chain unreachable is discharged at reachable `func1` guards
`X-F1-ADD` and `X-F1-TAG`, not inside this function.  The static
message/location are documentation only and receive no predicates or terminal
theorem.  Local work before panic formatting is constant.
