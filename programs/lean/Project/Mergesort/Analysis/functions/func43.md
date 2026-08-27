# Mergesort `func43` (absolute 46, `alloc::raw_vec::handle_error`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters encode the RawVec error result.  A nonzero layout/alignment branch
calls `func44` (`handle_alloc_error`) with the layout; the zero/sentinel branch
calls `func45` (`capacity_overflow`).  Both callees are terminal.

`func1`, `func13`, and syntactic null checks in `func3` call it.  On the
well-formed entry path, capacity-overflow and post-allocation null edges must be
proved unreachable; allocator failure already terminates through `func6`.
The reachable incoming edges are discharged at `X-F1-ADD`, `X-F1-TAG`,
`X-F3-VALUES-NULL`, and `X-F3-SCRATCH-NULL`; `func13` is already outside the
closure.  Therefore this function receives no `RawVecError` predicate or
terminal WP theorem.  Local work is constant.
