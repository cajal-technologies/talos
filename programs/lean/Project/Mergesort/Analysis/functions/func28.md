# Mergesort `func28` (absolute 31, `std::alloc::rust_oom`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters `(alignment,size)` are materialized as an eight-byte `Layout` at
offset eight of a newly reserved 16-byte frame.  The function calls
`func17(frame+8)` and never restores the frame because execution is terminal.

Called only by excluded `func27`.  The Layout materialization and stack use are
documentation for the generic allocation-error chain, not a formal bridge.
Local time is constant and stack use is 16 bytes.
