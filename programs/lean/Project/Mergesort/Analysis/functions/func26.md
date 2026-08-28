# Mergesort `func26` (absolute 29, `rust_begin_unwind`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 points to a 12-byte panic-info record.  The function reserves a
16-byte frame, copies an unaligned i64 from offsets 0--7 and a word from offset
8 into frame offsets 4--15, then calls `func19(frame+4)` and executes
`unreachable`.

Called only by excluded `func47`.  The fixed-frame copy is documented to map
the panic chain; it does not induce a structured panic-record predicate or WP
specification.  Local time is constant and stack use is 16 bytes.
