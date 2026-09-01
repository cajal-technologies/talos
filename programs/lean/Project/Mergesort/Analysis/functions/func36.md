# Mergesort `func36` (absolute 39, `StaticStrPayload::fmt`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are static payload and Formatter pointers; result is formatting
status.  It extracts the static `(pointer,length)` string and calls `func53`
(`Formatter::write_str`).  It is installed at table slot 6.

Its only use is table dispatch from excluded formatting code.  The adapter
behavior is exclusion evidence, not a `StaticStrPayload`/Formatter proof
interface.  Complexity would be linear in string length.
