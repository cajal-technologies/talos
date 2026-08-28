# Mergesort `func34` (absolute 37, `StaticStrPayload::as_str`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a return-place pointer and static payload pointer.  It writes
the payload's borrowed `(pointer,length)` string representation into the return
place with no allocation or calls.  It is installed at table slot 9.

It is reached only through excluded panic-payload dispatch.  The structured
record write is documentation only and receives no WP specification.  Time and
space are constant.
