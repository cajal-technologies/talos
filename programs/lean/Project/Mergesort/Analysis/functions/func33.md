# Mergesort `func33` (absolute 36, `StaticStrPayload::get`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a return-place pointer and payload pointer.  It writes a
two-word borrowed string view derived from the static payload into the return
place and returns normally.  It has no callees and is installed at table slot
8 for panic-payload dispatch.

It is reached only through excluded panic-payload dispatch.  The borrowed-slice
write documents the table entry; no `StaticStrPayload`/result-slot predicate or
WP theorem is introduced.  Time and space are constant.
