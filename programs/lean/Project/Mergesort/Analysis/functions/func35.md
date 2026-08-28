# Mergesort `func35` (absolute 38, `StaticStrPayload::take_box`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a result place and static-string payload.  It prepares an
eight-byte boxed payload: calls the allocation marker `func4`, allocates eight
bytes at alignment four with `func5`, reports null through `func44` if that
generic branch were taken, copies the two-word static string record, and writes
the box pointer/tag to the result place.

Installed at table slot seven and reachable only from the excluded panic
machinery.  Even though its body calls the in-scope allocator, this unreachable
caller does not receive a `BoxedStaticStr` predicate or allocator-composition
proof.  Local work is constant; the dead path could allocate or terminate OOM.
