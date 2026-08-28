# Mergesort `func30` (absolute 33, `String::type_id`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 is a 16-byte return-place pointer; parameter 1 is unused.  It
copies two static i64 constants from addresses `1049208` and `1049216` into
return offsets 0 and 8, producing String's `TypeId`.

Installed at table slot 16 for excluded panic-payload reflection.  The exact
constant write documents that table entry only; no return-place predicate or
WP specification is introduced.  Time and space are constant.
