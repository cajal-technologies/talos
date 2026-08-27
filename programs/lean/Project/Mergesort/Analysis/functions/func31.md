# Mergesort `func31` (absolute 34, `&str::type_id`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 is a 16-byte return place; parameter 1 is unused.  It copies the
two static i64 words at `1049192` and `1049200` into that place, producing the
`TypeId` for `&str`.

Installed at table slot 15 for excluded panic-payload reflection.  The
constant write is table evidence only and receives no structured predicate or
WP theorem.  Time and space are constant.
