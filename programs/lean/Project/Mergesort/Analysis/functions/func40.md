# Mergesort `func40` (absolute 43, `FormatStringPayload::take_box`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are result place and format payload.  It renders/copies payload
state using `func48`, allocates a 12-byte boxed representation through
`func4`/`func5`, calls `func44` on the generic null branch, stores the payload
record in the allocation, and writes the boxed result tag/pointer.

Installed at table slot 12 and reachable only inside the excluded panic
subgraph.  Its tagged-payload, formatting, and allocator effects are not
composed formally.  Complexity on that dead path would be linear in
formatting/copying plus allocation.
