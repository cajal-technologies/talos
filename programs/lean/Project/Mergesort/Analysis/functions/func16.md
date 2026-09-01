# Mergesort `func16` (absolute 19, drop `FormatStringPayload`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 points to a payload whose first word is an allocation
capacity/discriminant.  Values below one are inline/sentinel variants and need
no action.  Otherwise it loads the pointer at offset four and calls
`func7(pointer, capacity, 1)`.

It is installed at table slot 10 for excluded panic-payload destruction and
has no reachable direct caller.  The optional retirement effect is recorded
above only to classify the table edge.  No payload predicate or WP
specification is introduced; local time is constant.
