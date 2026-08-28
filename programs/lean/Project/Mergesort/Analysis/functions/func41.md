# Mergesort `func41` (absolute 44, `FormatStringPayload::as_str`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a return place and payload pointer.  It inspects the payload tag
and writes the corresponding optional borrowed-string representation without
calling other functions.  It is installed at table slot 14.

Its only use is table dispatch from excluded panic formatting.  The tag split
and optional borrowed view are documentation only; no payload or `ByteSlice`
predicate is introduced.  Time and space are constant.
