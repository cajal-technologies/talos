# Mergesort `func38` (absolute 41, `String::write_str`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are `(stringHeader, sourcePointer, sourceLength)`; result is writer
status.  It checks whether `length + sourceLength` fits capacity, calls
specialized reserve `func13` when necessary, copies the source bytes to the end
of the String, and increments length.

Installed at table slot three and reached only from excluded formatting.  The
append behavior and possible `func13` call are table evidence; no `ByteSlice`
to `StringValue` contract is introduced.  Time would be linear in source length
plus any reallocation copy.
