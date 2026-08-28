# Mergesort `func51` (absolute 54, `str::count::do_count_chars`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are byte pointer and length; result is the number of UTF-8 scalar
values.  The optimized body scans byte blocks, counts non-continuation bytes,
and handles the remaining tail without calls.  It assumes a valid UTF-8 slice
from the formatter.

Called only by excluded `func50`.  The UTF-8 assumption and returned count are
documented to understand that formatter, but no `ByteSlice` character-count
specification is introduced.  Time is linear in byte length and auxiliary
space is constant.
