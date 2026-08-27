# Mergesort `func42` (absolute 45, `String::write_fmt`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are mutable String header plus formatting-arguments pointer and
length; result is formatting status.  It constructs the String writer view and
calls `func48` (`core::fmt::write`), whose indirect writer methods resolve to
`func37`/`func38`.

Installed at table slot five and reached only from excluded formatting.  The
vtable linkage is retained as dispatch evidence; no Formatter/String protocol
is formalized.  Complexity would be linear in rendered output, with possible
String reallocations.
