# Mergesort `func37` (absolute 40, `String::write_char`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a mutable String header and a Unicode scalar; result is writer
status.  It encodes the scalar as one to four UTF-8 bytes, checks spare
capacity, calls specialized reserve `func13` if needed, stores the encoded
bytes at `pointer + length`, and updates length.

Installed at table slot four for excluded Formatter output.  UTF-8 append and
its possible `func13` reserve are documented to decode the vtable, but neither
String representation nor reserve composition is formalized.  Encoding work
is constant plus a possible linear reallocation copy on the dead path.
