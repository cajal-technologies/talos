# Mergesort `func50` (absolute 53, `Formatter::pad_integral`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Six parameters describe Formatter, sign/prefix flags, prefix string, digit
pointer, and digit length; result is formatting status.  It counts UTF-8
characters through `func51`, computes left/right/zero padding from Formatter
flags and width, emits fill characters through indirect writer calls, emits
sign/prefix through `func52`, and writes digits through indirect `write_str`.

Only excluded `func54` calls it.  Padding and vtable behavior are documented
for the formatting subgraph; no logical rendering/Writer contract is
introduced.  Time would be linear in digits plus padding with constant local
space.
