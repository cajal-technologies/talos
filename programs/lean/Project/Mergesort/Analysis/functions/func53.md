# Mergesort `func53` (absolute 56, `Formatter::write_str`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are Formatter, string pointer, and length; result is writer status.
It loads the underlying writer object/vtable from the Formatter and calls its
indirect `write_str` method.  `func32` and `func36` call it.

Its callers `func32` and `func36` are excluded, and its indirect writer target
lies in the same excluded formatting subgraph.  No Formatter/Writer predicate
or preservation theorem is introduced.  Dispatch overhead is constant plus
time linear in string length.
