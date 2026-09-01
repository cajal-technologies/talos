# Mergesort `func32` (absolute 35, `FormatStringPayload::fmt`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a tagged format-string payload pointer and a Formatter pointer;
the i32 result is Rust's formatting status.  It inspects the payload's first
word to distinguish inline/static and allocated representations.  It either
forwards an existing byte range through `func53` (`Formatter::write_str`) or
constructs formatting arguments and calls `func48` (`core::fmt::write`).

It is installed at table slot 11 and used only by excluded panic formatting.
The payload variants and dispatches are recorded for table classification; no
Formatter protocol or WP specification is introduced.  Work would be linear
in rendered text length.
