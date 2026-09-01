# Mergesort `func54` (absolute 57, unsigned-integer `Display::fmt`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are an unsigned integer pointer and Formatter pointer; result is
formatting status.  It reserves a 16-byte decimal buffer, repeatedly divides
the value into base-10,000 chunks, writes two-digit pairs from the static digit
table, handles the most significant one to four digits without leading zeros,
then calls `func50` to apply sign/prefix/padding.

Installed at table slot 17 and used only by excluded panic bounds/index
messages.  Decimal rendering is documented to classify the formatter entry;
no Formatter protocol or WP theorem is introduced.  Time would be
`Theta(number of decimal digits)` and stack use is 16 bytes.
