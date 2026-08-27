# Mergesort `func48` (absolute 51, `core::fmt::write`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

## Role and loop

Parameters identify a writer object/vtable and a sequence of formatting
pieces/arguments; result is formatting status.  The function reserves 16 bytes
and iterates through the formatting bytecode:

- writes literal pieces through indirect writer `write_str`;
- dispatches argument formatters indirectly (including `func32`, `func36`, and
  `func54` through table entries);
- handles optional formatting parameters and writes trailing literals;
- exits early on a nonzero writer/formatter status.

## Exclusion evidence and complexity

Called only by the excluded panic/String formatting family.  The loop and
indirect sites are decoded to justify that classification; no
`FormatterProgram`, `Writer`, or vtable-ownership protocol is formalized.  Time
would be linear in piece/argument count plus rendered byte count; stack space
is fixed at 16 bytes.
