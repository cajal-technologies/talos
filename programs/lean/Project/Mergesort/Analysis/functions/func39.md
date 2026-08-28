# Mergesort `func39` (absolute 42, `FormatStringPayload::get`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters are a result place and format-payload pointer.  The implementation
uses `func48` (`core::fmt::write`) to render the payload through its formatting
arguments, then writes the resulting borrowed/owned representation to the
result place.

Installed at table slot 13 and used only by excluded panic dispatch.  The
tagged payload, argument array, writer vtable, and result write are documented
only to classify that dispatch; no connecting predicate or WP theorem is
introduced.  Complexity would be linear in rendered output.
