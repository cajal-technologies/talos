# Mergesort `func20` (absolute 23, panic-handler closure)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

The parameter points to Rust panic-info/payload records.  The function reserves
16 stack bytes, decodes whether the payload contains an inline/static or boxed
message, constructs the corresponding two-word view in its frame, loads
location and payload-vtable flags, and calls `func22` (`panic_with_hook`).  Both
branches are terminal, so the stack pointer is not restored.

Called only by excluded `func19`.  Payload-tag decoding and the fixed frame are
documented to classify that edge, not to define a proof interface.  No payload
or terminal WP specification is introduced.  Local work is constant and the
frame is 16 bytes.
