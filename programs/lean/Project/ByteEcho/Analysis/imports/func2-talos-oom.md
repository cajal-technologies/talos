# ByteEcho imported function 2 (`talos.oom`)

The import has type `() -> ()` at the Wasm type level but is terminal in the
Universal host: it sets the typed OOM marker and returns the distinguished
host trap reason.  It is called only through `func3` after allocator failure.

The one-byte well-formed entry precondition proves this import unreachable.
Its host transition has constant complexity.
