# Mergesort imported function 2 (`talos.oom`)

Type `() -> ()` syntactically, but terminal in the Universal host.  Its main
contract consumes `Streams input output raised`, returns
`Streams input output true` at the terminal outcome, and preserves every
explicitly framed program resource while producing exactly
`.host OOM.trapMessage`.  The trap consumes the exclusive current-running-
instance token, so `RuntimeContext` is intentionally absent from the terminal
post.  It is called only through `func6`, itself reached by allocator/
reallocator/zeroed-allocation failure.  This is the sole reachable non-success
terminal outcome under the entry precondition.  Its host transition is
constant-time.
