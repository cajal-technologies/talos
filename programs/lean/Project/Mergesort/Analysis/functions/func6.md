# Mergesort `func6` (absolute 9, `talos_stdio::allocator::abort_oom`)

Calls imported `talos.oom` and then executes `unreachable`.  It is called only
by `func5`, `func8`, and `func9` after allocator failure.  Its sole main
contract owns `Streams input output oomRaised` and is terminal: establish the
exact host OOM trap and `Streams input output true`, with no normal
continuation.  Constant local work.

Under the exact Universal environment, the import transition traps, so the
following Wasm `unreachable` instruction is never stepped.  All explicitly
owned memory, heap, live-block, stack, and stream input/output resources are
framed; only `oom.raised` changes to true.  The trap consumes the exclusive
current-running-instance token, so the terminal continuation correctly omits
`RuntimeContext`.  The authoritative statement exposes the remaining framed
resources at that exact continuation rather than proving only an unlabelled
stuck state.
