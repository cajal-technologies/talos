# ByteEcho `func7` (absolute function 10, `end_short_backtrace<rust_oom>`)

## Role and behavior

Non-returning allocation-error dispatcher wrapper.  Its parameter points to an
eight-byte `Layout` record containing alignment and size.  It calls `func8(record)` and
then executes `unreachable`.

## Call sites

Called only by `func11`, which constructs the record on the shadow stack.

## Well-formed public path

Unreachable from the successful singleton-input execution; it belongs to the
null-allocation error path.

## Contract ingredients

The contract is terminal and should consume the structured `Layout` record
predicate rather than two unrelated words.
