# Xor `func8` (absolute function 11, `end_short_backtrace<rust_oom>`)

## Role and behavior

Non-returning allocation-error wrapper.  It forwards a pointer to an eight-byte
`Layout` record to `func9` and then executes `unreachable`.

## Call sites and reachability

Called only by `func12`.  It is unreachable on the well-formed two-byte public
path.

## Contract ingredients

Terminal contract over a structured `Layout` record and shadow-stack predicate.
