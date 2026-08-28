# ByteEcho `func1` (absolute function 4, `__rust_no_alloc_shim_is_unstable_v2`)

## Role and behavior

Compiler allocation-shim marker.  Its entire body is `return`; it has no
explicit parameters, results, memory accesses, or calls.

## Call sites

Called once by `func0` before allocation.

## Contract ingredients

The principal WP contract is an identity rule: every framed resource is
preserved and execution continues with no stack results.  The body should be
unfolded only in this proof.

## Complexity

Constant time and space.
