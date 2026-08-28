# Xor `func2` (absolute function 5, `__rust_no_alloc_shim_is_unstable_v2`)

## Role and behavior

Compiler allocation-shim marker with body `return`.  No parameters, results,
calls, or state changes.

## Call sites and contract

Called once by `func0` before allocation.  Its main WP contract is the identity
rule preserving every framed resource.

## Complexity

Constant time and space.
