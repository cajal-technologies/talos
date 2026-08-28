# ByteEcho `func5` (absolute function 8, `talos_stdio::read`)

## Role

Thin adapter from Rust's standard-I/O ABI to imported `stdio.read`.

## Interface and behavior

- Parameters: buffer pointer and capacity.
- Result: number of bytes read.
- Implicit input/output: standard-input cursor and the writable memory region.

The function reverses the two stack arguments to match the host import ABI and
calls absolute function 0.  It performs no other computation.

## Call sites

`func0` calls it with the owned one-byte allocation and capacity one.

## Contract ingredients

Its single main contract should be the reusable bridge from a writable-region
predicate to the host read relation: the count is at most capacity, memory is
updated with exactly the consumed prefix, unfilled suffix ownership remains,
and host input advances by that prefix.
