# ByteEcho `func11` (absolute function 14, `std::alloc::rust_oom`)

## Role

Builds an allocation `Layout` record on the shadow stack and dispatches it.

## Inputs and low-level behavior

It receives two i32 values interpreted as alignment and size.  It subtracts
16 from mutable global 0, stores the values at offsets 8 and 12, and calls
`func7(stackPtr + 8)`.  Since the callee is non-returning, the stack pointer is
not restored.

## Call sites

Called only by `func10`.

## Contract ingredients

The main contract should use a shadow-stack predicate that supports allocating
a 16-byte frame, exposing the structured `Layout` record at offset 8, and transferring
it to `func7`.  Terminality explains why restoration is unnecessary.
