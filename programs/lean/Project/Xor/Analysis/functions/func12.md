# Xor `func12` (absolute function 15, `std::alloc::rust_oom`)

## Role

Constructs an allocation `Layout` record on a 16-byte shadow-stack frame.

## Behavior

Subtracts 16 from global 0, stores its two parameters at frame offsets 8 and
12, passes `frame + 8` to `func8`, and executes `unreachable`.  The global
stack pointer is not restored because the path is terminal.

## Contract ingredients

The main contract should allocate the frame through a reusable shadow-stack
predicate and expose an eight-byte structured `Layout` record to `func8`.
