# Xor `func3` (absolute function 6, `__rust_alloc`)

## Role

Monotone bump allocator, structurally identical to ByteEcho `func2` except for
its absolute OOM call target.

## Interface and behavior

Parameters are `(size, align)` and the result is an aligned start pointer.  It
uses cursor word `1048576` or heap base `1048592`, checks all alignment/end
arithmetic and the signed-address ceiling, grows memory to the rounded-up page
count if needed, stores the new end cursor, and returns the start.  Any invalid
arithmetic or failed growth calls `func4` and traps.

## Call sites

`func0` calls it with `(2, 1)`.  In the initial state it returns `1048592`,
stores cursor `1048594`, and performs no memory growth.

## Contract ingredients

Use the same allocator abstraction and generic contract intended for ByteEcho
`func2`.  A program-specific corollary may discharge the concrete `(2, 1)`
arithmetic.  Reuse should come from a parameterized allocator theorem rather
than a false literal body-equality lemma.

## Complexity

Constant instruction count excluding a possible `memory.grow`; the public
two-byte call does not grow memory.
