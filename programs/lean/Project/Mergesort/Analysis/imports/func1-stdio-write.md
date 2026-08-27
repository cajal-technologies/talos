# Mergesort imported function 1 (`stdio.write`)

Type `(i32 length, i32 pointer) -> ()`; the direct import's top-first operand
list is `[pointer,length]`.  The Universal host reads exactly the specified byte
region and appends it to output.  `func11` translates its Rust-order shim call
into this host-import order.

`func3` calls it once per sorted `u32`, always with length four and pointer
`frame + 268`.  Each call is constant-size; aggregate output work is linear in
the number of values.  The authoritative valid-path contract therefore
requires a positive requested length: zero-length writes with no owned bytes
would not by themselves establish that an arbitrary pointer is within the
physical memory bound.
