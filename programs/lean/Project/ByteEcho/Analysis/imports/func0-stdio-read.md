# ByteEcho imported function 0 (`stdio.read`)

The import has type `(i32, i32) -> i32`.  The Rust shim `func5` supplies the
requested length and buffer address in the import ABI's order.  The Universal
host copies the maximal prefix of remaining input whose length is at most the
capacity, writes it at the buffer, advances the input cursor, and returns the
copied length.  It does not manufacture short nonzero reads.

For the well-formed entry call, capacity and remaining input length are both
one, so the result is one and the supplied byte occupies the owned cell.
Complexity is linear in the copied count.
