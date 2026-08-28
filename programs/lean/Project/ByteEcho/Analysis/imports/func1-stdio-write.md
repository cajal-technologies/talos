# ByteEcho imported function 1 (`stdio.write`)

The import has type `(i32, i32) -> ()`.  `func6` supplies a length and source
address in host ABI order.  The Universal host reads exactly that many bytes
from linear memory and appends them, in order, to its output stream.

On the well-formed path the region is the one-byte allocation and the length
is one.  Complexity is linear in the written length.
