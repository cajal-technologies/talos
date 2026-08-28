# Xor imported function 0 (`stdio.read`)

Type `(i32, i32) -> i32`.  Through `func6`, the Universal host receives a
capacity and destination address, copies the maximal available prefix up to
that capacity, advances input, and returns the copied count.

For the well-formed exact two-byte input, the first call has capacity two,
copies both bytes, and returns two.  Complexity is linear in the returned
count.
