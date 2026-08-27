# Mergesort imported function 0 (`stdio.read`)

Type `(i32 length, i32 pointer) -> i32`; immediately before the direct import,
the interpreter's top-first operand list is `[pointer,length]`.  The Universal
host copies the maximal
available input prefix of length at most `length` into memory, advances input,
and returns the copied count.  `func10` translates the shim call's top-first
`[length,pointer]` into this direct-import order.

`func3` always requests 256 bytes at frame offset 12.  Hence returned count is
at most 256, ruling out its slice-index panic.  For `B` input bytes there are
`ceil(B/256)` nonempty calls and one final zero-count call.  Host work is linear
in the copied count.
