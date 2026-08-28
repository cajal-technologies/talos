# ByteEcho `func10` (absolute function 13, `__rust_alloc_error_handler`)

## Role and behavior

Non-returning two-argument allocation-error wrapper.  It forwards its two parameters in
reversed order to `func11` and then executes `unreachable`.

## Call sites

Called only by `func12`, the allocation-failure wrapper.

## Contract ingredients

Its main contract should be a direct corollary-shaped composition of
`func11`'s terminal contract; its body is still unfolded exactly once here.
