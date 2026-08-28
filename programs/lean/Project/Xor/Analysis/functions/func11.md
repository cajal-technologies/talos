# Xor `func11` (absolute function 14, `__rust_alloc_error_handler`)

## Role and behavior

Non-returning two-argument allocation-error wrapper.  It reverses its parameters, calls
`func12`, and then executes `unreachable`.

## Call sites

Called only by `func13`.

## Contract ingredients

Its main contract composes the terminal `func12` contract without reopening
the latter's stack-frame implementation.
