# Xor `func6` (absolute function 9, `talos_stdio::read`)

## Role and interface

Standard-input adapter with parameters `(ptr, capacity)` and a returned byte
count.  It reverses the parameters for imported `stdio.read` and otherwise has
no body logic.

## Call sites

The `func0` loop calls it on the unfilled suffix:
`(ptr + filled, 2 - filled)`.

## Contract ingredients

The main contract must provide `count <= capacity`, update exactly the first
`count` bytes of the supplied writable region, and advance host input by the
same bytes.  These facts are precisely what prevents the caller's `filled`
counter from overshooting two.
