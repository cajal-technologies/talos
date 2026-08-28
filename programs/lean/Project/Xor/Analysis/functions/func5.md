# Xor `func5` (absolute function 8, `__rust_dealloc`)

## Role and behavior

No-op deallocation shim with parameters `(ptr, size, align)`.  It does not
alter memory or the bump cursor.

## Call sites

`func0` calls it after successful output and on the incomplete-input early
return.

## Contract ingredients

Its contract must preserve allocator state and accurately model the absence of
reclamation.  It should share the same high-level interface as ByteEcho
`func4`.
