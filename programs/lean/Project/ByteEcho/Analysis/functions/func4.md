# ByteEcho `func4` (absolute function 7, `__rust_dealloc`)

## Role and behavior

Deallocation shim for the monotone allocator.  Parameters are `(ptr, size,
align)`, but the body is empty.  It neither reclaims memory nor changes the
cursor.

## Call sites

`func0` calls it for the one-byte allocation on both the successful-read and
short-read paths.

## Contract ingredients

The main WP contract preserves the allocator state.  The chosen high-level
memory predicate must decide explicitly whether ownership of the region is
returned to the caller or absorbed as permanently allocated; callers should
not infer reclamation that the machine code does not perform.
