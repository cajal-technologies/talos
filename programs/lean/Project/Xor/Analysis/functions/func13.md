# Xor `func13` (absolute function 16, `alloc::alloc::handle_alloc_error`)

## Role and behavior

Rust allocation-failure wrapper.  It reverses its two layout parameters,
calls `func11`, and executes `unreachable`.

## Call sites and reachability

Called only by `func0` with `(align = 1, size = 2)` after a null allocator
result.  The concrete well-formed initial allocator returns nonzero, so this
branch is unreachable in the public two-byte proof.

## Contract ingredients

It needs a terminal main contract for completeness, while the public
well-formed corollary should eliminate its call site using allocator facts.
