# ByteEcho `func12` (absolute function 15, `alloc::alloc::handle_alloc_error`)

## Role and behavior

Rust allocation-failure wrapper reached when `func0` observes a null pointer.
It reverses its two layout arguments, calls `func10`, and executes
`unreachable`.

## Call sites and reachability

Called only by `func0` with `(1, 1)`.  Under a well-formed initial allocator,
the one-byte allocation returns heap base `1048592`, so this path is
unreachable for the public proof.

## Contract ingredients

It still needs one terminal main contract so that `func0`'s general contract
can account for every branch.  The singleton well-formed corollary should
discharge the branch arithmetically without invoking that contract.
