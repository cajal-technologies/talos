# Mergesort `func4` (absolute 7, `__rust_no_alloc_shim_is_unstable_v2`)

Compiler allocation-shim marker with body `return`.  It has no parameters,
results, state effects, or callees.  In the valid-input proof closure its exact
direct callers are `func0` and `func3`.  Calls from the excluded runtime are
documented in the global call graph but are not call sites of this theorem.
Its main WP contract is the identity rule.  Constant time and space.

The authoritative theorem is continuation-passing and preserves every framed
resource and operand-stack suffix exactly.  There are no failure modes or
hidden memory inputs.  Its call sites need no facts beyond function resolution.
The common outcome-valued WP signature is settled, and this exact identity
contract has passed both statement directions.  It is frozen; its trivial body
proof remains behind the global phase gate.
