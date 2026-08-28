# ByteEcho `func3` (absolute function 6, `talos_stdio::allocator::abort_oom`)

## Role and behavior

Terminal allocator OOM shim.  It calls imported `talos.oom` with no arguments
and then executes `unreachable`.

## Call sites

Called only by `func2` after invalid allocation arithmetic or failed
`memory.grow`.

## Contract ingredients

Its principal contract should establish the distinguished host trap and the
host state's OOM marker.  It has no successful continuation.  This is the
terminal alternative used by the allocator contract.
