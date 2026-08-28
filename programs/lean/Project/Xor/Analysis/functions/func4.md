# Xor `func4` (absolute function 7, `talos_stdio::allocator::abort_oom`)

## Role and behavior

Terminal OOM shim: call imported `talos.oom`, then execute `unreachable`.

## Call sites and contract

Called only by `func3`.  Its main contract establishes the distinguished host
OOM trap and marker and has no successful continuation.
