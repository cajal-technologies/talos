# ByteEcho `func8` (absolute function 11, `std::alloc::rust_oom` closure)

## Role

Low-level indirect allocation-error dispatch.

## Inputs and effects

Parameter 0 points to two consecutive i32 words containing `(alignment,
size)`.  The function loads both, reads a dispatch selector `x` from address
`1048580`, selects table index `x` when `x != 0` and the default index one when
`x = 0`, and performs an indirect call of type `(i32, i32) -> ()`.  It then
executes `unreachable`.

Only table slot 1 is initialized, with `func9`; slot 0 is null.  The initial
zero selector therefore invokes `func9` before the explicit trap.

## Call sites

Called only by `func7`.

## Contract ingredients

The main contract must state the table/selector precondition explicitly.  A
caller may use a simpler terminal corollary for the concrete initial module.
