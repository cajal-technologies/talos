# Xor `func9` (absolute function 12, `std::alloc::rust_oom` closure)

## Role

Low-level indirect allocation-error dispatch.

## Behavior

Loads `(alignment, size)` from the record at its sole parameter, reads the
dispatch selector `x` at memory address `1048580`, chooses slot `x` when
`x != 0` and the default slot one when `x = 0`, calls it indirectly with type
`(i32, i32) -> ()`, and then executes `unreachable`.  Only slot one is
initialized, with `func10`, so the initial zero selector invokes that handler.

## Contract ingredients

The principal contract must state table and selector ownership explicitly and
classify both invalid custom selectors and the initialized default-handler path.
