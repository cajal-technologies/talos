# Mergesort `func18` (absolute 21, `std::alloc::rust_oom` closure)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameter 0 points to two Layout words `(alignment,size)`.  It loads them and a
handler selector `x` from memory address `1049504`; it chooses table index `x`
when nonzero and the default slot one when zero.  It calls the selected
`(i32,i32)->()` handler and then executes `unreachable`.

The initial zero selector therefore invokes `func23`, the default allocation
error hook.  Its only incoming edge is from excluded `func17`; selector and
table behavior are retained solely to document the transitive error subgraph.
No Layout/table contract is required.  Work before dispatch is constant.
