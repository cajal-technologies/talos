(module $is_even.wasm
  (type (;0;) (func (param i32) (result i32)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 16)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048576)
  (global (;2;) i32 i32.const 1048576)
  (export "memory" (memory 0))
  (export "is_even" (func $is_even))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (func $is_even (;0;) (type 0) (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.and
    i32.eqz
  )
)
