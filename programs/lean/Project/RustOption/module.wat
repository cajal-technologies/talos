(module
  (type (;0;) (func (param i64) (result i64)))
  (type (;1;) (func (param i64) (result i32)))
  (type (;2;) (func (param i64 i64) (result i64)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 16)
  (global (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048576)
  (global (;2;) i32 i32.const 1048576)
  (export "memory" (memory 0))
  (export "filter_positive" (func 0))
  (export "is_some" (func 1))
  (export "map_add" (func 2))
  (export "or" (func 3))
  (export "unwrap_or_default" (func 4))
  (export "wrap" (func 5))
  (export "unwrap_or" (func 3))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (func (;0;) (type 0) (param i64) (result i64)
    local.get 0
    i64.const -9223372036854775808
    local.get 0
    i64.const 0
    i64.gt_s
    select
  )
  (func (;1;) (type 1) (param i64) (result i32)
    local.get 0
    i64.const -9223372036854775808
    i64.ne
  )
  (func (;2;) (type 2) (param i64 i64) (result i64)
    i64.const -9223372036854775808
    local.get 1
    local.get 0
    i64.add
    local.get 0
    i64.const -9223372036854775808
    i64.eq
    select
  )
  (func (;3;) (type 2) (param i64 i64) (result i64)
    local.get 1
    local.get 0
    local.get 0
    i64.const -9223372036854775808
    i64.eq
    select
  )
  (func (;4;) (type 0) (param i64) (result i64)
    i64.const 0
    local.get 0
    local.get 0
    i64.const -9223372036854775808
    i64.eq
    select
  )
  (func (;5;) (type 0) (param i64) (result i64)
    local.get 0
  )
)
