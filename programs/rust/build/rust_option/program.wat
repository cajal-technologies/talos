(module $rust_option.wasm
  (type (;0;) (func (param i64) (result i64)))
  (type (;1;) (func (param i64) (result i32)))
  (type (;2;) (func (param i64 i64) (result i64)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 16)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048576)
  (global (;2;) i32 i32.const 1048576)
  (export "memory" (memory 0))
  (export "filter_positive" (func $filter_positive))
  (export "is_some" (func $is_some))
  (export "map_add" (func $map_add))
  (export "or" (func $or))
  (export "unwrap_or_default" (func $unwrap_or_default))
  (export "wrap" (func $wrap))
  (export "unwrap_or" (func $or))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (func $filter_positive (;0;) (type 0) (param i64) (result i64)
    local.get 0
    i64.const -9223372036854775808
    local.get 0
    i64.const 0
    i64.gt_s
    select
  )
  (func $is_some (;1;) (type 1) (param i64) (result i32)
    local.get 0
    i64.const -9223372036854775808
    i64.ne
  )
  (func $map_add (;2;) (type 2) (param i64 i64) (result i64)
    i64.const -9223372036854775808
    local.get 1
    local.get 0
    i64.add
    local.get 0
    i64.const -9223372036854775808
    i64.eq
    select
  )
  (func $or (;3;) (type 2) (param i64 i64) (result i64)
    local.get 1
    local.get 0
    local.get 0
    i64.const -9223372036854775808
    i64.eq
    select
  )
  (func $unwrap_or_default (;4;) (type 0) (param i64) (result i64)
    i64.const 0
    local.get 0
    local.get 0
    i64.const -9223372036854775808
    i64.eq
    select
  )
  (func $wrap (;5;) (type 0) (param i64) (result i64)
    local.get 0
  )
  (@producers
    (language "Rust" "")
    (processed-by "rustc" "1.92.0 (ded5c06cf 2025-12-08)")
  )
  (@custom "target_features" (after code) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
)
