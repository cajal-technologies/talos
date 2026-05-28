(module $reverse_inplace.wasm
  (type (;0;) (func (param i32 i32)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 16)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048576)
  (global (;2;) i32 i32.const 1048576)
  (export "memory" (memory 0))
  (export "reverse_inplace" (func $reverse_inplace))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (func $reverse_inplace (;0;) (type 0) (param i32 i32)
    (local i32 i32 i32)
    block ;; label = @1
      local.get 1
      i32.const 2
      i32.lt_u
      br_if 0 (;@1;)
      local.get 1
      i32.const -1
      i32.add
      local.set 2
      local.get 1
      i32.const 2
      i32.shl
      local.get 0
      i32.add
      i32.const -4
      i32.add
      local.set 1
      i32.const 1
      local.set 3
      loop ;; label = @2
        local.get 0
        i32.load
        local.set 4
        local.get 0
        local.get 1
        i32.load
        i32.store
        local.get 1
        local.get 4
        i32.store
        local.get 0
        i32.const 4
        i32.add
        local.set 0
        local.get 1
        i32.const -4
        i32.add
        local.set 1
        local.get 3
        local.get 2
        i32.const -1
        i32.add
        local.tee 2
        i32.lt_u
        local.set 4
        local.get 3
        i32.const 1
        i32.add
        local.set 3
        local.get 4
        br_if 0 (;@2;)
      end
    end
  )
  (@producers
    (language "Rust" "")
    (processed-by "rustc" "1.92.0 (ded5c06cf 2025-12-08)")
  )
  (@custom "target_features" (after code) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
)
