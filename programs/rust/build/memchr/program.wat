(module $memchr.wasm
  (type (;0;) (func (param i32 i32 i32) (result i32)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 16)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048576)
  (global (;2;) i32 i32.const 1048576)
  (export "memory" (memory 0))
  (export "memchr" (func $memchr))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (func $memchr (;0;) (type 0) (param i32 i32 i32) (result i32)
    (local i32)
    i32.const 0
    local.set 3
    block ;; label = @1
      local.get 1
      i32.eqz
      br_if 0 (;@1;)
      loop ;; label = @2
        local.get 0
        local.get 3
        i32.add
        i32.load8_u
        local.get 2
        i32.eq
        br_if 1 (;@1;)
        local.get 1
        local.get 3
        i32.const 1
        i32.add
        local.tee 3
        i32.ne
        br_if 0 (;@2;)
      end
      local.get 1
      local.set 3
    end
    local.get 3
  )
  (@producers
    (language "Rust" "")
    (processed-by "rustc" "1.92.0 (ded5c06cf 2025-12-08)")
  )
  (@custom "target_features" (after code) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
)
