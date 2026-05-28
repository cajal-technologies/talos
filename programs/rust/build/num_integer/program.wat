(module $num_integer.wasm
  (type (;0;) (func (param i64 i64) (result i64)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 16)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048576)
  (global (;2;) i32 i32.const 1048576)
  (export "memory" (memory 0))
  (export "gcd_u64" (func $gcd_u64))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (func $gcd_u64 (;0;) (type 0) (param i64 i64) (result i64)
    (local i64 i64)
    local.get 1
    local.get 0
    i64.or
    local.set 2
    block ;; label = @1
      local.get 0
      i64.eqz
      br_if 0 (;@1;)
      local.get 1
      i64.eqz
      br_if 0 (;@1;)
      local.get 2
      i64.ctz
      local.set 3
      block ;; label = @2
        block ;; label = @3
          local.get 0
          local.get 0
          i64.ctz
          i64.shr_u
          local.tee 2
          local.get 1
          local.get 1
          i64.ctz
          i64.shr_u
          local.tee 0
          i64.ne
          br_if 0 (;@3;)
          local.get 2
          local.set 0
          br 1 (;@2;)
        end
        loop ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 2
              local.get 0
              i64.gt_u
              br_if 0 (;@5;)
              local.get 0
              local.get 2
              i64.sub
              local.tee 0
              local.get 0
              i64.ctz
              i64.shr_u
              local.set 0
              br 1 (;@4;)
            end
            local.get 2
            local.get 0
            i64.sub
            local.tee 2
            local.get 2
            i64.ctz
            i64.shr_u
            local.set 2
          end
          local.get 2
          local.get 0
          i64.ne
          br_if 0 (;@3;)
        end
      end
      local.get 0
      local.get 3
      i64.shl
      local.set 2
    end
    local.get 2
  )
)
