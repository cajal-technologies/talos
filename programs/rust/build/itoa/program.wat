(module $itoa.wasm
  (type (;0;) (func (param i32 i32)))
  (type (;1;) (func (param i32 i32 i32) (result i32)))
  (type (;2;) (func (param i32 i32) (result i32)))
  (type (;3;) (func (param i32 i32 i64)))
  (type (;4;) (func (param i64 i32 i32) (result i32)))
  (type (;5;) (func (param i64) (result i32)))
  (type (;6;) (func (param i32 i32 i32)))
  (type (;7;) (func (param i32 i32 i32 i32) (result i32)))
  (type (;8;) (func (result i32)))
  (type (;9;) (func))
  (type (;10;) (func (param i64 i32) (result i32)))
  (type (;11;) (func (param i32 i32 i32 i32)))
  (type (;12;) (func (param i32) (result i32)))
  (type (;13;) (func (param i32)))
  (type (;14;) (func (param i32 i32 i32 i32 i32)))
  (type (;15;) (func (param i32 i32 i32 i32 i32 i32)))
  (type (;16;) (func (param i32 i32 i32 i32 i32 i32) (result i32)))
  (type (;17;) (func (param i32 i32 i32 i32 i32) (result i32)))
  (table (;0;) 18 18 funcref)
  (memory (;0;) 17)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1050136)
  (global (;2;) i32 i32.const 1050144)
  (export "memory" (memory 0))
  (export "itoa_i64" (func $itoa_i64))
  (export "itoa_i64_len" (func $itoa_i64_len))
  (export "itoa_u64" (func $itoa_u64))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (elem (;0;) (i32.const 1) func $_ZN3std5alloc24default_alloc_error_hook17h4789bd729e081a35E $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u32$GT$3fmt17h959da39f0c36984eE $_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17ha04294fd91816487E $_ZN58_$LT$alloc..string..String$u20$as$u20$core..fmt..Write$GT$9write_str17he8b31b395be857d0E $_ZN58_$LT$alloc..string..String$u20$as$u20$core..fmt..Write$GT$10write_char17ha4fad37ffa3383adE $_ZN4core3fmt5Write9write_fmt17hcdb9918cbf030b79E $_ZN86_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..fmt..Display$GT$3fmt17hd11db1273e797870E $_ZN93_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$8take_box17hc8b72e339dd81ae0E $_ZN93_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$3get17h7f48818314d9168cE $_ZN93_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$6as_str17hc17d597821cf031dE $_ZN4core3ptr71drop_in_place$LT$std..panicking..panic_handler..FormatStringPayload$GT$17h15618c514526fd50E $_ZN89_$LT$std..panicking..panic_handler..FormatStringPayload$u20$as$u20$core..fmt..Display$GT$3fmt17he4328ebb258ee506E $_ZN96_$LT$std..panicking..panic_handler..FormatStringPayload$u20$as$u20$core..panic..PanicPayload$GT$8take_box17h053d6b7c04e3df4dE $_ZN96_$LT$std..panicking..panic_handler..FormatStringPayload$u20$as$u20$core..panic..PanicPayload$GT$3get17h0c13fdf90f4d99c7E $_ZN4core5panic12PanicPayload6as_str17h23c66d29e6d02f31E $_ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h8c2ff05d5ddcfd57E $_ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h5b60737a5bd77be9E)
  (func $_ZN4itoa6Buffer6format17hffaed6e9cc606d30E (;0;) (type 3) (param i32 i32 i64)
    (local i32 i64 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 2
    local.get 2
    i64.const 63
    i64.shr_s
    local.tee 4
    i64.xor
    local.get 4
    i64.sub
    local.get 1
    call $_ZN38_$LT$u64$u20$as$u20$itoa..Unsigned$GT$3fmt17h2508595827681c71E
    local.set 5
    block ;; label = @1
      block ;; label = @2
        local.get 2
        i64.const -1
        i64.gt_s
        br_if 0 (;@2;)
        local.get 5
        i32.const -1
        i32.add
        local.tee 5
        i32.const 19
        i32.gt_u
        br_if 1 (;@1;)
        local.get 1
        local.get 5
        i32.add
        i32.const 45
        i32.store8
      end
      local.get 3
      i32.const 8
      i32.add
      local.get 1
      i32.const 20
      local.get 5
      call $_ZN4itoa19slice_buffer_to_str17h40012cd411ec62f2E
      local.get 3
      i32.load offset=12
      local.set 1
      local.get 0
      local.get 3
      i32.load offset=8
      i32.store
      local.get 0
      local.get 1
      i32.store offset=4
      local.get 3
      i32.const 16
      i32.add
      global.set $__stack_pointer
      return
    end
    local.get 5
    i32.const 20
    i32.const 1048772
    call $_ZN4core9panicking18panic_bounds_check17h62ab6f5933ba978dE
    unreachable
  )
  (func $itoa_i64 (;1;) (type 4) (param i64 i32 i32) (result i32)
    (local i32 i32 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 3
    i32.const 8
    i32.add
    local.get 0
    call $_ZN4itoa6Buffer6format17hffaed6e9cc606d30E
    i32.const -1
    local.set 4
    block ;; label = @1
      local.get 3
      i32.load offset=4
      local.tee 5
      local.get 2
      i32.gt_s
      br_if 0 (;@1;)
      block ;; label = @2
        local.get 5
        i32.eqz
        br_if 0 (;@2;)
        local.get 1
        local.get 3
        i32.load
        local.get 5
        memory.copy
      end
      local.get 5
      local.set 4
    end
    local.get 3
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get 4
  )
  (func $itoa_i64_len (;2;) (type 5) (param i64) (result i32)
    (local i32 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee 1
    global.set $__stack_pointer
    local.get 1
    local.get 1
    i32.const 8
    i32.add
    local.get 0
    call $_ZN4itoa6Buffer6format17hffaed6e9cc606d30E
    local.get 1
    i32.load offset=4
    local.set 2
    local.get 1
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get 2
  )
  (func $itoa_u64 (;3;) (type 4) (param i64 i32 i32) (result i32)
    (local i32 i32 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 3
    i32.const 8
    i32.add
    i32.const 20
    local.get 0
    local.get 3
    i32.const 8
    i32.add
    call $_ZN38_$LT$u64$u20$as$u20$itoa..Unsigned$GT$3fmt17h2508595827681c71E
    call $_ZN4itoa19slice_buffer_to_str17h40012cd411ec62f2E
    i32.const -1
    local.set 4
    block ;; label = @1
      local.get 3
      i32.load offset=4
      local.tee 5
      local.get 2
      i32.gt_s
      br_if 0 (;@1;)
      block ;; label = @2
        local.get 5
        i32.eqz
        br_if 0 (;@2;)
        local.get 1
        local.get 3
        i32.load
        local.get 5
        memory.copy
      end
      local.get 5
      local.set 4
    end
    local.get 3
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get 4
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc12___rust_alloc (;4;) (type 2) (param i32 i32) (result i32)
    local.get 0
    local.get 1
    call $_RNvCsiGVaDesi5rv_7___rustc11___rdl_alloc
    return
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc14___rust_dealloc (;5;) (type 6) (param i32 i32 i32)
    local.get 0
    local.get 1
    local.get 2
    call $_RNvCsiGVaDesi5rv_7___rustc13___rdl_dealloc
    return
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc14___rust_realloc (;6;) (type 7) (param i32 i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    call $_RNvCsiGVaDesi5rv_7___rustc13___rdl_realloc
    return
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc42___rust_alloc_error_handler_should_panic_v2 (;7;) (type 8) (result i32)
    i32.const 0
    return
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc35___rust_no_alloc_shim_is_unstable_v2 (;8;) (type 9)
    return
  )
  (func $_ZN38_$LT$u64$u20$as$u20$itoa..Unsigned$GT$3fmt17h2508595827681c71E (;9;) (type 10) (param i64 i32) (result i32)
    (local i32 i64 i32 i64 i32 i32 i32)
    i32.const 20
    local.set 2
    local.get 0
    local.set 3
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 0
          i64.const 1000
          i64.lt_u
          br_if 0 (;@3;)
          i32.const 20
          local.set 4
          local.get 0
          local.set 5
          loop ;; label = @4
            local.get 4
            i32.const -4
            i32.add
            local.tee 2
            i32.const 20
            i32.ge_u
            br_if 2 (;@2;)
            local.get 1
            local.get 4
            i32.add
            local.tee 4
            i32.const -3
            i32.add
            local.get 5
            local.get 5
            i64.const 10000
            i64.div_u
            local.tee 3
            i64.const 10000
            i64.mul
            i64.sub
            i32.wrap_i64
            local.tee 6
            i32.const 5243
            i32.mul
            i32.const 19
            i32.shr_u
            local.tee 7
            i32.const 1
            i32.shl
            local.tee 8
            i32.load8_u offset=1048805
            i32.store8
            local.get 4
            i32.const -4
            i32.add
            local.get 8
            i32.load8_u offset=1048804
            i32.store8
            local.get 4
            i32.const -1
            i32.add
            local.get 7
            i32.const -100
            i32.mul
            local.get 6
            i32.add
            i32.const 1
            i32.shl
            local.tee 6
            i32.load8_u offset=1048805
            i32.store8
            local.get 4
            i32.const -2
            i32.add
            local.get 6
            i32.load8_u offset=1048804
            i32.store8
            local.get 5
            i64.const 9999999
            i64.gt_u
            local.set 6
            local.get 2
            local.set 4
            local.get 3
            local.set 5
            local.get 6
            br_if 0 (;@4;)
          end
        end
        block ;; label = @3
          local.get 3
          i64.const 10
          i64.ge_u
          br_if 0 (;@3;)
          local.get 2
          local.set 4
          br 2 (;@1;)
        end
        block ;; label = @3
          local.get 2
          i32.const -2
          i32.add
          local.tee 4
          i32.const 20
          i32.ge_u
          br_if 0 (;@3;)
          local.get 1
          local.get 2
          i32.add
          i32.const -1
          i32.add
          local.get 3
          i32.wrap_i64
          local.tee 2
          i32.const 5243
          i32.mul
          i32.const 19
          i32.shr_u
          local.tee 6
          i32.const -100
          i32.mul
          local.get 2
          i32.add
          i32.const 1
          i32.shl
          local.tee 2
          i32.load8_u offset=1048805
          i32.store8
          local.get 1
          local.get 4
          i32.add
          local.get 2
          i32.load8_u offset=1048804
          i32.store8
          local.get 6
          i64.extend_i32_u
          local.set 3
          br 2 (;@1;)
        end
        local.get 4
        i32.const 20
        i32.const 1048788
        call $_ZN4core9panicking18panic_bounds_check17h62ab6f5933ba978dE
        unreachable
      end
      i32.const -4
      i32.const 20
      i32.const 1048788
      call $_ZN4core9panicking18panic_bounds_check17h62ab6f5933ba978dE
      unreachable
    end
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 0
          i64.eqz
          br_if 0 (;@3;)
          local.get 3
          i64.const 0
          i64.eq
          br_if 1 (;@2;)
        end
        local.get 4
        i32.const -1
        i32.add
        local.tee 4
        i32.const 20
        i32.ge_u
        br_if 1 (;@1;)
        local.get 1
        local.get 4
        i32.add
        local.get 3
        i32.wrap_i64
        i32.const 48
        i32.or
        i32.store8
      end
      local.get 4
      return
    end
    i32.const -1
    i32.const 20
    i32.const 1048788
    call $_ZN4core9panicking18panic_bounds_check17h62ab6f5933ba978dE
    unreachable
  )
  (func $_ZN4itoa19slice_buffer_to_str17h40012cd411ec62f2E (;10;) (type 11) (param i32 i32 i32 i32)
    local.get 0
    local.get 2
    local.get 3
    i32.sub
    i32.store offset=4
    local.get 0
    local.get 1
    local.get 3
    i32.add
    i32.store
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc18___rust_start_panic (;11;) (type 2) (param i32 i32) (result i32)
    call $_RNvCsiGVaDesi5rv_7___rustc12___rust_abort
    unreachable
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc10rust_panic (;12;) (type 0) (param i32 i32)
    local.get 0
    local.get 1
    call $_RNvCsiGVaDesi5rv_7___rustc18___rust_start_panic
    drop
    unreachable
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc11___rdl_alloc (;13;) (type 2) (param i32 i32) (result i32)
    block ;; label = @1
      local.get 1
      i32.const 9
      i32.lt_u
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$8memalign17h5ffef2f2481bdd36E
      return
    end
    local.get 0
    call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$6malloc17h44b8dc71ab434912E
  )
  (func $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$8memalign17h5ffef2f2481bdd36E (;14;) (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32)
    i32.const 0
    local.set 2
    block ;; label = @1
      local.get 1
      i32.const -65587
      local.get 0
      i32.const 16
      local.get 0
      i32.const 16
      i32.gt_u
      select
      local.tee 0
      i32.sub
      i32.ge_u
      br_if 0 (;@1;)
      local.get 0
      i32.const 16
      local.get 1
      i32.const 11
      i32.add
      i32.const -8
      i32.and
      local.get 1
      i32.const 11
      i32.lt_u
      select
      local.tee 3
      i32.add
      i32.const 12
      i32.add
      call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$6malloc17h44b8dc71ab434912E
      local.tee 1
      i32.eqz
      br_if 0 (;@1;)
      local.get 1
      i32.const -8
      i32.add
      local.set 2
      block ;; label = @2
        block ;; label = @3
          local.get 0
          i32.const -1
          i32.add
          local.tee 4
          local.get 1
          i32.and
          br_if 0 (;@3;)
          local.get 2
          local.set 0
          br 1 (;@2;)
        end
        local.get 1
        i32.const -4
        i32.add
        local.tee 5
        i32.load
        local.tee 6
        i32.const -8
        i32.and
        local.get 4
        local.get 1
        i32.add
        i32.const 0
        local.get 0
        i32.sub
        i32.and
        i32.const -8
        i32.add
        local.tee 1
        i32.const 0
        local.get 0
        local.get 1
        local.get 2
        i32.sub
        i32.const 16
        i32.gt_u
        select
        i32.add
        local.tee 0
        local.get 2
        i32.sub
        local.tee 1
        i32.sub
        local.set 4
        block ;; label = @3
          local.get 6
          i32.const 3
          i32.and
          i32.eqz
          br_if 0 (;@3;)
          local.get 0
          local.get 4
          local.get 0
          i32.load offset=4
          i32.const 1
          i32.and
          i32.or
          i32.const 2
          i32.or
          i32.store offset=4
          local.get 0
          local.get 4
          i32.add
          local.tee 4
          local.get 4
          i32.load offset=4
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 5
          local.get 1
          local.get 5
          i32.load
          i32.const 1
          i32.and
          i32.or
          i32.const 2
          i32.or
          i32.store
          local.get 2
          local.get 1
          i32.add
          local.tee 4
          local.get 4
          i32.load offset=4
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 2
          local.get 1
          call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$13dispose_chunk17hef6ec97b6fbd28fdE
          br 1 (;@2;)
        end
        local.get 2
        i32.load
        local.set 2
        local.get 0
        local.get 4
        i32.store offset=4
        local.get 0
        local.get 2
        local.get 1
        i32.add
        i32.store
      end
      block ;; label = @2
        local.get 0
        i32.load offset=4
        local.tee 1
        i32.const 3
        i32.and
        i32.eqz
        br_if 0 (;@2;)
        local.get 1
        i32.const -8
        i32.and
        local.tee 2
        local.get 3
        i32.const 16
        i32.add
        i32.le_u
        br_if 0 (;@2;)
        local.get 0
        local.get 3
        local.get 1
        i32.const 1
        i32.and
        i32.or
        i32.const 2
        i32.or
        i32.store offset=4
        local.get 0
        local.get 3
        i32.add
        local.tee 1
        local.get 2
        local.get 3
        i32.sub
        local.tee 3
        i32.const 3
        i32.or
        i32.store offset=4
        local.get 0
        local.get 2
        i32.add
        local.tee 2
        local.get 2
        i32.load offset=4
        i32.const 1
        i32.or
        i32.store offset=4
        local.get 1
        local.get 3
        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$13dispose_chunk17hef6ec97b6fbd28fdE
      end
      local.get 0
      i32.const 8
      i32.add
      local.set 2
    end
    local.get 2
  )
  (func $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$6malloc17h44b8dc71ab434912E (;15;) (type 12) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 1
    global.set $__stack_pointer
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                local.get 0
                i32.const 245
                i32.lt_u
                br_if 0 (;@6;)
                block ;; label = @7
                  local.get 0
                  i32.const -65588
                  i32.le_u
                  br_if 0 (;@7;)
                  i32.const 0
                  local.set 0
                  br 6 (;@1;)
                end
                local.get 0
                i32.const 11
                i32.add
                local.tee 2
                i32.const -8
                i32.and
                local.set 3
                i32.const 0
                i32.load offset=1050068
                local.tee 4
                i32.eqz
                br_if 4 (;@2;)
                i32.const 31
                local.set 5
                block ;; label = @7
                  local.get 0
                  i32.const 16777204
                  i32.gt_u
                  br_if 0 (;@7;)
                  local.get 3
                  i32.const 38
                  local.get 2
                  i32.const 8
                  i32.shr_u
                  i32.clz
                  local.tee 0
                  i32.sub
                  i32.shr_u
                  i32.const 1
                  i32.and
                  local.get 0
                  i32.const 1
                  i32.shl
                  i32.sub
                  i32.const 62
                  i32.add
                  local.set 5
                end
                i32.const 0
                local.get 3
                i32.sub
                local.set 2
                block ;; label = @7
                  local.get 5
                  i32.const 2
                  i32.shl
                  i32.const 1049656
                  i32.add
                  i32.load
                  local.tee 6
                  br_if 0 (;@7;)
                  i32.const 0
                  local.set 7
                  i32.const 0
                  local.set 0
                  br 2 (;@5;)
                end
                i32.const 0
                local.set 7
                local.get 3
                i32.const 0
                i32.const 25
                local.get 5
                i32.const 1
                i32.shr_u
                i32.sub
                local.get 5
                i32.const 31
                i32.eq
                select
                i32.shl
                local.set 8
                i32.const 0
                local.set 0
                loop ;; label = @7
                  block ;; label = @8
                    local.get 6
                    local.tee 6
                    i32.load offset=4
                    i32.const -8
                    i32.and
                    local.tee 9
                    local.get 3
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 9
                    local.get 3
                    i32.sub
                    local.tee 9
                    local.get 2
                    i32.ge_u
                    br_if 0 (;@8;)
                    local.get 6
                    local.set 7
                    local.get 9
                    local.set 2
                    local.get 9
                    br_if 0 (;@8;)
                    i32.const 0
                    local.set 2
                    local.get 6
                    local.set 0
                    local.get 6
                    local.set 7
                    br 4 (;@4;)
                  end
                  local.get 6
                  i32.load offset=20
                  local.tee 9
                  local.get 0
                  local.get 9
                  local.get 6
                  local.get 8
                  i32.const 29
                  i32.shr_u
                  i32.const 4
                  i32.and
                  i32.add
                  i32.load offset=16
                  local.tee 6
                  i32.ne
                  select
                  local.get 0
                  local.get 9
                  select
                  local.set 0
                  local.get 8
                  i32.const 1
                  i32.shl
                  local.set 8
                  local.get 6
                  i32.eqz
                  br_if 2 (;@5;)
                  br 0 (;@7;)
                end
              end
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          i32.const 0
                          i32.load offset=1050064
                          local.tee 6
                          i32.const 16
                          local.get 0
                          i32.const 11
                          i32.add
                          i32.const 504
                          i32.and
                          local.get 0
                          i32.const 11
                          i32.lt_u
                          select
                          local.tee 3
                          i32.const 3
                          i32.shr_u
                          local.tee 2
                          i32.shr_u
                          local.tee 0
                          i32.const 3
                          i32.and
                          i32.eqz
                          br_if 0 (;@11;)
                          local.get 0
                          i32.const -1
                          i32.xor
                          i32.const 1
                          i32.and
                          local.get 2
                          i32.add
                          local.tee 8
                          i32.const 3
                          i32.shl
                          local.tee 3
                          i32.const 1049800
                          i32.add
                          local.tee 0
                          local.get 3
                          i32.const 1049808
                          i32.add
                          i32.load
                          local.tee 2
                          i32.load offset=8
                          local.tee 7
                          i32.eq
                          br_if 1 (;@10;)
                          local.get 7
                          local.get 0
                          i32.store offset=12
                          local.get 0
                          local.get 7
                          i32.store offset=8
                          br 2 (;@9;)
                        end
                        local.get 3
                        i32.const 0
                        i32.load offset=1050072
                        i32.le_u
                        br_if 8 (;@2;)
                        local.get 0
                        br_if 2 (;@8;)
                        i32.const 0
                        i32.load offset=1050068
                        local.tee 0
                        i32.eqz
                        br_if 8 (;@2;)
                        local.get 0
                        i32.ctz
                        i32.const 2
                        i32.shl
                        i32.const 1049656
                        i32.add
                        i32.load
                        local.tee 6
                        i32.load offset=4
                        i32.const -8
                        i32.and
                        local.get 3
                        i32.sub
                        local.set 2
                        local.get 6
                        local.set 7
                        loop ;; label = @11
                          block ;; label = @12
                            local.get 7
                            i32.load offset=16
                            local.tee 0
                            br_if 0 (;@12;)
                            local.get 7
                            i32.load offset=20
                            local.tee 0
                            br_if 0 (;@12;)
                            local.get 6
                            i32.load offset=24
                            local.set 5
                            block ;; label = @13
                              block ;; label = @14
                                block ;; label = @15
                                  local.get 6
                                  i32.load offset=12
                                  local.tee 0
                                  local.get 6
                                  i32.ne
                                  br_if 0 (;@15;)
                                  local.get 6
                                  i32.const 20
                                  i32.const 16
                                  local.get 6
                                  i32.load offset=20
                                  local.tee 0
                                  select
                                  i32.add
                                  i32.load
                                  local.tee 7
                                  br_if 1 (;@14;)
                                  i32.const 0
                                  local.set 0
                                  br 2 (;@13;)
                                end
                                local.get 6
                                i32.load offset=8
                                local.tee 7
                                local.get 0
                                i32.store offset=12
                                local.get 0
                                local.get 7
                                i32.store offset=8
                                br 1 (;@13;)
                              end
                              local.get 6
                              i32.const 20
                              i32.add
                              local.get 6
                              i32.const 16
                              i32.add
                              local.get 0
                              select
                              local.set 8
                              loop ;; label = @14
                                local.get 8
                                local.set 9
                                local.get 7
                                local.tee 0
                                i32.const 20
                                i32.add
                                local.get 0
                                i32.const 16
                                i32.add
                                local.get 0
                                i32.load offset=20
                                local.tee 7
                                select
                                local.set 8
                                local.get 0
                                i32.const 20
                                i32.const 16
                                local.get 7
                                select
                                i32.add
                                i32.load
                                local.tee 7
                                br_if 0 (;@14;)
                              end
                              local.get 9
                              i32.const 0
                              i32.store
                            end
                            local.get 5
                            i32.eqz
                            br_if 6 (;@6;)
                            block ;; label = @13
                              block ;; label = @14
                                local.get 6
                                local.get 6
                                i32.load offset=28
                                i32.const 2
                                i32.shl
                                i32.const 1049656
                                i32.add
                                local.tee 7
                                i32.load
                                i32.eq
                                br_if 0 (;@14;)
                                block ;; label = @15
                                  local.get 5
                                  i32.load offset=16
                                  local.get 6
                                  i32.eq
                                  br_if 0 (;@15;)
                                  local.get 5
                                  local.get 0
                                  i32.store offset=20
                                  local.get 0
                                  br_if 2 (;@13;)
                                  br 9 (;@6;)
                                end
                                local.get 5
                                local.get 0
                                i32.store offset=16
                                local.get 0
                                br_if 1 (;@13;)
                                br 8 (;@6;)
                              end
                              local.get 7
                              local.get 0
                              i32.store
                              local.get 0
                              i32.eqz
                              br_if 6 (;@7;)
                            end
                            local.get 0
                            local.get 5
                            i32.store offset=24
                            block ;; label = @13
                              local.get 6
                              i32.load offset=16
                              local.tee 7
                              i32.eqz
                              br_if 0 (;@13;)
                              local.get 0
                              local.get 7
                              i32.store offset=16
                              local.get 7
                              local.get 0
                              i32.store offset=24
                            end
                            local.get 6
                            i32.load offset=20
                            local.tee 7
                            i32.eqz
                            br_if 6 (;@6;)
                            local.get 0
                            local.get 7
                            i32.store offset=20
                            local.get 7
                            local.get 0
                            i32.store offset=24
                            br 6 (;@6;)
                          end
                          local.get 0
                          i32.load offset=4
                          i32.const -8
                          i32.and
                          local.get 3
                          i32.sub
                          local.tee 7
                          local.get 2
                          local.get 7
                          local.get 2
                          i32.lt_u
                          local.tee 7
                          select
                          local.set 2
                          local.get 0
                          local.get 6
                          local.get 7
                          select
                          local.set 6
                          local.get 0
                          local.set 7
                          br 0 (;@11;)
                        end
                      end
                      i32.const 0
                      local.get 6
                      i32.const -2
                      local.get 8
                      i32.rotl
                      i32.and
                      i32.store offset=1050064
                    end
                    local.get 2
                    i32.const 8
                    i32.add
                    local.set 0
                    local.get 2
                    local.get 3
                    i32.const 3
                    i32.or
                    i32.store offset=4
                    local.get 2
                    local.get 3
                    i32.add
                    local.tee 3
                    local.get 3
                    i32.load offset=4
                    i32.const 1
                    i32.or
                    i32.store offset=4
                    br 7 (;@1;)
                  end
                  block ;; label = @8
                    block ;; label = @9
                      local.get 0
                      local.get 2
                      i32.shl
                      i32.const 2
                      local.get 2
                      i32.shl
                      local.tee 0
                      i32.const 0
                      local.get 0
                      i32.sub
                      i32.or
                      i32.and
                      i32.ctz
                      local.tee 9
                      i32.const 3
                      i32.shl
                      local.tee 2
                      i32.const 1049800
                      i32.add
                      local.tee 7
                      local.get 2
                      i32.const 1049808
                      i32.add
                      i32.load
                      local.tee 0
                      i32.load offset=8
                      local.tee 8
                      i32.eq
                      br_if 0 (;@9;)
                      local.get 8
                      local.get 7
                      i32.store offset=12
                      local.get 7
                      local.get 8
                      i32.store offset=8
                      br 1 (;@8;)
                    end
                    i32.const 0
                    local.get 6
                    i32.const -2
                    local.get 9
                    i32.rotl
                    i32.and
                    i32.store offset=1050064
                  end
                  local.get 0
                  local.get 3
                  i32.const 3
                  i32.or
                  i32.store offset=4
                  local.get 0
                  local.get 3
                  i32.add
                  local.tee 6
                  local.get 2
                  local.get 3
                  i32.sub
                  local.tee 7
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 0
                  local.get 2
                  i32.add
                  local.get 7
                  i32.store
                  block ;; label = @8
                    i32.const 0
                    i32.load offset=1050072
                    local.tee 2
                    i32.eqz
                    br_if 0 (;@8;)
                    i32.const 0
                    i32.load offset=1050080
                    local.set 3
                    block ;; label = @9
                      block ;; label = @10
                        i32.const 0
                        i32.load offset=1050064
                        local.tee 8
                        i32.const 1
                        local.get 2
                        i32.const 3
                        i32.shr_u
                        i32.shl
                        local.tee 9
                        i32.and
                        br_if 0 (;@10;)
                        i32.const 0
                        local.get 8
                        local.get 9
                        i32.or
                        i32.store offset=1050064
                        local.get 2
                        i32.const -8
                        i32.and
                        i32.const 1049800
                        i32.add
                        local.tee 2
                        local.set 8
                        br 1 (;@9;)
                      end
                      local.get 2
                      i32.const -8
                      i32.and
                      local.tee 2
                      i32.const 1049800
                      i32.add
                      local.set 8
                      local.get 2
                      i32.const 1049808
                      i32.add
                      i32.load
                      local.set 2
                    end
                    local.get 8
                    local.get 3
                    i32.store offset=8
                    local.get 2
                    local.get 3
                    i32.store offset=12
                    local.get 3
                    local.get 8
                    i32.store offset=12
                    local.get 3
                    local.get 2
                    i32.store offset=8
                  end
                  local.get 0
                  i32.const 8
                  i32.add
                  local.set 0
                  i32.const 0
                  local.get 6
                  i32.store offset=1050080
                  i32.const 0
                  local.get 7
                  i32.store offset=1050072
                  br 6 (;@1;)
                end
                i32.const 0
                i32.const 0
                i32.load offset=1050068
                i32.const -2
                local.get 6
                i32.load offset=28
                i32.rotl
                i32.and
                i32.store offset=1050068
              end
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    local.get 2
                    i32.const 16
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 6
                    local.get 3
                    i32.const 3
                    i32.or
                    i32.store offset=4
                    local.get 6
                    local.get 3
                    i32.add
                    local.tee 7
                    local.get 2
                    i32.const 1
                    i32.or
                    i32.store offset=4
                    local.get 7
                    local.get 2
                    i32.add
                    local.get 2
                    i32.store
                    i32.const 0
                    i32.load offset=1050072
                    local.tee 8
                    i32.eqz
                    br_if 1 (;@7;)
                    i32.const 0
                    i32.load offset=1050080
                    local.set 0
                    block ;; label = @9
                      block ;; label = @10
                        i32.const 0
                        i32.load offset=1050064
                        local.tee 9
                        i32.const 1
                        local.get 8
                        i32.const 3
                        i32.shr_u
                        i32.shl
                        local.tee 5
                        i32.and
                        br_if 0 (;@10;)
                        i32.const 0
                        local.get 9
                        local.get 5
                        i32.or
                        i32.store offset=1050064
                        local.get 8
                        i32.const -8
                        i32.and
                        i32.const 1049800
                        i32.add
                        local.tee 8
                        local.set 9
                        br 1 (;@9;)
                      end
                      local.get 8
                      i32.const -8
                      i32.and
                      local.tee 8
                      i32.const 1049800
                      i32.add
                      local.set 9
                      local.get 8
                      i32.const 1049808
                      i32.add
                      i32.load
                      local.set 8
                    end
                    local.get 9
                    local.get 0
                    i32.store offset=8
                    local.get 8
                    local.get 0
                    i32.store offset=12
                    local.get 0
                    local.get 9
                    i32.store offset=12
                    local.get 0
                    local.get 8
                    i32.store offset=8
                    br 1 (;@7;)
                  end
                  local.get 6
                  local.get 2
                  local.get 3
                  i32.add
                  local.tee 0
                  i32.const 3
                  i32.or
                  i32.store offset=4
                  local.get 6
                  local.get 0
                  i32.add
                  local.tee 0
                  local.get 0
                  i32.load offset=4
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  br 1 (;@6;)
                end
                i32.const 0
                local.get 7
                i32.store offset=1050080
                i32.const 0
                local.get 2
                i32.store offset=1050072
              end
              local.get 6
              i32.const 8
              i32.add
              local.tee 0
              i32.eqz
              br_if 3 (;@2;)
              br 4 (;@1;)
            end
            block ;; label = @5
              local.get 0
              local.get 7
              i32.or
              br_if 0 (;@5;)
              i32.const 0
              local.set 7
              i32.const 2
              local.get 5
              i32.shl
              local.tee 0
              i32.const 0
              local.get 0
              i32.sub
              i32.or
              local.get 4
              i32.and
              local.tee 0
              i32.eqz
              br_if 3 (;@2;)
              local.get 0
              i32.ctz
              i32.const 2
              i32.shl
              i32.const 1049656
              i32.add
              i32.load
              local.set 0
            end
            local.get 0
            i32.eqz
            br_if 1 (;@3;)
          end
          loop ;; label = @4
            local.get 0
            i32.load offset=4
            i32.const -8
            i32.and
            local.tee 6
            local.get 3
            i32.sub
            local.tee 8
            local.get 2
            local.get 8
            local.get 2
            i32.lt_u
            local.tee 9
            select
            local.set 5
            local.get 6
            local.get 3
            i32.lt_u
            local.set 8
            local.get 0
            local.get 7
            local.get 9
            select
            local.set 9
            block ;; label = @5
              local.get 0
              i32.load offset=16
              local.tee 6
              br_if 0 (;@5;)
              local.get 0
              i32.load offset=20
              local.set 6
            end
            local.get 2
            local.get 5
            local.get 8
            select
            local.set 2
            local.get 7
            local.get 9
            local.get 8
            select
            local.set 7
            local.get 6
            local.set 0
            local.get 6
            br_if 0 (;@4;)
          end
        end
        local.get 7
        i32.eqz
        br_if 0 (;@2;)
        block ;; label = @3
          i32.const 0
          i32.load offset=1050072
          local.tee 0
          local.get 3
          i32.lt_u
          br_if 0 (;@3;)
          local.get 2
          local.get 0
          local.get 3
          i32.sub
          i32.ge_u
          br_if 1 (;@2;)
        end
        local.get 7
        i32.load offset=24
        local.set 5
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 7
              i32.load offset=12
              local.tee 0
              local.get 7
              i32.ne
              br_if 0 (;@5;)
              local.get 7
              i32.const 20
              i32.const 16
              local.get 7
              i32.load offset=20
              local.tee 0
              select
              i32.add
              i32.load
              local.tee 6
              br_if 1 (;@4;)
              i32.const 0
              local.set 0
              br 2 (;@3;)
            end
            local.get 7
            i32.load offset=8
            local.tee 6
            local.get 0
            i32.store offset=12
            local.get 0
            local.get 6
            i32.store offset=8
            br 1 (;@3;)
          end
          local.get 7
          i32.const 20
          i32.add
          local.get 7
          i32.const 16
          i32.add
          local.get 0
          select
          local.set 8
          loop ;; label = @4
            local.get 8
            local.set 9
            local.get 6
            local.tee 0
            i32.const 20
            i32.add
            local.get 0
            i32.const 16
            i32.add
            local.get 0
            i32.load offset=20
            local.tee 6
            select
            local.set 8
            local.get 0
            i32.const 20
            i32.const 16
            local.get 6
            select
            i32.add
            i32.load
            local.tee 6
            br_if 0 (;@4;)
          end
          local.get 9
          i32.const 0
          i32.store
        end
        block ;; label = @3
          local.get 5
          i32.eqz
          br_if 0 (;@3;)
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                local.get 7
                local.get 7
                i32.load offset=28
                i32.const 2
                i32.shl
                i32.const 1049656
                i32.add
                local.tee 6
                i32.load
                i32.eq
                br_if 0 (;@6;)
                block ;; label = @7
                  local.get 5
                  i32.load offset=16
                  local.get 7
                  i32.eq
                  br_if 0 (;@7;)
                  local.get 5
                  local.get 0
                  i32.store offset=20
                  local.get 0
                  br_if 2 (;@5;)
                  br 4 (;@3;)
                end
                local.get 5
                local.get 0
                i32.store offset=16
                local.get 0
                br_if 1 (;@5;)
                br 3 (;@3;)
              end
              local.get 6
              local.get 0
              i32.store
              local.get 0
              i32.eqz
              br_if 1 (;@4;)
            end
            local.get 0
            local.get 5
            i32.store offset=24
            block ;; label = @5
              local.get 7
              i32.load offset=16
              local.tee 6
              i32.eqz
              br_if 0 (;@5;)
              local.get 0
              local.get 6
              i32.store offset=16
              local.get 6
              local.get 0
              i32.store offset=24
            end
            local.get 7
            i32.load offset=20
            local.tee 6
            i32.eqz
            br_if 1 (;@3;)
            local.get 0
            local.get 6
            i32.store offset=20
            local.get 6
            local.get 0
            i32.store offset=24
            br 1 (;@3;)
          end
          i32.const 0
          i32.const 0
          i32.load offset=1050068
          i32.const -2
          local.get 7
          i32.load offset=28
          i32.rotl
          i32.and
          i32.store offset=1050068
        end
        block ;; label = @3
          block ;; label = @4
            local.get 2
            i32.const 16
            i32.lt_u
            br_if 0 (;@4;)
            local.get 7
            local.get 3
            i32.const 3
            i32.or
            i32.store offset=4
            local.get 7
            local.get 3
            i32.add
            local.tee 0
            local.get 2
            i32.const 1
            i32.or
            i32.store offset=4
            local.get 0
            local.get 2
            i32.add
            local.get 2
            i32.store
            block ;; label = @5
              local.get 2
              i32.const 256
              i32.lt_u
              br_if 0 (;@5;)
              local.get 0
              local.get 2
              call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$18insert_large_chunk17h9a68b724c352c311E
              br 2 (;@3;)
            end
            block ;; label = @5
              block ;; label = @6
                i32.const 0
                i32.load offset=1050064
                local.tee 6
                i32.const 1
                local.get 2
                i32.const 3
                i32.shr_u
                i32.shl
                local.tee 8
                i32.and
                br_if 0 (;@6;)
                i32.const 0
                local.get 6
                local.get 8
                i32.or
                i32.store offset=1050064
                local.get 2
                i32.const 248
                i32.and
                i32.const 1049800
                i32.add
                local.tee 2
                local.set 6
                br 1 (;@5;)
              end
              local.get 2
              i32.const 248
              i32.and
              local.tee 2
              i32.const 1049800
              i32.add
              local.set 6
              local.get 2
              i32.const 1049808
              i32.add
              i32.load
              local.set 2
            end
            local.get 6
            local.get 0
            i32.store offset=8
            local.get 2
            local.get 0
            i32.store offset=12
            local.get 0
            local.get 6
            i32.store offset=12
            local.get 0
            local.get 2
            i32.store offset=8
            br 1 (;@3;)
          end
          local.get 7
          local.get 2
          local.get 3
          i32.add
          local.tee 0
          i32.const 3
          i32.or
          i32.store offset=4
          local.get 7
          local.get 0
          i32.add
          local.tee 0
          local.get 0
          i32.load offset=4
          i32.const 1
          i32.or
          i32.store offset=4
        end
        local.get 7
        i32.const 8
        i32.add
        local.tee 0
        br_if 1 (;@1;)
      end
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  i32.const 0
                  i32.load offset=1050072
                  local.tee 0
                  local.get 3
                  i32.ge_u
                  br_if 0 (;@7;)
                  block ;; label = @8
                    i32.const 0
                    i32.load offset=1050076
                    local.tee 0
                    local.get 3
                    i32.gt_u
                    br_if 0 (;@8;)
                    local.get 1
                    i32.const 4
                    i32.add
                    i32.const 1050108
                    local.get 3
                    i32.const 65583
                    i32.add
                    i32.const -65536
                    i32.and
                    call $_ZN61_$LT$dlmalloc..sys..System$u20$as$u20$dlmalloc..Allocator$GT$5alloc17h422ed1229d1b7810E
                    block ;; label = @9
                      local.get 1
                      i32.load offset=4
                      local.tee 6
                      br_if 0 (;@9;)
                      i32.const 0
                      local.set 0
                      br 8 (;@1;)
                    end
                    local.get 1
                    i32.load offset=12
                    local.set 5
                    i32.const 0
                    i32.const 0
                    i32.load offset=1050088
                    local.get 1
                    i32.load offset=8
                    local.tee 9
                    i32.add
                    local.tee 0
                    i32.store offset=1050088
                    i32.const 0
                    local.get 0
                    i32.const 0
                    i32.load offset=1050092
                    local.tee 2
                    local.get 0
                    local.get 2
                    i32.gt_u
                    select
                    i32.store offset=1050092
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          i32.const 0
                          i32.load offset=1050084
                          local.tee 2
                          i32.eqz
                          br_if 0 (;@11;)
                          i32.const 1049784
                          local.set 0
                          loop ;; label = @12
                            local.get 6
                            local.get 0
                            i32.load
                            local.tee 7
                            local.get 0
                            i32.load offset=4
                            local.tee 8
                            i32.add
                            i32.eq
                            br_if 2 (;@10;)
                            local.get 0
                            i32.load offset=8
                            local.tee 0
                            br_if 0 (;@12;)
                            br 3 (;@9;)
                          end
                        end
                        block ;; label = @11
                          block ;; label = @12
                            i32.const 0
                            i32.load offset=1050100
                            local.tee 0
                            i32.eqz
                            br_if 0 (;@12;)
                            local.get 6
                            local.get 0
                            i32.ge_u
                            br_if 1 (;@11;)
                          end
                          i32.const 0
                          local.get 6
                          i32.store offset=1050100
                        end
                        i32.const 0
                        i32.const 4095
                        i32.store offset=1050104
                        i32.const 0
                        local.get 5
                        i32.store offset=1049796
                        i32.const 0
                        local.get 9
                        i32.store offset=1049788
                        i32.const 0
                        local.get 6
                        i32.store offset=1049784
                        i32.const 0
                        i32.const 1049800
                        i32.store offset=1049812
                        i32.const 0
                        i32.const 1049808
                        i32.store offset=1049820
                        i32.const 0
                        i32.const 1049800
                        i32.store offset=1049808
                        i32.const 0
                        i32.const 1049816
                        i32.store offset=1049828
                        i32.const 0
                        i32.const 1049808
                        i32.store offset=1049816
                        i32.const 0
                        i32.const 1049824
                        i32.store offset=1049836
                        i32.const 0
                        i32.const 1049816
                        i32.store offset=1049824
                        i32.const 0
                        i32.const 1049832
                        i32.store offset=1049844
                        i32.const 0
                        i32.const 1049824
                        i32.store offset=1049832
                        i32.const 0
                        i32.const 1049840
                        i32.store offset=1049852
                        i32.const 0
                        i32.const 1049832
                        i32.store offset=1049840
                        i32.const 0
                        i32.const 1049848
                        i32.store offset=1049860
                        i32.const 0
                        i32.const 1049840
                        i32.store offset=1049848
                        i32.const 0
                        i32.const 1049856
                        i32.store offset=1049868
                        i32.const 0
                        i32.const 1049848
                        i32.store offset=1049856
                        i32.const 0
                        i32.const 1049864
                        i32.store offset=1049876
                        i32.const 0
                        i32.const 1049856
                        i32.store offset=1049864
                        i32.const 0
                        i32.const 1049864
                        i32.store offset=1049872
                        i32.const 0
                        i32.const 1049872
                        i32.store offset=1049884
                        i32.const 0
                        i32.const 1049872
                        i32.store offset=1049880
                        i32.const 0
                        i32.const 1049880
                        i32.store offset=1049892
                        i32.const 0
                        i32.const 1049880
                        i32.store offset=1049888
                        i32.const 0
                        i32.const 1049888
                        i32.store offset=1049900
                        i32.const 0
                        i32.const 1049888
                        i32.store offset=1049896
                        i32.const 0
                        i32.const 1049896
                        i32.store offset=1049908
                        i32.const 0
                        i32.const 1049896
                        i32.store offset=1049904
                        i32.const 0
                        i32.const 1049904
                        i32.store offset=1049916
                        i32.const 0
                        i32.const 1049904
                        i32.store offset=1049912
                        i32.const 0
                        i32.const 1049912
                        i32.store offset=1049924
                        i32.const 0
                        i32.const 1049912
                        i32.store offset=1049920
                        i32.const 0
                        i32.const 1049920
                        i32.store offset=1049932
                        i32.const 0
                        i32.const 1049920
                        i32.store offset=1049928
                        i32.const 0
                        i32.const 1049928
                        i32.store offset=1049940
                        i32.const 0
                        i32.const 1049936
                        i32.store offset=1049948
                        i32.const 0
                        i32.const 1049928
                        i32.store offset=1049936
                        i32.const 0
                        i32.const 1049944
                        i32.store offset=1049956
                        i32.const 0
                        i32.const 1049936
                        i32.store offset=1049944
                        i32.const 0
                        i32.const 1049952
                        i32.store offset=1049964
                        i32.const 0
                        i32.const 1049944
                        i32.store offset=1049952
                        i32.const 0
                        i32.const 1049960
                        i32.store offset=1049972
                        i32.const 0
                        i32.const 1049952
                        i32.store offset=1049960
                        i32.const 0
                        i32.const 1049968
                        i32.store offset=1049980
                        i32.const 0
                        i32.const 1049960
                        i32.store offset=1049968
                        i32.const 0
                        i32.const 1049976
                        i32.store offset=1049988
                        i32.const 0
                        i32.const 1049968
                        i32.store offset=1049976
                        i32.const 0
                        i32.const 1049984
                        i32.store offset=1049996
                        i32.const 0
                        i32.const 1049976
                        i32.store offset=1049984
                        i32.const 0
                        i32.const 1049992
                        i32.store offset=1050004
                        i32.const 0
                        i32.const 1049984
                        i32.store offset=1049992
                        i32.const 0
                        i32.const 1050000
                        i32.store offset=1050012
                        i32.const 0
                        i32.const 1049992
                        i32.store offset=1050000
                        i32.const 0
                        i32.const 1050008
                        i32.store offset=1050020
                        i32.const 0
                        i32.const 1050000
                        i32.store offset=1050008
                        i32.const 0
                        i32.const 1050016
                        i32.store offset=1050028
                        i32.const 0
                        i32.const 1050008
                        i32.store offset=1050016
                        i32.const 0
                        i32.const 1050024
                        i32.store offset=1050036
                        i32.const 0
                        i32.const 1050016
                        i32.store offset=1050024
                        i32.const 0
                        i32.const 1050032
                        i32.store offset=1050044
                        i32.const 0
                        i32.const 1050024
                        i32.store offset=1050032
                        i32.const 0
                        i32.const 1050040
                        i32.store offset=1050052
                        i32.const 0
                        i32.const 1050032
                        i32.store offset=1050040
                        i32.const 0
                        i32.const 1050048
                        i32.store offset=1050060
                        i32.const 0
                        i32.const 1050040
                        i32.store offset=1050048
                        i32.const 0
                        local.get 6
                        i32.const 15
                        i32.add
                        i32.const -8
                        i32.and
                        local.tee 0
                        i32.const -8
                        i32.add
                        local.tee 2
                        i32.store offset=1050084
                        i32.const 0
                        i32.const 1050048
                        i32.store offset=1050056
                        i32.const 0
                        local.get 6
                        local.get 0
                        i32.sub
                        local.get 9
                        i32.const -40
                        i32.add
                        local.tee 0
                        i32.add
                        i32.const 8
                        i32.add
                        local.tee 7
                        i32.store offset=1050076
                        local.get 2
                        local.get 7
                        i32.const 1
                        i32.or
                        i32.store offset=4
                        local.get 6
                        local.get 0
                        i32.add
                        i32.const 40
                        i32.store offset=4
                        i32.const 0
                        i32.const 2097152
                        i32.store offset=1050096
                        br 8 (;@2;)
                      end
                      local.get 2
                      local.get 6
                      i32.ge_u
                      br_if 0 (;@9;)
                      local.get 7
                      local.get 2
                      i32.gt_u
                      br_if 0 (;@9;)
                      local.get 0
                      i32.load offset=12
                      local.tee 7
                      i32.const 1
                      i32.and
                      br_if 0 (;@9;)
                      local.get 7
                      i32.const 1
                      i32.shr_u
                      local.get 5
                      i32.eq
                      br_if 3 (;@6;)
                    end
                    i32.const 0
                    i32.const 0
                    i32.load offset=1050100
                    local.tee 0
                    local.get 6
                    local.get 0
                    local.get 6
                    i32.lt_u
                    select
                    i32.store offset=1050100
                    local.get 6
                    local.get 9
                    i32.add
                    local.set 7
                    i32.const 1049784
                    local.set 0
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          loop ;; label = @12
                            local.get 0
                            i32.load
                            local.tee 8
                            local.get 7
                            i32.eq
                            br_if 1 (;@11;)
                            local.get 0
                            i32.load offset=8
                            local.tee 0
                            br_if 0 (;@12;)
                            br 2 (;@10;)
                          end
                        end
                        local.get 0
                        i32.load offset=12
                        local.tee 7
                        i32.const 1
                        i32.and
                        br_if 0 (;@10;)
                        local.get 7
                        i32.const 1
                        i32.shr_u
                        local.get 5
                        i32.eq
                        br_if 1 (;@9;)
                      end
                      i32.const 1049784
                      local.set 0
                      block ;; label = @10
                        loop ;; label = @11
                          block ;; label = @12
                            local.get 0
                            i32.load
                            local.tee 7
                            local.get 2
                            i32.gt_u
                            br_if 0 (;@12;)
                            local.get 2
                            local.get 7
                            local.get 0
                            i32.load offset=4
                            i32.add
                            local.tee 7
                            i32.lt_u
                            br_if 2 (;@10;)
                          end
                          local.get 0
                          i32.load offset=8
                          local.set 0
                          br 0 (;@11;)
                        end
                      end
                      i32.const 0
                      local.get 6
                      i32.const 15
                      i32.add
                      i32.const -8
                      i32.and
                      local.tee 0
                      i32.const -8
                      i32.add
                      local.tee 8
                      i32.store offset=1050084
                      i32.const 0
                      local.get 6
                      local.get 0
                      i32.sub
                      local.get 9
                      i32.const -40
                      i32.add
                      local.tee 0
                      i32.add
                      i32.const 8
                      i32.add
                      local.tee 4
                      i32.store offset=1050076
                      local.get 8
                      local.get 4
                      i32.const 1
                      i32.or
                      i32.store offset=4
                      local.get 6
                      local.get 0
                      i32.add
                      i32.const 40
                      i32.store offset=4
                      i32.const 0
                      i32.const 2097152
                      i32.store offset=1050096
                      local.get 2
                      local.get 7
                      i32.const -32
                      i32.add
                      i32.const -8
                      i32.and
                      i32.const -8
                      i32.add
                      local.tee 0
                      local.get 0
                      local.get 2
                      i32.const 16
                      i32.add
                      i32.lt_u
                      select
                      local.tee 8
                      i32.const 27
                      i32.store offset=4
                      i32.const 0
                      i64.load offset=1049784 align=4
                      local.set 10
                      local.get 8
                      i32.const 16
                      i32.add
                      i32.const 0
                      i64.load offset=1049792 align=4
                      i64.store align=4
                      local.get 8
                      i32.const 8
                      i32.add
                      local.tee 0
                      local.get 10
                      i64.store align=4
                      i32.const 0
                      local.get 5
                      i32.store offset=1049796
                      i32.const 0
                      local.get 9
                      i32.store offset=1049788
                      i32.const 0
                      local.get 6
                      i32.store offset=1049784
                      i32.const 0
                      local.get 0
                      i32.store offset=1049792
                      local.get 8
                      i32.const 28
                      i32.add
                      local.set 0
                      loop ;; label = @10
                        local.get 0
                        i32.const 7
                        i32.store
                        local.get 0
                        i32.const 4
                        i32.add
                        local.tee 0
                        local.get 7
                        i32.lt_u
                        br_if 0 (;@10;)
                      end
                      local.get 8
                      local.get 2
                      i32.eq
                      br_if 7 (;@2;)
                      local.get 8
                      local.get 8
                      i32.load offset=4
                      i32.const -2
                      i32.and
                      i32.store offset=4
                      local.get 2
                      local.get 8
                      local.get 2
                      i32.sub
                      local.tee 0
                      i32.const 1
                      i32.or
                      i32.store offset=4
                      local.get 8
                      local.get 0
                      i32.store
                      block ;; label = @10
                        local.get 0
                        i32.const 256
                        i32.lt_u
                        br_if 0 (;@10;)
                        local.get 2
                        local.get 0
                        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$18insert_large_chunk17h9a68b724c352c311E
                        br 8 (;@2;)
                      end
                      block ;; label = @10
                        block ;; label = @11
                          i32.const 0
                          i32.load offset=1050064
                          local.tee 7
                          i32.const 1
                          local.get 0
                          i32.const 3
                          i32.shr_u
                          i32.shl
                          local.tee 6
                          i32.and
                          br_if 0 (;@11;)
                          i32.const 0
                          local.get 7
                          local.get 6
                          i32.or
                          i32.store offset=1050064
                          local.get 0
                          i32.const 248
                          i32.and
                          i32.const 1049800
                          i32.add
                          local.tee 0
                          local.set 7
                          br 1 (;@10;)
                        end
                        local.get 0
                        i32.const 248
                        i32.and
                        local.tee 0
                        i32.const 1049800
                        i32.add
                        local.set 7
                        local.get 0
                        i32.const 1049808
                        i32.add
                        i32.load
                        local.set 0
                      end
                      local.get 7
                      local.get 2
                      i32.store offset=8
                      local.get 0
                      local.get 2
                      i32.store offset=12
                      local.get 2
                      local.get 7
                      i32.store offset=12
                      local.get 2
                      local.get 0
                      i32.store offset=8
                      br 7 (;@2;)
                    end
                    local.get 0
                    local.get 6
                    i32.store
                    local.get 0
                    local.get 0
                    i32.load offset=4
                    local.get 9
                    i32.add
                    i32.store offset=4
                    local.get 6
                    i32.const 15
                    i32.add
                    i32.const -8
                    i32.and
                    i32.const -8
                    i32.add
                    local.tee 7
                    local.get 3
                    i32.const 3
                    i32.or
                    i32.store offset=4
                    local.get 8
                    i32.const 15
                    i32.add
                    i32.const -8
                    i32.and
                    i32.const -8
                    i32.add
                    local.tee 2
                    local.get 7
                    local.get 3
                    i32.add
                    local.tee 0
                    i32.sub
                    local.set 3
                    local.get 2
                    i32.const 0
                    i32.load offset=1050084
                    i32.eq
                    br_if 3 (;@5;)
                    local.get 2
                    i32.const 0
                    i32.load offset=1050080
                    i32.eq
                    br_if 4 (;@4;)
                    block ;; label = @9
                      local.get 2
                      i32.load offset=4
                      local.tee 6
                      i32.const 3
                      i32.and
                      i32.const 1
                      i32.ne
                      br_if 0 (;@9;)
                      local.get 2
                      local.get 6
                      i32.const -8
                      i32.and
                      local.tee 6
                      call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE
                      local.get 6
                      local.get 3
                      i32.add
                      local.set 3
                      local.get 2
                      local.get 6
                      i32.add
                      local.tee 2
                      i32.load offset=4
                      local.set 6
                    end
                    local.get 2
                    local.get 6
                    i32.const -2
                    i32.and
                    i32.store offset=4
                    local.get 0
                    local.get 3
                    i32.const 1
                    i32.or
                    i32.store offset=4
                    local.get 0
                    local.get 3
                    i32.add
                    local.get 3
                    i32.store
                    block ;; label = @9
                      local.get 3
                      i32.const 256
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 0
                      local.get 3
                      call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$18insert_large_chunk17h9a68b724c352c311E
                      br 6 (;@3;)
                    end
                    block ;; label = @9
                      block ;; label = @10
                        i32.const 0
                        i32.load offset=1050064
                        local.tee 2
                        i32.const 1
                        local.get 3
                        i32.const 3
                        i32.shr_u
                        i32.shl
                        local.tee 6
                        i32.and
                        br_if 0 (;@10;)
                        i32.const 0
                        local.get 2
                        local.get 6
                        i32.or
                        i32.store offset=1050064
                        local.get 3
                        i32.const 248
                        i32.and
                        i32.const 1049800
                        i32.add
                        local.tee 3
                        local.set 2
                        br 1 (;@9;)
                      end
                      local.get 3
                      i32.const 248
                      i32.and
                      local.tee 3
                      i32.const 1049800
                      i32.add
                      local.set 2
                      local.get 3
                      i32.const 1049808
                      i32.add
                      i32.load
                      local.set 3
                    end
                    local.get 2
                    local.get 0
                    i32.store offset=8
                    local.get 3
                    local.get 0
                    i32.store offset=12
                    local.get 0
                    local.get 2
                    i32.store offset=12
                    local.get 0
                    local.get 3
                    i32.store offset=8
                    br 5 (;@3;)
                  end
                  i32.const 0
                  local.get 0
                  local.get 3
                  i32.sub
                  local.tee 2
                  i32.store offset=1050076
                  i32.const 0
                  i32.const 0
                  i32.load offset=1050084
                  local.tee 0
                  local.get 3
                  i32.add
                  local.tee 7
                  i32.store offset=1050084
                  local.get 7
                  local.get 2
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 0
                  local.get 3
                  i32.const 3
                  i32.or
                  i32.store offset=4
                  local.get 0
                  i32.const 8
                  i32.add
                  local.set 0
                  br 6 (;@1;)
                end
                i32.const 0
                i32.load offset=1050080
                local.set 2
                block ;; label = @7
                  block ;; label = @8
                    local.get 0
                    local.get 3
                    i32.sub
                    local.tee 7
                    i32.const 15
                    i32.gt_u
                    br_if 0 (;@8;)
                    i32.const 0
                    i32.const 0
                    i32.store offset=1050080
                    i32.const 0
                    i32.const 0
                    i32.store offset=1050072
                    local.get 2
                    local.get 0
                    i32.const 3
                    i32.or
                    i32.store offset=4
                    local.get 2
                    local.get 0
                    i32.add
                    local.tee 0
                    local.get 0
                    i32.load offset=4
                    i32.const 1
                    i32.or
                    i32.store offset=4
                    br 1 (;@7;)
                  end
                  i32.const 0
                  local.get 7
                  i32.store offset=1050072
                  i32.const 0
                  local.get 2
                  local.get 3
                  i32.add
                  local.tee 6
                  i32.store offset=1050080
                  local.get 6
                  local.get 7
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 2
                  local.get 0
                  i32.add
                  local.get 7
                  i32.store
                  local.get 2
                  local.get 3
                  i32.const 3
                  i32.or
                  i32.store offset=4
                end
                local.get 2
                i32.const 8
                i32.add
                local.set 0
                br 5 (;@1;)
              end
              local.get 0
              local.get 8
              local.get 9
              i32.add
              i32.store offset=4
              i32.const 0
              i32.const 0
              i32.load offset=1050084
              local.tee 0
              i32.const 15
              i32.add
              i32.const -8
              i32.and
              local.tee 2
              i32.const -8
              i32.add
              local.tee 7
              i32.store offset=1050084
              i32.const 0
              local.get 0
              local.get 2
              i32.sub
              i32.const 0
              i32.load offset=1050076
              local.get 9
              i32.add
              local.tee 2
              i32.add
              i32.const 8
              i32.add
              local.tee 6
              i32.store offset=1050076
              local.get 7
              local.get 6
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 0
              local.get 2
              i32.add
              i32.const 40
              i32.store offset=4
              i32.const 0
              i32.const 2097152
              i32.store offset=1050096
              br 3 (;@2;)
            end
            i32.const 0
            local.get 0
            i32.store offset=1050084
            i32.const 0
            i32.const 0
            i32.load offset=1050076
            local.get 3
            i32.add
            local.tee 3
            i32.store offset=1050076
            local.get 0
            local.get 3
            i32.const 1
            i32.or
            i32.store offset=4
            br 1 (;@3;)
          end
          i32.const 0
          local.get 0
          i32.store offset=1050080
          i32.const 0
          i32.const 0
          i32.load offset=1050072
          local.get 3
          i32.add
          local.tee 3
          i32.store offset=1050072
          local.get 0
          local.get 3
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 0
          local.get 3
          i32.add
          local.get 3
          i32.store
        end
        local.get 7
        i32.const 8
        i32.add
        local.set 0
        br 1 (;@1;)
      end
      i32.const 0
      local.set 0
      i32.const 0
      i32.load offset=1050076
      local.tee 2
      local.get 3
      i32.le_u
      br_if 0 (;@1;)
      i32.const 0
      local.get 2
      local.get 3
      i32.sub
      local.tee 2
      i32.store offset=1050076
      i32.const 0
      i32.const 0
      i32.load offset=1050084
      local.tee 0
      local.get 3
      i32.add
      local.tee 7
      i32.store offset=1050084
      local.get 7
      local.get 2
      i32.const 1
      i32.or
      i32.store offset=4
      local.get 0
      local.get 3
      i32.const 3
      i32.or
      i32.store offset=4
      local.get 0
      i32.const 8
      i32.add
      local.set 0
    end
    local.get 1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get 0
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc12___rust_abort (;16;) (type 9)
    unreachable
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc13___rdl_dealloc (;17;) (type 6) (param i32 i32 i32)
    (local i32 i32)
    block ;; label = @1
      block ;; label = @2
        local.get 0
        i32.const -4
        i32.add
        i32.load
        local.tee 3
        i32.const -8
        i32.and
        local.tee 4
        i32.const 4
        i32.const 8
        local.get 3
        i32.const 3
        i32.and
        local.tee 3
        select
        local.get 1
        i32.add
        i32.lt_u
        br_if 0 (;@2;)
        block ;; label = @3
          local.get 3
          i32.eqz
          br_if 0 (;@3;)
          local.get 4
          local.get 1
          i32.const 39
          i32.add
          i32.gt_u
          br_if 2 (;@1;)
        end
        local.get 0
        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$4free17h509b2e19faacb72fE
        return
      end
      i32.const 1049200
      i32.const 46
      i32.const 1049248
      call $_ZN4core9panicking5panic17h64d6d0d7de424379E
      unreachable
    end
    i32.const 1049264
    i32.const 46
    i32.const 1049312
    call $_ZN4core9panicking5panic17h64d6d0d7de424379E
    unreachable
  )
  (func $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$4free17h509b2e19faacb72fE (;18;) (type 13) (param i32)
    (local i32 i32 i32 i32 i32)
    local.get 0
    i32.const -8
    i32.add
    local.tee 1
    local.get 0
    i32.const -4
    i32.add
    i32.load
    local.tee 2
    i32.const -8
    i32.and
    local.tee 0
    i32.add
    local.set 3
    block ;; label = @1
      block ;; label = @2
        local.get 2
        i32.const 1
        i32.and
        br_if 0 (;@2;)
        local.get 2
        i32.const 2
        i32.and
        i32.eqz
        br_if 1 (;@1;)
        local.get 1
        i32.load
        local.tee 2
        local.get 0
        i32.add
        local.set 0
        block ;; label = @3
          local.get 1
          local.get 2
          i32.sub
          local.tee 1
          i32.const 0
          i32.load offset=1050080
          i32.ne
          br_if 0 (;@3;)
          local.get 3
          i32.load offset=4
          i32.const 3
          i32.and
          i32.const 3
          i32.ne
          br_if 1 (;@2;)
          i32.const 0
          local.get 0
          i32.store offset=1050072
          local.get 3
          local.get 3
          i32.load offset=4
          i32.const -2
          i32.and
          i32.store offset=4
          local.get 1
          local.get 0
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 3
          local.get 0
          i32.store
          return
        end
        local.get 1
        local.get 2
        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE
      end
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  local.get 3
                  i32.load offset=4
                  local.tee 2
                  i32.const 2
                  i32.and
                  br_if 0 (;@7;)
                  local.get 3
                  i32.const 0
                  i32.load offset=1050084
                  i32.eq
                  br_if 2 (;@5;)
                  local.get 3
                  i32.const 0
                  i32.load offset=1050080
                  i32.eq
                  br_if 3 (;@4;)
                  local.get 3
                  local.get 2
                  i32.const -8
                  i32.and
                  local.tee 2
                  call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE
                  local.get 1
                  local.get 2
                  local.get 0
                  i32.add
                  local.tee 0
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 1
                  local.get 0
                  i32.add
                  local.get 0
                  i32.store
                  local.get 1
                  i32.const 0
                  i32.load offset=1050080
                  i32.ne
                  br_if 1 (;@6;)
                  i32.const 0
                  local.get 0
                  i32.store offset=1050072
                  return
                end
                local.get 3
                local.get 2
                i32.const -2
                i32.and
                i32.store offset=4
                local.get 1
                local.get 0
                i32.const 1
                i32.or
                i32.store offset=4
                local.get 1
                local.get 0
                i32.add
                local.get 0
                i32.store
              end
              local.get 0
              i32.const 256
              i32.lt_u
              br_if 2 (;@3;)
              local.get 1
              local.get 0
              call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$18insert_large_chunk17h9a68b724c352c311E
              i32.const 0
              local.set 1
              i32.const 0
              i32.const 0
              i32.load offset=1050104
              i32.const -1
              i32.add
              local.tee 0
              i32.store offset=1050104
              local.get 0
              br_if 4 (;@1;)
              block ;; label = @6
                i32.const 0
                i32.load offset=1049792
                local.tee 0
                i32.eqz
                br_if 0 (;@6;)
                i32.const 0
                local.set 1
                loop ;; label = @7
                  local.get 1
                  i32.const 1
                  i32.add
                  local.set 1
                  local.get 0
                  i32.load offset=8
                  local.tee 0
                  br_if 0 (;@7;)
                end
              end
              i32.const 0
              local.get 1
              i32.const 4095
              local.get 1
              i32.const 4095
              i32.gt_u
              select
              i32.store offset=1050104
              return
            end
            i32.const 0
            local.get 1
            i32.store offset=1050084
            i32.const 0
            i32.const 0
            i32.load offset=1050076
            local.get 0
            i32.add
            local.tee 0
            i32.store offset=1050076
            local.get 1
            local.get 0
            i32.const 1
            i32.or
            i32.store offset=4
            block ;; label = @5
              local.get 1
              i32.const 0
              i32.load offset=1050080
              i32.ne
              br_if 0 (;@5;)
              i32.const 0
              i32.const 0
              i32.store offset=1050072
              i32.const 0
              i32.const 0
              i32.store offset=1050080
            end
            local.get 0
            i32.const 0
            i32.load offset=1050096
            local.tee 4
            i32.le_u
            br_if 3 (;@1;)
            i32.const 0
            i32.load offset=1050084
            local.tee 0
            i32.eqz
            br_if 3 (;@1;)
            i32.const 0
            local.set 2
            i32.const 0
            i32.load offset=1050076
            local.tee 5
            i32.const 41
            i32.lt_u
            br_if 2 (;@2;)
            i32.const 1049784
            local.set 1
            loop ;; label = @5
              block ;; label = @6
                local.get 1
                i32.load
                local.tee 3
                local.get 0
                i32.gt_u
                br_if 0 (;@6;)
                local.get 0
                local.get 3
                local.get 1
                i32.load offset=4
                i32.add
                i32.lt_u
                br_if 4 (;@2;)
              end
              local.get 1
              i32.load offset=8
              local.set 1
              br 0 (;@5;)
            end
          end
          i32.const 0
          local.get 1
          i32.store offset=1050080
          i32.const 0
          i32.const 0
          i32.load offset=1050072
          local.get 0
          i32.add
          local.tee 0
          i32.store offset=1050072
          local.get 1
          local.get 0
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 1
          local.get 0
          i32.add
          local.get 0
          i32.store
          return
        end
        block ;; label = @3
          block ;; label = @4
            i32.const 0
            i32.load offset=1050064
            local.tee 3
            i32.const 1
            local.get 0
            i32.const 3
            i32.shr_u
            i32.shl
            local.tee 2
            i32.and
            br_if 0 (;@4;)
            i32.const 0
            local.get 3
            local.get 2
            i32.or
            i32.store offset=1050064
            local.get 0
            i32.const 248
            i32.and
            i32.const 1049800
            i32.add
            local.tee 0
            local.set 3
            br 1 (;@3;)
          end
          local.get 0
          i32.const 248
          i32.and
          local.tee 0
          i32.const 1049800
          i32.add
          local.set 3
          local.get 0
          i32.const 1049808
          i32.add
          i32.load
          local.set 0
        end
        local.get 3
        local.get 1
        i32.store offset=8
        local.get 0
        local.get 1
        i32.store offset=12
        local.get 1
        local.get 3
        i32.store offset=12
        local.get 1
        local.get 0
        i32.store offset=8
        return
      end
      block ;; label = @2
        i32.const 0
        i32.load offset=1049792
        local.tee 1
        i32.eqz
        br_if 0 (;@2;)
        i32.const 0
        local.set 2
        loop ;; label = @3
          local.get 2
          i32.const 1
          i32.add
          local.set 2
          local.get 1
          i32.load offset=8
          local.tee 1
          br_if 0 (;@3;)
        end
      end
      i32.const 0
      local.get 2
      i32.const 4095
      local.get 2
      i32.const 4095
      i32.gt_u
      select
      i32.store offset=1050104
      local.get 5
      local.get 4
      i32.le_u
      br_if 0 (;@1;)
      i32.const 0
      i32.const -1
      i32.store offset=1050096
    end
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc13___rdl_realloc (;19;) (type 7) (param i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32)
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    local.get 0
                    i32.const -4
                    i32.add
                    local.tee 4
                    i32.load
                    local.tee 5
                    i32.const -8
                    i32.and
                    local.tee 6
                    i32.const 4
                    i32.const 8
                    local.get 5
                    i32.const 3
                    i32.and
                    local.tee 7
                    select
                    local.get 1
                    i32.add
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 1
                    i32.const 39
                    i32.add
                    local.set 8
                    block ;; label = @9
                      local.get 7
                      i32.eqz
                      br_if 0 (;@9;)
                      local.get 6
                      local.get 8
                      i32.gt_u
                      br_if 2 (;@7;)
                    end
                    block ;; label = @9
                      block ;; label = @10
                        local.get 2
                        i32.const 9
                        i32.lt_u
                        br_if 0 (;@10;)
                        local.get 2
                        local.get 3
                        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$8memalign17h5ffef2f2481bdd36E
                        local.tee 2
                        br_if 1 (;@9;)
                        i32.const 0
                        return
                      end
                      i32.const 0
                      local.set 2
                      local.get 3
                      i32.const -65588
                      i32.gt_u
                      br_if 8 (;@1;)
                      i32.const 16
                      local.get 3
                      i32.const 11
                      i32.add
                      i32.const -8
                      i32.and
                      local.get 3
                      i32.const 11
                      i32.lt_u
                      select
                      local.set 1
                      local.get 0
                      i32.const -8
                      i32.add
                      local.set 8
                      block ;; label = @10
                        local.get 7
                        br_if 0 (;@10;)
                        local.get 1
                        i32.const 256
                        i32.lt_u
                        br_if 7 (;@3;)
                        local.get 8
                        i32.eqz
                        br_if 7 (;@3;)
                        local.get 6
                        local.get 1
                        i32.le_u
                        br_if 7 (;@3;)
                        local.get 6
                        local.get 1
                        i32.sub
                        i32.const 131072
                        i32.gt_u
                        br_if 7 (;@3;)
                        local.get 0
                        return
                      end
                      local.get 8
                      local.get 6
                      i32.add
                      local.set 7
                      block ;; label = @10
                        block ;; label = @11
                          local.get 6
                          local.get 1
                          i32.ge_u
                          br_if 0 (;@11;)
                          local.get 7
                          i32.const 0
                          i32.load offset=1050084
                          i32.eq
                          br_if 1 (;@10;)
                          block ;; label = @12
                            local.get 7
                            i32.const 0
                            i32.load offset=1050080
                            i32.eq
                            br_if 0 (;@12;)
                            local.get 7
                            i32.load offset=4
                            local.tee 5
                            i32.const 2
                            i32.and
                            br_if 9 (;@3;)
                            local.get 5
                            i32.const -8
                            i32.and
                            local.tee 9
                            local.get 6
                            i32.add
                            local.tee 5
                            local.get 1
                            i32.lt_u
                            br_if 9 (;@3;)
                            local.get 7
                            local.get 9
                            call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE
                            block ;; label = @13
                              local.get 5
                              local.get 1
                              i32.sub
                              local.tee 7
                              i32.const 16
                              i32.lt_u
                              br_if 0 (;@13;)
                              local.get 4
                              local.get 1
                              local.get 4
                              i32.load
                              i32.const 1
                              i32.and
                              i32.or
                              i32.const 2
                              i32.or
                              i32.store
                              local.get 8
                              local.get 1
                              i32.add
                              local.tee 1
                              local.get 7
                              i32.const 3
                              i32.or
                              i32.store offset=4
                              local.get 8
                              local.get 5
                              i32.add
                              local.tee 5
                              local.get 5
                              i32.load offset=4
                              i32.const 1
                              i32.or
                              i32.store offset=4
                              local.get 1
                              local.get 7
                              call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$13dispose_chunk17hef6ec97b6fbd28fdE
                              br 9 (;@4;)
                            end
                            local.get 4
                            local.get 5
                            local.get 4
                            i32.load
                            i32.const 1
                            i32.and
                            i32.or
                            i32.const 2
                            i32.or
                            i32.store
                            local.get 8
                            local.get 5
                            i32.add
                            local.tee 1
                            local.get 1
                            i32.load offset=4
                            i32.const 1
                            i32.or
                            i32.store offset=4
                            br 8 (;@4;)
                          end
                          i32.const 0
                          i32.load offset=1050072
                          local.get 6
                          i32.add
                          local.tee 7
                          local.get 1
                          i32.lt_u
                          br_if 8 (;@3;)
                          block ;; label = @12
                            block ;; label = @13
                              local.get 7
                              local.get 1
                              i32.sub
                              local.tee 6
                              i32.const 15
                              i32.gt_u
                              br_if 0 (;@13;)
                              local.get 4
                              local.get 5
                              i32.const 1
                              i32.and
                              local.get 7
                              i32.or
                              i32.const 2
                              i32.or
                              i32.store
                              local.get 8
                              local.get 7
                              i32.add
                              local.tee 1
                              local.get 1
                              i32.load offset=4
                              i32.const 1
                              i32.or
                              i32.store offset=4
                              i32.const 0
                              local.set 6
                              i32.const 0
                              local.set 1
                              br 1 (;@12;)
                            end
                            local.get 4
                            local.get 1
                            local.get 5
                            i32.const 1
                            i32.and
                            i32.or
                            i32.const 2
                            i32.or
                            i32.store
                            local.get 8
                            local.get 1
                            i32.add
                            local.tee 1
                            local.get 6
                            i32.const 1
                            i32.or
                            i32.store offset=4
                            local.get 8
                            local.get 7
                            i32.add
                            local.tee 7
                            local.get 6
                            i32.store
                            local.get 7
                            local.get 7
                            i32.load offset=4
                            i32.const -2
                            i32.and
                            i32.store offset=4
                          end
                          i32.const 0
                          local.get 1
                          i32.store offset=1050080
                          i32.const 0
                          local.get 6
                          i32.store offset=1050072
                          br 7 (;@4;)
                        end
                        local.get 6
                        local.get 1
                        i32.sub
                        local.tee 6
                        i32.const 15
                        i32.le_u
                        br_if 6 (;@4;)
                        local.get 4
                        local.get 1
                        local.get 5
                        i32.const 1
                        i32.and
                        i32.or
                        i32.const 2
                        i32.or
                        i32.store
                        local.get 8
                        local.get 1
                        i32.add
                        local.tee 1
                        local.get 6
                        i32.const 3
                        i32.or
                        i32.store offset=4
                        local.get 7
                        local.get 7
                        i32.load offset=4
                        i32.const 1
                        i32.or
                        i32.store offset=4
                        local.get 1
                        local.get 6
                        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$13dispose_chunk17hef6ec97b6fbd28fdE
                        br 6 (;@4;)
                      end
                      i32.const 0
                      i32.load offset=1050076
                      local.get 6
                      i32.add
                      local.tee 7
                      local.get 1
                      i32.gt_u
                      br_if 4 (;@5;)
                      br 6 (;@3;)
                    end
                    block ;; label = @9
                      local.get 3
                      local.get 1
                      local.get 3
                      local.get 1
                      i32.lt_u
                      select
                      local.tee 3
                      i32.eqz
                      br_if 0 (;@9;)
                      local.get 2
                      local.get 0
                      local.get 3
                      memory.copy
                    end
                    local.get 4
                    i32.load
                    local.tee 3
                    i32.const -8
                    i32.and
                    local.tee 7
                    i32.const 4
                    i32.const 8
                    local.get 3
                    i32.const 3
                    i32.and
                    local.tee 3
                    select
                    local.get 1
                    i32.add
                    i32.lt_u
                    br_if 2 (;@6;)
                    local.get 3
                    i32.eqz
                    br_if 6 (;@2;)
                    local.get 7
                    local.get 8
                    i32.le_u
                    br_if 6 (;@2;)
                    i32.const 1049264
                    i32.const 46
                    i32.const 1049312
                    call $_ZN4core9panicking5panic17h64d6d0d7de424379E
                    unreachable
                  end
                  i32.const 1049200
                  i32.const 46
                  i32.const 1049248
                  call $_ZN4core9panicking5panic17h64d6d0d7de424379E
                  unreachable
                end
                i32.const 1049264
                i32.const 46
                i32.const 1049312
                call $_ZN4core9panicking5panic17h64d6d0d7de424379E
                unreachable
              end
              i32.const 1049200
              i32.const 46
              i32.const 1049248
              call $_ZN4core9panicking5panic17h64d6d0d7de424379E
              unreachable
            end
            local.get 4
            local.get 1
            local.get 5
            i32.const 1
            i32.and
            i32.or
            i32.const 2
            i32.or
            i32.store
            local.get 8
            local.get 1
            i32.add
            local.tee 5
            local.get 7
            local.get 1
            i32.sub
            local.tee 1
            i32.const 1
            i32.or
            i32.store offset=4
            i32.const 0
            local.get 1
            i32.store offset=1050076
            i32.const 0
            local.get 5
            i32.store offset=1050084
          end
          local.get 8
          i32.eqz
          br_if 0 (;@3;)
          local.get 0
          return
        end
        local.get 3
        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$6malloc17h44b8dc71ab434912E
        local.tee 1
        i32.eqz
        br_if 1 (;@1;)
        block ;; label = @3
          local.get 3
          i32.const -4
          i32.const -8
          local.get 4
          i32.load
          local.tee 2
          i32.const 3
          i32.and
          select
          local.get 2
          i32.const -8
          i32.and
          i32.add
          local.tee 2
          local.get 3
          local.get 2
          i32.lt_u
          select
          local.tee 3
          i32.eqz
          br_if 0 (;@3;)
          local.get 1
          local.get 0
          local.get 3
          memory.copy
        end
        local.get 1
        local.set 2
      end
      local.get 0
      call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$4free17h509b2e19faacb72fE
    end
    local.get 2
  )
  (func $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE (;20;) (type 0) (param i32 i32)
    (local i32 i32 i32 i32)
    local.get 0
    i32.load offset=12
    local.set 2
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            local.get 1
            i32.const 256
            i32.lt_u
            br_if 0 (;@4;)
            local.get 0
            i32.load offset=24
            local.set 3
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  local.get 2
                  local.get 0
                  i32.ne
                  br_if 0 (;@7;)
                  local.get 0
                  i32.const 20
                  i32.const 16
                  local.get 0
                  i32.load offset=20
                  local.tee 2
                  select
                  i32.add
                  i32.load
                  local.tee 1
                  br_if 1 (;@6;)
                  i32.const 0
                  local.set 2
                  br 2 (;@5;)
                end
                local.get 0
                i32.load offset=8
                local.tee 1
                local.get 2
                i32.store offset=12
                local.get 2
                local.get 1
                i32.store offset=8
                br 1 (;@5;)
              end
              local.get 0
              i32.const 20
              i32.add
              local.get 0
              i32.const 16
              i32.add
              local.get 2
              select
              local.set 4
              loop ;; label = @6
                local.get 4
                local.set 5
                local.get 1
                local.tee 2
                i32.const 20
                i32.add
                local.get 2
                i32.const 16
                i32.add
                local.get 2
                i32.load offset=20
                local.tee 1
                select
                local.set 4
                local.get 2
                i32.const 20
                i32.const 16
                local.get 1
                select
                i32.add
                i32.load
                local.tee 1
                br_if 0 (;@6;)
              end
              local.get 5
              i32.const 0
              i32.store
            end
            local.get 3
            i32.eqz
            br_if 2 (;@2;)
            block ;; label = @5
              block ;; label = @6
                local.get 0
                local.get 0
                i32.load offset=28
                i32.const 2
                i32.shl
                i32.const 1049656
                i32.add
                local.tee 1
                i32.load
                i32.eq
                br_if 0 (;@6;)
                local.get 3
                i32.load offset=16
                local.get 0
                i32.eq
                br_if 1 (;@5;)
                local.get 3
                local.get 2
                i32.store offset=20
                local.get 2
                br_if 3 (;@3;)
                br 4 (;@2;)
              end
              local.get 1
              local.get 2
              i32.store
              local.get 2
              i32.eqz
              br_if 4 (;@1;)
              br 2 (;@3;)
            end
            local.get 3
            local.get 2
            i32.store offset=16
            local.get 2
            br_if 1 (;@3;)
            br 2 (;@2;)
          end
          block ;; label = @4
            local.get 2
            local.get 0
            i32.load offset=8
            local.tee 4
            i32.eq
            br_if 0 (;@4;)
            local.get 4
            local.get 2
            i32.store offset=12
            local.get 2
            local.get 4
            i32.store offset=8
            return
          end
          i32.const 0
          i32.const 0
          i32.load offset=1050064
          i32.const -2
          local.get 1
          i32.const 3
          i32.shr_u
          i32.rotl
          i32.and
          i32.store offset=1050064
          return
        end
        local.get 2
        local.get 3
        i32.store offset=24
        block ;; label = @3
          local.get 0
          i32.load offset=16
          local.tee 1
          i32.eqz
          br_if 0 (;@3;)
          local.get 2
          local.get 1
          i32.store offset=16
          local.get 1
          local.get 2
          i32.store offset=24
        end
        local.get 0
        i32.load offset=20
        local.tee 1
        i32.eqz
        br_if 0 (;@2;)
        local.get 2
        local.get 1
        i32.store offset=20
        local.get 1
        local.get 2
        i32.store offset=24
        return
      end
      return
    end
    i32.const 0
    i32.const 0
    i32.load offset=1050068
    i32.const -2
    local.get 0
    i32.load offset=28
    i32.rotl
    i32.and
    i32.store offset=1050068
  )
  (func $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$13dispose_chunk17hef6ec97b6fbd28fdE (;21;) (type 0) (param i32 i32)
    (local i32 i32)
    local.get 0
    local.get 1
    i32.add
    local.set 2
    block ;; label = @1
      block ;; label = @2
        local.get 0
        i32.load offset=4
        local.tee 3
        i32.const 1
        i32.and
        br_if 0 (;@2;)
        local.get 3
        i32.const 2
        i32.and
        i32.eqz
        br_if 1 (;@1;)
        local.get 0
        i32.load
        local.tee 3
        local.get 1
        i32.add
        local.set 1
        block ;; label = @3
          local.get 0
          local.get 3
          i32.sub
          local.tee 0
          i32.const 0
          i32.load offset=1050080
          i32.ne
          br_if 0 (;@3;)
          local.get 2
          i32.load offset=4
          i32.const 3
          i32.and
          i32.const 3
          i32.ne
          br_if 1 (;@2;)
          i32.const 0
          local.get 1
          i32.store offset=1050072
          local.get 2
          local.get 2
          i32.load offset=4
          i32.const -2
          i32.and
          i32.store offset=4
          local.get 0
          local.get 1
          i32.const 1
          i32.or
          i32.store offset=4
          local.get 2
          local.get 1
          i32.store
          br 2 (;@1;)
        end
        local.get 0
        local.get 3
        call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE
      end
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 2
              i32.load offset=4
              local.tee 3
              i32.const 2
              i32.and
              br_if 0 (;@5;)
              local.get 2
              i32.const 0
              i32.load offset=1050084
              i32.eq
              br_if 2 (;@3;)
              local.get 2
              i32.const 0
              i32.load offset=1050080
              i32.eq
              br_if 3 (;@2;)
              local.get 2
              local.get 3
              i32.const -8
              i32.and
              local.tee 3
              call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$12unlink_chunk17h930d298e370350deE
              local.get 0
              local.get 3
              local.get 1
              i32.add
              local.tee 1
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 0
              local.get 1
              i32.add
              local.get 1
              i32.store
              local.get 0
              i32.const 0
              i32.load offset=1050080
              i32.ne
              br_if 1 (;@4;)
              i32.const 0
              local.get 1
              i32.store offset=1050072
              return
            end
            local.get 2
            local.get 3
            i32.const -2
            i32.and
            i32.store offset=4
            local.get 0
            local.get 1
            i32.const 1
            i32.or
            i32.store offset=4
            local.get 0
            local.get 1
            i32.add
            local.get 1
            i32.store
          end
          block ;; label = @4
            local.get 1
            i32.const 256
            i32.lt_u
            br_if 0 (;@4;)
            local.get 0
            local.get 1
            call $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$18insert_large_chunk17h9a68b724c352c311E
            return
          end
          block ;; label = @4
            block ;; label = @5
              i32.const 0
              i32.load offset=1050064
              local.tee 2
              i32.const 1
              local.get 1
              i32.const 3
              i32.shr_u
              i32.shl
              local.tee 3
              i32.and
              br_if 0 (;@5;)
              i32.const 0
              local.get 2
              local.get 3
              i32.or
              i32.store offset=1050064
              local.get 1
              i32.const 248
              i32.and
              i32.const 1049800
              i32.add
              local.tee 1
              local.set 2
              br 1 (;@4;)
            end
            local.get 1
            i32.const 248
            i32.and
            local.tee 1
            i32.const 1049800
            i32.add
            local.set 2
            local.get 1
            i32.const 1049808
            i32.add
            i32.load
            local.set 1
          end
          local.get 2
          local.get 0
          i32.store offset=8
          local.get 1
          local.get 0
          i32.store offset=12
          local.get 0
          local.get 2
          i32.store offset=12
          local.get 0
          local.get 1
          i32.store offset=8
          return
        end
        i32.const 0
        local.get 0
        i32.store offset=1050084
        i32.const 0
        i32.const 0
        i32.load offset=1050076
        local.get 1
        i32.add
        local.tee 1
        i32.store offset=1050076
        local.get 0
        local.get 1
        i32.const 1
        i32.or
        i32.store offset=4
        local.get 0
        i32.const 0
        i32.load offset=1050080
        i32.ne
        br_if 1 (;@1;)
        i32.const 0
        i32.const 0
        i32.store offset=1050072
        i32.const 0
        i32.const 0
        i32.store offset=1050080
        return
      end
      i32.const 0
      local.get 0
      i32.store offset=1050080
      i32.const 0
      i32.const 0
      i32.load offset=1050072
      local.get 1
      i32.add
      local.tee 1
      i32.store offset=1050072
      local.get 0
      local.get 1
      i32.const 1
      i32.or
      i32.store offset=4
      local.get 0
      local.get 1
      i32.add
      local.get 1
      i32.store
      return
    end
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc17rust_begin_unwind (;22;) (type 13) (param i32)
    (local i32 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 1
    global.set $__stack_pointer
    local.get 0
    i64.load align=4
    local.set 2
    local.get 1
    local.get 0
    i32.store offset=12
    local.get 1
    local.get 2
    i64.store offset=4 align=4
    local.get 1
    i32.const 4
    i32.add
    call $_ZN3std3sys9backtrace26__rust_end_short_backtrace17hdaee13ec4dd4f348E
    unreachable
  )
  (func $_ZN3std3sys9backtrace26__rust_end_short_backtrace17hdaee13ec4dd4f348E (;23;) (type 13) (param i32)
    local.get 0
    call $_ZN3std9panicking13panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17he5eb13023b639916E
    unreachable
  )
  (func $_RNvCsiGVaDesi5rv_7___rustc26___rust_alloc_error_handler (;24;) (type 0) (param i32 i32)
    (local i32)
    local.get 1
    local.get 0
    i32.const 0
    i32.load offset=1050108
    local.tee 2
    i32.const 1
    local.get 2
    select
    call_indirect (type 0)
    unreachable
  )
  (func $_ZN3std5alloc24default_alloc_error_hook17h4789bd729e081a35E (;25;) (type 0) (param i32 i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    block ;; label = @1
      call $_RNvCsiGVaDesi5rv_7___rustc42___rust_alloc_error_handler_should_panic_v2
      i32.const 255
      i32.and
      br_if 0 (;@1;)
      local.get 2
      i32.const 48
      i32.add
      global.set $__stack_pointer
      return
    end
    local.get 2
    local.get 1
    i32.store offset=36
    local.get 2
    i32.const 2
    i32.store offset=16
    local.get 2
    i32.const 1049072
    i32.store offset=12
    local.get 2
    i64.const 1
    i64.store offset=24 align=4
    local.get 2
    i32.const 2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get 2
    i32.const 36
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=40
    local.get 2
    local.get 2
    i32.const 40
    i32.add
    i32.store offset=20
    local.get 2
    i32.const 12
    i32.add
    i32.const 1049088
    call $_ZN4core9panicking9panic_fmt17hcb6b2b4be1f4be38E
    unreachable
  )
  (func $_ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h5b60737a5bd77be9E (;26;) (type 0) (param i32 i32)
    local.get 0
    i32.const 8
    i32.add
    i32.const 0
    i64.load offset=1049012 align=4
    i64.store align=4
    local.get 0
    i32.const 0
    i64.load offset=1049004 align=4
    i64.store align=4
  )
  (func $_ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h8c2ff05d5ddcfd57E (;27;) (type 0) (param i32 i32)
    local.get 0
    i32.const 8
    i32.add
    i32.const 0
    i64.load offset=1049028 align=4
    i64.store align=4
    local.get 0
    i32.const 0
    i64.load offset=1049020 align=4
    i64.store align=4
  )
  (func $_ZN5alloc7raw_vec20RawVecInner$LT$A$GT$7reserve21do_reserve_and_handle17hcf4186c3a8b06364E (;28;) (type 14) (param i32 i32 i32 i32 i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 5
    global.set $__stack_pointer
    block ;; label = @1
      local.get 2
      local.get 1
      i32.add
      local.tee 1
      local.get 2
      i32.ge_u
      br_if 0 (;@1;)
      i32.const 0
      i32.const 0
      call $_ZN5alloc7raw_vec12handle_error17h801d426cf510b77bE
      unreachable
    end
    local.get 5
    i32.const 4
    i32.add
    local.get 0
    i32.load
    local.tee 2
    local.get 0
    i32.load offset=4
    local.get 1
    local.get 2
    i32.const 1
    i32.shl
    local.tee 2
    local.get 1
    local.get 2
    i32.gt_u
    select
    local.tee 2
    i32.const 8
    i32.const 4
    local.get 4
    i32.const 1
    i32.eq
    select
    local.tee 1
    local.get 2
    local.get 1
    i32.gt_u
    select
    local.tee 2
    local.get 3
    local.get 4
    call $_ZN5alloc7raw_vec20RawVecInner$LT$A$GT$11finish_grow17h1f19212d6c980386E
    block ;; label = @1
      local.get 5
      i32.load offset=4
      i32.const 1
      i32.ne
      br_if 0 (;@1;)
      local.get 5
      i32.load offset=8
      local.get 5
      i32.load offset=12
      call $_ZN5alloc7raw_vec12handle_error17h801d426cf510b77bE
      unreachable
    end
    local.get 5
    i32.load offset=8
    local.set 4
    local.get 0
    local.get 2
    i32.store
    local.get 0
    local.get 4
    i32.store offset=4
    local.get 5
    i32.const 16
    i32.add
    global.set $__stack_pointer
  )
  (func $_ZN3std9panicking13panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17he5eb13023b639916E (;29;) (type 13) (param i32)
    (local i32 i32 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 1
    global.set $__stack_pointer
    local.get 0
    i32.load
    local.tee 2
    i32.load offset=12
    local.set 3
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            local.get 2
            i32.load offset=4
            br_table 0 (;@4;) 1 (;@3;) 2 (;@2;)
          end
          local.get 3
          br_if 1 (;@2;)
          i32.const 1
          local.set 2
          i32.const 0
          local.set 3
          br 2 (;@1;)
        end
        local.get 3
        br_if 0 (;@2;)
        local.get 2
        i32.load
        local.tee 2
        i32.load offset=4
        local.set 3
        local.get 2
        i32.load
        local.set 2
        br 1 (;@1;)
      end
      local.get 1
      i32.const -2147483648
      i32.store
      local.get 1
      local.get 0
      i32.store offset=12
      local.get 1
      i32.const 1049156
      local.get 0
      i32.load offset=4
      local.get 0
      i32.load offset=8
      local.tee 0
      i32.load8_u offset=8
      local.get 0
      i32.load8_u offset=9
      call $_ZN3std9panicking15panic_with_hook17hf90632d5c7102557E
      unreachable
    end
    local.get 1
    local.get 3
    i32.store offset=4
    local.get 1
    local.get 2
    i32.store
    local.get 1
    i32.const 1049128
    local.get 0
    i32.load offset=4
    local.get 0
    i32.load offset=8
    local.tee 0
    i32.load8_u offset=8
    local.get 0
    i32.load8_u offset=9
    call $_ZN3std9panicking15panic_with_hook17hf90632d5c7102557E
    unreachable
  )
  (func $_ZN5alloc7raw_vec20RawVecInner$LT$A$GT$11finish_grow17h1f19212d6c980386E (;30;) (type 15) (param i32 i32 i32 i32 i32 i32)
    (local i32 i32 i64)
    i32.const 1
    local.set 6
    i32.const 4
    local.set 7
    block ;; label = @1
      block ;; label = @2
        local.get 4
        local.get 5
        i32.add
        i32.const -1
        i32.add
        i32.const 0
        local.get 4
        i32.sub
        i32.and
        i64.extend_i32_u
        local.get 3
        i64.extend_i32_u
        i64.mul
        local.tee 8
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.eqz
        br_if 0 (;@2;)
        i32.const 0
        local.set 3
        br 1 (;@1;)
      end
      block ;; label = @2
        local.get 8
        i32.wrap_i64
        local.tee 3
        i32.const -2147483648
        local.get 4
        i32.sub
        i32.le_u
        br_if 0 (;@2;)
        i32.const 0
        local.set 3
        br 1 (;@1;)
      end
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 1
              i32.eqz
              br_if 0 (;@5;)
              local.get 2
              local.get 5
              local.get 1
              i32.mul
              local.get 4
              local.get 3
              call $_RNvCsiGVaDesi5rv_7___rustc14___rust_realloc
              local.set 7
              br 1 (;@4;)
            end
            block ;; label = @5
              local.get 3
              br_if 0 (;@5;)
              local.get 4
              local.set 7
              br 2 (;@3;)
            end
            call $_RNvCsiGVaDesi5rv_7___rustc35___rust_no_alloc_shim_is_unstable_v2
            local.get 3
            local.get 4
            call $_RNvCsiGVaDesi5rv_7___rustc12___rust_alloc
            local.set 7
          end
          local.get 7
          br_if 0 (;@3;)
          local.get 0
          local.get 4
          i32.store offset=4
          br 1 (;@2;)
        end
        local.get 0
        local.get 7
        i32.store offset=4
        i32.const 0
        local.set 6
      end
      i32.const 8
      local.set 7
    end
    local.get 0
    local.get 7
    i32.add
    local.get 3
    i32.store
    local.get 0
    local.get 6
    i32.store
  )
  (func $_ZN3std9panicking15panic_with_hook17hf90632d5c7102557E (;31;) (type 14) (param i32 i32 i32 i32 i32)
    (local i32 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 5
    global.set $__stack_pointer
    block ;; label = @1
      block ;; label = @2
        i32.const 1
        call $_ZN3std9panicking11panic_count8increase17h2fad2e4e885f053fE
        i32.const 255
        i32.and
        local.tee 6
        i32.const 2
        i32.eq
        br_if 0 (;@2;)
        local.get 6
        i32.const 1
        i32.and
        i32.eqz
        br_if 1 (;@1;)
        local.get 5
        i32.const 8
        i32.add
        local.get 0
        local.get 1
        i32.load offset=24
        call_indirect (type 0)
        br 1 (;@1;)
      end
      i32.const 0
      i32.load offset=1050124
      local.tee 6
      i32.const -1
      i32.le_s
      br_if 0 (;@1;)
      i32.const 0
      local.get 6
      i32.const 1
      i32.add
      i32.store offset=1050124
      block ;; label = @2
        block ;; label = @3
          i32.const 0
          i32.load offset=1050128
          i32.eqz
          br_if 0 (;@3;)
          local.get 5
          local.get 0
          local.get 1
          i32.load offset=20
          call_indirect (type 0)
          local.get 5
          local.get 4
          i32.store8 offset=29
          local.get 5
          local.get 3
          i32.store8 offset=28
          local.get 5
          local.get 2
          i32.store offset=24
          local.get 5
          local.get 5
          i64.load
          i64.store offset=16 align=4
          i32.const 0
          i32.load offset=1050128
          local.get 5
          i32.const 16
          i32.add
          i32.const 0
          i32.load offset=1050132
          i32.load offset=20
          call_indirect (type 0)
          br 1 (;@2;)
        end
        i32.const -2147483648
        local.get 5
        call $_ZN4core3ptr74drop_in_place$LT$core..option..Option$LT$alloc..vec..Vec$LT$u8$GT$$GT$$GT$17h59a19a21119bdc3aE
      end
      i32.const 0
      i32.const 0
      i32.load offset=1050124
      i32.const -1
      i32.add
      i32.store offset=1050124
      i32.const 0
      i32.const 0
      i32.store8 offset=1050116
      local.get 3
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      local.get 1
      call $_RNvCsiGVaDesi5rv_7___rustc10rust_panic
      unreachable
    end
    unreachable
  )
  (func $_ZN3std9panicking11panic_count8increase17h2fad2e4e885f053fE (;32;) (type 12) (param i32) (result i32)
    (local i32 i32)
    i32.const 0
    local.set 1
    i32.const 0
    i32.const 0
    i32.load offset=1050120
    local.tee 2
    i32.const 1
    i32.add
    i32.store offset=1050120
    block ;; label = @1
      local.get 2
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      i32.const 1
      local.set 1
      i32.const 0
      i32.load8_u offset=1050116
      br_if 0 (;@1;)
      i32.const 0
      local.get 0
      i32.store8 offset=1050116
      i32.const 0
      i32.const 0
      i32.load offset=1050112
      i32.const 1
      i32.add
      i32.store offset=1050112
      i32.const 2
      local.set 1
    end
    local.get 1
  )
  (func $_ZN4core3ptr74drop_in_place$LT$core..option..Option$LT$alloc..vec..Vec$LT$u8$GT$$GT$$GT$17h59a19a21119bdc3aE (;33;) (type 0) (param i32 i32)
    block ;; label = @1
      local.get 0
      i32.const -2147483648
      i32.or
      i32.const -2147483648
      i32.eq
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      i32.const 1
      call $_RNvCsiGVaDesi5rv_7___rustc14___rust_dealloc
    end
  )
  (func $_ZN4core3fmt5Write9write_fmt17hcdb9918cbf030b79E (;34;) (type 2) (param i32 i32) (result i32)
    local.get 0
    i32.const 1049104
    local.get 1
    call $_ZN4core3fmt5write17h105e86fc9b656fddE
  )
  (func $_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17ha04294fd91816487E (;35;) (type 13) (param i32)
    (local i32)
    block ;; label = @1
      local.get 0
      i32.load
      local.tee 1
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      i32.load offset=4
      local.get 1
      i32.const 1
      call $_RNvCsiGVaDesi5rv_7___rustc14___rust_dealloc
    end
  )
  (func $_ZN4core3ptr71drop_in_place$LT$std..panicking..panic_handler..FormatStringPayload$GT$17h15618c514526fd50E (;36;) (type 13) (param i32)
    (local i32)
    block ;; label = @1
      local.get 0
      i32.load
      local.tee 1
      i32.const -2147483648
      i32.or
      i32.const -2147483648
      i32.eq
      br_if 0 (;@1;)
      local.get 0
      i32.load offset=4
      local.get 1
      i32.const 1
      call $_RNvCsiGVaDesi5rv_7___rustc14___rust_dealloc
    end
  )
  (func $_ZN4core5panic12PanicPayload6as_str17h23c66d29e6d02f31E (;37;) (type 0) (param i32 i32)
    local.get 0
    i32.const 0
    i32.store
  )
  (func $_ZN58_$LT$alloc..string..String$u20$as$u20$core..fmt..Write$GT$10write_char17ha4fad37ffa3383adE (;38;) (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32)
    local.get 0
    i32.load offset=8
    local.set 2
    block ;; label = @1
      block ;; label = @2
        local.get 1
        i32.const 128
        i32.ge_u
        br_if 0 (;@2;)
        i32.const 1
        local.set 3
        br 1 (;@1;)
      end
      block ;; label = @2
        local.get 1
        i32.const 2048
        i32.ge_u
        br_if 0 (;@2;)
        i32.const 2
        local.set 3
        br 1 (;@1;)
      end
      i32.const 3
      i32.const 4
      local.get 1
      i32.const 65536
      i32.lt_u
      select
      local.set 3
    end
    local.get 2
    local.set 4
    block ;; label = @1
      local.get 3
      local.get 0
      i32.load
      local.get 2
      i32.sub
      i32.le_u
      br_if 0 (;@1;)
      local.get 0
      local.get 2
      local.get 3
      i32.const 1
      i32.const 1
      call $_ZN5alloc7raw_vec20RawVecInner$LT$A$GT$7reserve21do_reserve_and_handle17hcf4186c3a8b06364E
      local.get 0
      i32.load offset=8
      local.set 4
    end
    local.get 0
    i32.load offset=4
    local.get 4
    i32.add
    local.set 4
    block ;; label = @1
      block ;; label = @2
        local.get 1
        i32.const 128
        i32.lt_u
        br_if 0 (;@2;)
        local.get 1
        i32.const 63
        i32.and
        i32.const -128
        i32.or
        local.set 5
        local.get 1
        i32.const 6
        i32.shr_u
        local.set 6
        block ;; label = @3
          local.get 1
          i32.const 2048
          i32.ge_u
          br_if 0 (;@3;)
          local.get 4
          local.get 5
          i32.store8 offset=1
          local.get 4
          local.get 6
          i32.const 192
          i32.or
          i32.store8
          br 2 (;@1;)
        end
        local.get 1
        i32.const 12
        i32.shr_u
        local.set 7
        local.get 6
        i32.const 63
        i32.and
        i32.const -128
        i32.or
        local.set 6
        block ;; label = @3
          local.get 1
          i32.const 65535
          i32.gt_u
          br_if 0 (;@3;)
          local.get 4
          local.get 5
          i32.store8 offset=2
          local.get 4
          local.get 6
          i32.store8 offset=1
          local.get 4
          local.get 7
          i32.const 224
          i32.or
          i32.store8
          br 2 (;@1;)
        end
        local.get 4
        local.get 5
        i32.store8 offset=3
        local.get 4
        local.get 6
        i32.store8 offset=2
        local.get 4
        local.get 7
        i32.const 63
        i32.and
        i32.const -128
        i32.or
        i32.store8 offset=1
        local.get 4
        local.get 1
        i32.const 18
        i32.shr_u
        i32.const -16
        i32.or
        i32.store8
        br 1 (;@1;)
      end
      local.get 4
      local.get 1
      i32.store8
    end
    local.get 0
    local.get 3
    local.get 2
    i32.add
    i32.store offset=8
    i32.const 0
  )
  (func $_ZN58_$LT$alloc..string..String$u20$as$u20$core..fmt..Write$GT$9write_str17he8b31b395be857d0E (;39;) (type 1) (param i32 i32 i32) (result i32)
    (local i32)
    block ;; label = @1
      local.get 2
      local.get 0
      i32.load
      local.get 0
      i32.load offset=8
      local.tee 3
      i32.sub
      i32.le_u
      br_if 0 (;@1;)
      local.get 0
      local.get 3
      local.get 2
      i32.const 1
      i32.const 1
      call $_ZN5alloc7raw_vec20RawVecInner$LT$A$GT$7reserve21do_reserve_and_handle17hcf4186c3a8b06364E
      local.get 0
      i32.load offset=8
      local.set 3
    end
    block ;; label = @1
      local.get 2
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      i32.load offset=4
      local.get 3
      i32.add
      local.get 1
      local.get 2
      memory.copy
    end
    local.get 0
    local.get 3
    local.get 2
    i32.add
    i32.store offset=8
    i32.const 0
  )
  (func $_ZN86_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..fmt..Display$GT$3fmt17hd11db1273e797870E (;40;) (type 2) (param i32 i32) (result i32)
    local.get 1
    local.get 0
    i32.load
    local.get 0
    i32.load offset=4
    call $_ZN4core3fmt9Formatter9write_str17hb5ca0e988d371786E
  )
  (func $_ZN89_$LT$std..panicking..panic_handler..FormatStringPayload$u20$as$u20$core..fmt..Display$GT$3fmt17he4328ebb258ee506E (;41;) (type 2) (param i32 i32) (result i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    block ;; label = @1
      block ;; label = @2
        local.get 0
        i32.load
        i32.const -2147483648
        i32.eq
        br_if 0 (;@2;)
        local.get 1
        local.get 0
        i32.load offset=4
        local.get 0
        i32.load offset=8
        call $_ZN4core3fmt9Formatter9write_str17hb5ca0e988d371786E
        local.set 0
        br 1 (;@1;)
      end
      local.get 2
      i32.const 8
      i32.add
      i32.const 8
      i32.add
      local.get 0
      i32.load offset=12
      i32.load
      local.tee 0
      i32.const 8
      i32.add
      i64.load align=4
      i64.store
      local.get 2
      i32.const 8
      i32.add
      i32.const 16
      i32.add
      local.get 0
      i32.const 16
      i32.add
      i64.load align=4
      i64.store
      local.get 2
      local.get 0
      i64.load align=4
      i64.store offset=8
      local.get 1
      i32.load
      local.get 1
      i32.load offset=4
      local.get 2
      i32.const 8
      i32.add
      call $_ZN4core3fmt5write17h105e86fc9b656fddE
      local.set 0
    end
    local.get 2
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get 0
  )
  (func $_ZN8dlmalloc8dlmalloc17Dlmalloc$LT$A$GT$18insert_large_chunk17h9a68b724c352c311E (;42;) (type 0) (param i32 i32)
    (local i32 i32 i32 i32)
    i32.const 0
    local.set 2
    block ;; label = @1
      local.get 1
      i32.const 256
      i32.lt_u
      br_if 0 (;@1;)
      i32.const 31
      local.set 2
      local.get 1
      i32.const 16777215
      i32.gt_u
      br_if 0 (;@1;)
      local.get 1
      i32.const 38
      local.get 1
      i32.const 8
      i32.shr_u
      i32.clz
      local.tee 2
      i32.sub
      i32.shr_u
      i32.const 1
      i32.and
      local.get 2
      i32.const 1
      i32.shl
      i32.sub
      i32.const 62
      i32.add
      local.set 2
    end
    local.get 0
    i64.const 0
    i64.store offset=16 align=4
    local.get 0
    local.get 2
    i32.store offset=28
    local.get 2
    i32.const 2
    i32.shl
    i32.const 1049656
    i32.add
    local.set 3
    block ;; label = @1
      i32.const 0
      i32.load offset=1050068
      i32.const 1
      local.get 2
      i32.shl
      local.tee 4
      i32.and
      br_if 0 (;@1;)
      local.get 3
      local.get 0
      i32.store
      local.get 0
      local.get 3
      i32.store offset=24
      local.get 0
      local.get 0
      i32.store offset=12
      local.get 0
      local.get 0
      i32.store offset=8
      i32.const 0
      i32.const 0
      i32.load offset=1050068
      local.get 4
      i32.or
      i32.store offset=1050068
      return
    end
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 3
          i32.load
          local.tee 4
          i32.load offset=4
          i32.const -8
          i32.and
          local.get 1
          i32.ne
          br_if 0 (;@3;)
          local.get 4
          local.set 2
          br 1 (;@2;)
        end
        local.get 1
        i32.const 0
        i32.const 25
        local.get 2
        i32.const 1
        i32.shr_u
        i32.sub
        local.get 2
        i32.const 31
        i32.eq
        select
        i32.shl
        local.set 3
        loop ;; label = @3
          local.get 4
          local.get 3
          i32.const 29
          i32.shr_u
          i32.const 4
          i32.and
          i32.add
          local.tee 5
          i32.load offset=16
          local.tee 2
          i32.eqz
          br_if 2 (;@1;)
          local.get 3
          i32.const 1
          i32.shl
          local.set 3
          local.get 2
          local.set 4
          local.get 2
          i32.load offset=4
          i32.const -8
          i32.and
          local.get 1
          i32.ne
          br_if 0 (;@3;)
        end
      end
      local.get 2
      i32.load offset=8
      local.tee 3
      local.get 0
      i32.store offset=12
      local.get 2
      local.get 0
      i32.store offset=8
      local.get 0
      i32.const 0
      i32.store offset=24
      local.get 0
      local.get 2
      i32.store offset=12
      local.get 0
      local.get 3
      i32.store offset=8
      return
    end
    local.get 5
    i32.const 16
    i32.add
    local.get 0
    i32.store
    local.get 0
    local.get 4
    i32.store offset=24
    local.get 0
    local.get 0
    i32.store offset=12
    local.get 0
    local.get 0
    i32.store offset=8
  )
  (func $_ZN93_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$3get17h7f48818314d9168cE (;43;) (type 0) (param i32 i32)
    local.get 0
    i32.const 1049184
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
  )
  (func $_ZN93_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$6as_str17hc17d597821cf031dE (;44;) (type 0) (param i32 i32)
    local.get 0
    local.get 1
    i64.load align=4
    i64.store
  )
  (func $_ZN93_$LT$std..panicking..panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$8take_box17hc8b72e339dd81ae0E (;45;) (type 0) (param i32 i32)
    (local i32 i32)
    local.get 1
    i32.load offset=4
    local.set 2
    local.get 1
    i32.load
    local.set 3
    call $_RNvCsiGVaDesi5rv_7___rustc35___rust_no_alloc_shim_is_unstable_v2
    block ;; label = @1
      i32.const 8
      i32.const 4
      call $_RNvCsiGVaDesi5rv_7___rustc12___rust_alloc
      local.tee 1
      br_if 0 (;@1;)
      i32.const 4
      i32.const 8
      call $_ZN5alloc5alloc18handle_alloc_error17hfe7d39ac186073beE
      unreachable
    end
    local.get 1
    local.get 2
    i32.store offset=4
    local.get 1
    local.get 3
    i32.store
    local.get 0
    i32.const 1049184
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
  )
  (func $_ZN96_$LT$std..panicking..panic_handler..FormatStringPayload$u20$as$u20$core..panic..PanicPayload$GT$3get17h0c13fdf90f4d99c7E (;46;) (type 0) (param i32 i32)
    (local i32 i32 i32 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    block ;; label = @1
      local.get 1
      i32.load
      i32.const -2147483648
      i32.ne
      br_if 0 (;@1;)
      local.get 1
      i32.load offset=12
      local.set 3
      local.get 2
      i32.const 12
      i32.add
      i32.const 8
      i32.add
      local.tee 4
      i32.const 0
      i32.store
      local.get 2
      i64.const 4294967296
      i64.store offset=12 align=4
      local.get 2
      i32.const 24
      i32.add
      i32.const 8
      i32.add
      local.get 3
      i32.load
      local.tee 3
      i32.const 8
      i32.add
      i64.load align=4
      i64.store
      local.get 2
      i32.const 24
      i32.add
      i32.const 16
      i32.add
      local.get 3
      i32.const 16
      i32.add
      i64.load align=4
      i64.store
      local.get 2
      local.get 3
      i64.load align=4
      i64.store offset=24
      local.get 2
      i32.const 12
      i32.add
      i32.const 1049104
      local.get 2
      i32.const 24
      i32.add
      call $_ZN4core3fmt5write17h105e86fc9b656fddE
      drop
      local.get 2
      i32.const 8
      i32.add
      local.get 4
      i32.load
      local.tee 3
      i32.store
      local.get 2
      local.get 2
      i64.load offset=12 align=4
      local.tee 5
      i64.store
      local.get 1
      i32.const 8
      i32.add
      local.get 3
      i32.store
      local.get 1
      local.get 5
      i64.store align=4
    end
    local.get 0
    i32.const 1049328
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
    local.get 2
    i32.const 48
    i32.add
    global.set $__stack_pointer
  )
  (func $_ZN96_$LT$std..panicking..panic_handler..FormatStringPayload$u20$as$u20$core..panic..PanicPayload$GT$8take_box17h053d6b7c04e3df4dE (;47;) (type 0) (param i32 i32)
    (local i32 i32 i32 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    block ;; label = @1
      local.get 1
      i32.load
      i32.const -2147483648
      i32.ne
      br_if 0 (;@1;)
      local.get 1
      i32.load offset=12
      local.set 3
      local.get 2
      i32.const 28
      i32.add
      i32.const 8
      i32.add
      local.tee 4
      i32.const 0
      i32.store
      local.get 2
      i64.const 4294967296
      i64.store offset=28 align=4
      local.get 2
      i32.const 40
      i32.add
      i32.const 8
      i32.add
      local.get 3
      i32.load
      local.tee 3
      i32.const 8
      i32.add
      i64.load align=4
      i64.store
      local.get 2
      i32.const 40
      i32.add
      i32.const 16
      i32.add
      local.get 3
      i32.const 16
      i32.add
      i64.load align=4
      i64.store
      local.get 2
      local.get 3
      i64.load align=4
      i64.store offset=40
      local.get 2
      i32.const 28
      i32.add
      i32.const 1049104
      local.get 2
      i32.const 40
      i32.add
      call $_ZN4core3fmt5write17h105e86fc9b656fddE
      drop
      local.get 2
      i32.const 16
      i32.add
      i32.const 8
      i32.add
      local.get 4
      i32.load
      local.tee 3
      i32.store
      local.get 2
      local.get 2
      i64.load offset=28 align=4
      local.tee 5
      i64.store offset=16
      local.get 1
      i32.const 8
      i32.add
      local.get 3
      i32.store
      local.get 1
      local.get 5
      i64.store align=4
    end
    local.get 1
    i64.load align=4
    local.set 5
    local.get 1
    i64.const 4294967296
    i64.store align=4
    local.get 2
    i32.const 8
    i32.add
    local.tee 3
    local.get 1
    i32.const 8
    i32.add
    local.tee 1
    i32.load
    i32.store
    local.get 1
    i32.const 0
    i32.store
    local.get 2
    local.get 5
    i64.store
    call $_RNvCsiGVaDesi5rv_7___rustc35___rust_no_alloc_shim_is_unstable_v2
    block ;; label = @1
      i32.const 12
      i32.const 4
      call $_RNvCsiGVaDesi5rv_7___rustc12___rust_alloc
      local.tee 1
      br_if 0 (;@1;)
      i32.const 4
      i32.const 12
      call $_ZN5alloc5alloc18handle_alloc_error17hfe7d39ac186073beE
      unreachable
    end
    local.get 1
    local.get 2
    i64.load
    i64.store align=4
    local.get 1
    i32.const 8
    i32.add
    local.get 3
    i32.load
    i32.store
    local.get 0
    i32.const 1049328
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
    local.get 2
    i32.const 64
    i32.add
    global.set $__stack_pointer
  )
  (func $_ZN61_$LT$dlmalloc..sys..System$u20$as$u20$dlmalloc..Allocator$GT$5alloc17h422ed1229d1b7810E (;48;) (type 6) (param i32 i32 i32)
    (local i32 i32)
    block ;; label = @1
      block ;; label = @2
        local.get 2
        i32.const 16
        i32.shr_u
        local.get 2
        i32.const 65535
        i32.and
        i32.const 0
        i32.ne
        i32.add
        local.tee 2
        memory.grow
        local.tee 3
        i32.const -1
        i32.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set 2
        i32.const 0
        local.set 4
        br 1 (;@1;)
      end
      local.get 2
      i32.const 16
      i32.shl
      local.tee 4
      i32.const -16
      i32.add
      local.get 4
      local.get 3
      i32.const 16
      i32.shl
      local.tee 2
      i32.const 0
      local.get 4
      i32.sub
      i32.eq
      select
      local.set 4
    end
    local.get 0
    i32.const 0
    i32.store offset=8
    local.get 0
    local.get 4
    i32.store offset=4
    local.get 0
    local.get 2
    i32.store
  )
  (func $_ZN5alloc7raw_vec12handle_error17h801d426cf510b77bE (;49;) (type 0) (param i32 i32)
    block ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      local.get 1
      call $_ZN5alloc5alloc18handle_alloc_error17hfe7d39ac186073beE
      unreachable
    end
    call $_ZN5alloc7raw_vec17capacity_overflow17hf37eaeedcf19c4ccE
    unreachable
  )
  (func $_ZN5alloc5alloc18handle_alloc_error17hfe7d39ac186073beE (;50;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call $_RNvCsiGVaDesi5rv_7___rustc26___rust_alloc_error_handler
    unreachable
  )
  (func $_ZN5alloc7raw_vec17capacity_overflow17hf37eaeedcf19c4ccE (;51;) (type 9)
    (local i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 0
    global.set $__stack_pointer
    local.get 0
    i32.const 0
    i32.store offset=24
    local.get 0
    i32.const 1
    i32.store offset=12
    local.get 0
    i32.const 1049364
    i32.store offset=8
    local.get 0
    i64.const 4
    i64.store offset=16 align=4
    local.get 0
    i32.const 8
    i32.add
    i32.const 1049372
    call $_ZN4core9panicking9panic_fmt17hcb6b2b4be1f4be38E
    unreachable
  )
  (func $_ZN4core3fmt5write17h105e86fc9b656fddE (;52;) (type 1) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 1
    i32.store offset=4
    local.get 3
    local.get 0
    i32.store
    local.get 3
    i64.const 3758096416
    i64.store offset=8 align=4
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 2
              i32.load offset=16
              local.tee 4
              i32.eqz
              br_if 0 (;@5;)
              local.get 2
              i32.load offset=20
              local.tee 1
              br_if 1 (;@4;)
              br 2 (;@3;)
            end
            local.get 2
            i32.load offset=12
            local.tee 0
            i32.eqz
            br_if 1 (;@3;)
            local.get 2
            i32.load offset=8
            local.tee 1
            local.get 0
            i32.const 3
            i32.shl
            local.tee 0
            i32.add
            local.set 5
            local.get 0
            i32.const -8
            i32.add
            i32.const 3
            i32.shr_u
            i32.const 1
            i32.add
            local.set 6
            local.get 2
            i32.load
            local.set 0
            loop ;; label = @5
              block ;; label = @6
                local.get 0
                i32.const 4
                i32.add
                i32.load
                local.tee 7
                i32.eqz
                br_if 0 (;@6;)
                local.get 3
                i32.load
                local.get 0
                i32.load
                local.get 7
                local.get 3
                i32.load offset=4
                i32.load offset=12
                call_indirect (type 1)
                i32.eqz
                br_if 0 (;@6;)
                i32.const 1
                local.set 1
                br 5 (;@1;)
              end
              block ;; label = @6
                local.get 1
                i32.load
                local.get 3
                local.get 1
                i32.const 4
                i32.add
                i32.load
                call_indirect (type 2)
                i32.eqz
                br_if 0 (;@6;)
                i32.const 1
                local.set 1
                br 5 (;@1;)
              end
              local.get 0
              i32.const 8
              i32.add
              local.set 0
              local.get 1
              i32.const 8
              i32.add
              local.tee 1
              local.get 5
              i32.eq
              br_if 3 (;@2;)
              br 0 (;@5;)
            end
          end
          local.get 1
          i32.const 24
          i32.mul
          local.set 8
          local.get 1
          i32.const -1
          i32.add
          i32.const 536870911
          i32.and
          i32.const 1
          i32.add
          local.set 6
          local.get 2
          i32.load offset=8
          local.set 9
          local.get 2
          i32.load
          local.set 0
          i32.const 0
          local.set 7
          loop ;; label = @4
            block ;; label = @5
              local.get 0
              i32.const 4
              i32.add
              i32.load
              local.tee 1
              i32.eqz
              br_if 0 (;@5;)
              local.get 3
              i32.load
              local.get 0
              i32.load
              local.get 1
              local.get 3
              i32.load offset=4
              i32.load offset=12
              call_indirect (type 1)
              i32.eqz
              br_if 0 (;@5;)
              i32.const 1
              local.set 1
              br 4 (;@1;)
            end
            i32.const 0
            local.set 5
            i32.const 0
            local.set 10
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  local.get 4
                  local.get 7
                  i32.add
                  local.tee 1
                  i32.const 8
                  i32.add
                  i32.load16_u
                  br_table 0 (;@7;) 1 (;@6;) 2 (;@5;) 0 (;@7;)
                end
                local.get 1
                i32.const 10
                i32.add
                i32.load16_u
                local.set 10
                br 1 (;@5;)
              end
              local.get 9
              local.get 1
              i32.const 12
              i32.add
              i32.load
              i32.const 3
              i32.shl
              i32.add
              i32.load16_u offset=4
              local.set 10
            end
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  local.get 1
                  i32.load16_u
                  br_table 0 (;@7;) 1 (;@6;) 2 (;@5;) 0 (;@7;)
                end
                local.get 1
                i32.const 2
                i32.add
                i32.load16_u
                local.set 5
                br 1 (;@5;)
              end
              local.get 9
              local.get 1
              i32.const 4
              i32.add
              i32.load
              i32.const 3
              i32.shl
              i32.add
              i32.load16_u offset=4
              local.set 5
            end
            local.get 3
            local.get 5
            i32.store16 offset=14
            local.get 3
            local.get 10
            i32.store16 offset=12
            local.get 3
            local.get 1
            i32.const 20
            i32.add
            i32.load
            i32.store offset=8
            block ;; label = @5
              local.get 9
              local.get 1
              i32.const 16
              i32.add
              i32.load
              i32.const 3
              i32.shl
              i32.add
              local.tee 1
              i32.load
              local.get 3
              local.get 1
              i32.load offset=4
              call_indirect (type 2)
              i32.eqz
              br_if 0 (;@5;)
              i32.const 1
              local.set 1
              br 4 (;@1;)
            end
            local.get 0
            i32.const 8
            i32.add
            local.set 0
            local.get 8
            local.get 7
            i32.const 24
            i32.add
            local.tee 7
            i32.eq
            br_if 2 (;@2;)
            br 0 (;@4;)
          end
        end
        i32.const 0
        local.set 6
      end
      block ;; label = @2
        local.get 6
        local.get 2
        i32.load offset=4
        i32.ge_u
        br_if 0 (;@2;)
        local.get 3
        i32.load
        local.get 2
        i32.load
        local.get 6
        i32.const 3
        i32.shl
        i32.add
        local.tee 1
        i32.load
        local.get 1
        i32.load offset=4
        local.get 3
        i32.load offset=4
        i32.load offset=12
        call_indirect (type 1)
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1
        local.set 1
        br 1 (;@1;)
      end
      i32.const 0
      local.set 1
    end
    local.get 3
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get 1
  )
  (func $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u32$GT$3fmt17h959da39f0c36984eE (;53;) (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    i32.const 10
    local.set 3
    local.get 0
    i32.load
    local.tee 4
    local.set 5
    block ;; label = @1
      local.get 4
      i32.const 1000
      i32.lt_u
      br_if 0 (;@1;)
      i32.const 10
      local.set 3
      local.get 4
      local.set 0
      loop ;; label = @2
        local.get 2
        i32.const 6
        i32.add
        local.get 3
        i32.add
        local.tee 6
        i32.const -4
        i32.add
        local.get 0
        local.get 0
        i32.const 10000
        i32.div_u
        local.tee 5
        i32.const 10000
        i32.mul
        i32.sub
        local.tee 7
        i32.const 65535
        i32.and
        i32.const 100
        i32.div_u
        local.tee 8
        i32.const 1
        i32.shl
        i32.load16_u offset=1049388 align=1
        i32.store16 align=1
        local.get 6
        i32.const -2
        i32.add
        local.get 7
        local.get 8
        i32.const 100
        i32.mul
        i32.sub
        i32.const 65535
        i32.and
        i32.const 1
        i32.shl
        i32.load16_u offset=1049388 align=1
        i32.store16 align=1
        local.get 3
        i32.const -4
        i32.add
        local.set 3
        local.get 0
        i32.const 9999999
        i32.gt_u
        local.set 6
        local.get 5
        local.set 0
        local.get 6
        br_if 0 (;@2;)
      end
    end
    block ;; label = @1
      block ;; label = @2
        local.get 5
        i32.const 9
        i32.gt_u
        br_if 0 (;@2;)
        local.get 5
        local.set 0
        br 1 (;@1;)
      end
      local.get 2
      i32.const 6
      i32.add
      local.get 3
      i32.const -2
      i32.add
      local.tee 3
      i32.add
      local.get 5
      local.get 5
      i32.const 65535
      i32.and
      i32.const 100
      i32.div_u
      local.tee 0
      i32.const 100
      i32.mul
      i32.sub
      i32.const 65535
      i32.and
      i32.const 1
      i32.shl
      i32.load16_u offset=1049388 align=1
      i32.store16 align=1
    end
    block ;; label = @1
      block ;; label = @2
        local.get 4
        i32.eqz
        br_if 0 (;@2;)
        local.get 0
        i32.eqz
        br_if 1 (;@1;)
      end
      local.get 2
      i32.const 6
      i32.add
      local.get 3
      i32.const -1
      i32.add
      local.tee 3
      i32.add
      local.get 0
      i32.const 1
      i32.shl
      i32.load8_u offset=1049389
      i32.store8
    end
    local.get 1
    i32.const 1
    i32.const 1
    i32.const 0
    local.get 2
    i32.const 6
    i32.add
    local.get 3
    i32.add
    i32.const 10
    local.get 3
    i32.sub
    call $_ZN4core3fmt9Formatter12pad_integral17hbdad2815f8b1b74cE
    local.set 0
    local.get 2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get 0
  )
  (func $_ZN4core3fmt9Formatter12pad_integral17hbdad2815f8b1b74cE (;54;) (type 16) (param i32 i32 i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i64)
    block ;; label = @1
      block ;; label = @2
        local.get 1
        br_if 0 (;@2;)
        local.get 5
        i32.const 1
        i32.add
        local.set 6
        local.get 0
        i32.load offset=8
        local.set 7
        i32.const 45
        local.set 8
        br 1 (;@1;)
      end
      i32.const 43
      i32.const 1114112
      local.get 0
      i32.load offset=8
      local.tee 7
      i32.const 2097152
      i32.and
      local.tee 1
      select
      local.set 8
      local.get 1
      i32.const 21
      i32.shr_u
      local.get 5
      i32.add
      local.set 6
    end
    block ;; label = @1
      block ;; label = @2
        local.get 7
        i32.const 8388608
        i32.and
        br_if 0 (;@2;)
        i32.const 0
        local.set 2
        br 1 (;@1;)
      end
      block ;; label = @2
        block ;; label = @3
          local.get 3
          i32.const 16
          i32.lt_u
          br_if 0 (;@3;)
          local.get 2
          local.get 3
          call $_ZN4core3str5count14do_count_chars17h3a6be4dd70539b83E
          local.set 1
          br 1 (;@2;)
        end
        block ;; label = @3
          local.get 3
          br_if 0 (;@3;)
          i32.const 0
          local.set 1
          br 1 (;@2;)
        end
        local.get 3
        i32.const 3
        i32.and
        local.set 9
        block ;; label = @3
          block ;; label = @4
            local.get 3
            i32.const 4
            i32.ge_u
            br_if 0 (;@4;)
            i32.const 0
            local.set 10
            i32.const 0
            local.set 1
            br 1 (;@3;)
          end
          local.get 3
          i32.const 12
          i32.and
          local.set 11
          i32.const 0
          local.set 10
          i32.const 0
          local.set 1
          loop ;; label = @4
            local.get 1
            local.get 2
            local.get 10
            i32.add
            local.tee 12
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get 12
            i32.const 1
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get 12
            i32.const 2
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get 12
            i32.const 3
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set 1
            local.get 11
            local.get 10
            i32.const 4
            i32.add
            local.tee 10
            i32.ne
            br_if 0 (;@4;)
          end
        end
        local.get 9
        i32.eqz
        br_if 0 (;@2;)
        local.get 2
        local.get 10
        i32.add
        local.set 12
        loop ;; label = @3
          local.get 1
          local.get 12
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set 1
          local.get 12
          i32.const 1
          i32.add
          local.set 12
          local.get 9
          i32.const -1
          i32.add
          local.tee 9
          br_if 0 (;@3;)
        end
      end
      local.get 1
      local.get 6
      i32.add
      local.set 6
    end
    block ;; label = @1
      block ;; label = @2
        local.get 6
        local.get 0
        i32.load16_u offset=12
        local.tee 11
        i32.ge_u
        br_if 0 (;@2;)
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 7
              i32.const 16777216
              i32.and
              br_if 0 (;@5;)
              local.get 11
              local.get 6
              i32.sub
              local.set 13
              i32.const 0
              local.set 1
              i32.const 0
              local.set 11
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    local.get 7
                    i32.const 29
                    i32.shr_u
                    i32.const 3
                    i32.and
                    br_table 2 (;@6;) 0 (;@8;) 1 (;@7;) 0 (;@8;) 2 (;@6;)
                  end
                  local.get 13
                  local.set 11
                  br 1 (;@6;)
                end
                local.get 13
                i32.const 65534
                i32.and
                i32.const 1
                i32.shr_u
                local.set 11
              end
              local.get 7
              i32.const 2097151
              i32.and
              local.set 6
              local.get 0
              i32.load offset=4
              local.set 9
              local.get 0
              i32.load
              local.set 10
              loop ;; label = @6
                local.get 1
                i32.const 65535
                i32.and
                local.get 11
                i32.const 65535
                i32.and
                i32.ge_u
                br_if 2 (;@4;)
                i32.const 1
                local.set 12
                local.get 1
                i32.const 1
                i32.add
                local.set 1
                local.get 10
                local.get 6
                local.get 9
                i32.load offset=16
                call_indirect (type 2)
                i32.eqz
                br_if 0 (;@6;)
                br 5 (;@1;)
              end
            end
            local.get 0
            local.get 0
            i64.load offset=8 align=4
            local.tee 14
            i32.wrap_i64
            i32.const -1612709888
            i32.and
            i32.const 536870960
            i32.or
            i32.store offset=8
            i32.const 1
            local.set 12
            local.get 0
            i32.load
            local.tee 10
            local.get 0
            i32.load offset=4
            local.tee 9
            local.get 8
            local.get 2
            local.get 3
            call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17h919f5846d356d1c8E
            br_if 3 (;@1;)
            i32.const 0
            local.set 1
            local.get 11
            local.get 6
            i32.sub
            i32.const 65535
            i32.and
            local.set 2
            loop ;; label = @5
              local.get 1
              i32.const 65535
              i32.and
              local.get 2
              i32.ge_u
              br_if 2 (;@3;)
              i32.const 1
              local.set 12
              local.get 1
              i32.const 1
              i32.add
              local.set 1
              local.get 10
              i32.const 48
              local.get 9
              i32.load offset=16
              call_indirect (type 2)
              i32.eqz
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
          end
          i32.const 1
          local.set 12
          local.get 10
          local.get 9
          local.get 8
          local.get 2
          local.get 3
          call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17h919f5846d356d1c8E
          br_if 2 (;@1;)
          local.get 10
          local.get 4
          local.get 5
          local.get 9
          i32.load offset=12
          call_indirect (type 1)
          br_if 2 (;@1;)
          i32.const 0
          local.set 1
          local.get 13
          local.get 11
          i32.sub
          i32.const 65535
          i32.and
          local.set 0
          loop ;; label = @4
            local.get 1
            i32.const 65535
            i32.and
            local.tee 2
            local.get 0
            i32.lt_u
            local.set 12
            local.get 2
            local.get 0
            i32.ge_u
            br_if 3 (;@1;)
            local.get 1
            i32.const 1
            i32.add
            local.set 1
            local.get 10
            local.get 6
            local.get 9
            i32.load offset=16
            call_indirect (type 2)
            i32.eqz
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        i32.const 1
        local.set 12
        local.get 10
        local.get 4
        local.get 5
        local.get 9
        i32.load offset=12
        call_indirect (type 1)
        br_if 1 (;@1;)
        local.get 0
        local.get 14
        i64.store offset=8 align=4
        i32.const 0
        return
      end
      i32.const 1
      local.set 12
      local.get 0
      i32.load
      local.tee 1
      local.get 0
      i32.load offset=4
      local.tee 10
      local.get 8
      local.get 2
      local.get 3
      call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17h919f5846d356d1c8E
      br_if 0 (;@1;)
      local.get 1
      local.get 4
      local.get 5
      local.get 10
      i32.load offset=12
      call_indirect (type 1)
      local.set 12
    end
    local.get 12
  )
  (func $_ZN4core9panicking9panic_fmt17hcb6b2b4be1f4be38E (;55;) (type 0) (param i32 i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    local.get 2
    i32.const 1
    i32.store16 offset=12
    local.get 2
    local.get 1
    i32.store offset=8
    local.get 2
    local.get 0
    i32.store offset=4
    local.get 2
    i32.const 4
    i32.add
    call $_RNvCsiGVaDesi5rv_7___rustc17rust_begin_unwind
    unreachable
  )
  (func $_ZN4core9panicking18panic_bounds_check17h62ab6f5933ba978dE (;56;) (type 6) (param i32 i32 i32)
    (local i32 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 1
    i32.store offset=4
    local.get 3
    local.get 0
    i32.store
    local.get 3
    i32.const 2
    i32.store offset=12
    local.get 3
    i32.const 1049640
    i32.store offset=8
    local.get 3
    i64.const 2
    i64.store offset=20 align=4
    local.get 3
    i32.const 2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.tee 4
    local.get 3
    i64.extend_i32_u
    i64.or
    i64.store offset=40
    local.get 3
    local.get 4
    local.get 3
    i32.const 4
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=32
    local.get 3
    local.get 3
    i32.const 32
    i32.add
    i32.store offset=16
    local.get 3
    i32.const 8
    i32.add
    local.get 2
    call $_ZN4core9panicking9panic_fmt17hcb6b2b4be1f4be38E
    unreachable
  )
  (func $_ZN4core9panicking5panic17h64d6d0d7de424379E (;57;) (type 6) (param i32 i32 i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    i32.const 0
    i32.store offset=16
    local.get 3
    i32.const 1
    i32.store offset=4
    local.get 3
    i64.const 4
    i64.store offset=8 align=4
    local.get 3
    local.get 1
    i32.store offset=28
    local.get 3
    local.get 0
    i32.store offset=24
    local.get 3
    local.get 3
    i32.const 24
    i32.add
    i32.store
    local.get 3
    local.get 2
    call $_ZN4core9panicking9panic_fmt17hcb6b2b4be1f4be38E
    unreachable
  )
  (func $_ZN4core3fmt9Formatter12pad_integral12write_prefix17h919f5846d356d1c8E (;58;) (type 17) (param i32 i32 i32 i32 i32) (result i32)
    block ;; label = @1
      local.get 2
      i32.const 1114112
      i32.eq
      br_if 0 (;@1;)
      local.get 0
      local.get 2
      local.get 1
      i32.load offset=16
      call_indirect (type 2)
      i32.eqz
      br_if 0 (;@1;)
      i32.const 1
      return
    end
    block ;; label = @1
      local.get 3
      br_if 0 (;@1;)
      i32.const 0
      return
    end
    local.get 0
    local.get 3
    local.get 4
    local.get 1
    i32.load offset=12
    call_indirect (type 1)
  )
  (func $_ZN4core3str5count14do_count_chars17h3a6be4dd70539b83E (;59;) (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    block ;; label = @1
      block ;; label = @2
        local.get 1
        local.get 0
        i32.const 3
        i32.add
        i32.const -4
        i32.and
        local.tee 2
        local.get 0
        i32.sub
        local.tee 3
        i32.lt_u
        br_if 0 (;@2;)
        local.get 1
        local.get 3
        i32.sub
        local.tee 4
        i32.const 4
        i32.lt_u
        br_if 0 (;@2;)
        local.get 4
        i32.const 3
        i32.and
        local.set 5
        i32.const 0
        local.set 6
        i32.const 0
        local.set 1
        block ;; label = @3
          local.get 2
          local.get 0
          i32.eq
          br_if 0 (;@3;)
          i32.const 0
          local.set 7
          i32.const 0
          local.set 1
          block ;; label = @4
            local.get 0
            local.get 2
            i32.sub
            local.tee 8
            i32.const -4
            i32.gt_u
            br_if 0 (;@4;)
            i32.const 0
            local.set 7
            i32.const 0
            local.set 1
            loop ;; label = @5
              local.get 1
              local.get 0
              local.get 7
              i32.add
              local.tee 2
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get 2
              i32.const 1
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get 2
              i32.const 2
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get 2
              i32.const 3
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.set 1
              local.get 7
              i32.const 4
              i32.add
              local.tee 7
              br_if 0 (;@5;)
            end
          end
          local.get 0
          local.get 7
          i32.add
          local.set 2
          loop ;; label = @4
            local.get 1
            local.get 2
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set 1
            local.get 2
            i32.const 1
            i32.add
            local.set 2
            local.get 8
            i32.const 1
            i32.add
            local.tee 8
            br_if 0 (;@4;)
          end
        end
        local.get 0
        local.get 3
        i32.add
        local.set 8
        block ;; label = @3
          local.get 5
          i32.eqz
          br_if 0 (;@3;)
          local.get 8
          local.get 4
          i32.const -4
          i32.and
          i32.add
          local.tee 2
          i32.load8_s
          i32.const -65
          i32.gt_s
          local.set 6
          local.get 5
          i32.const 1
          i32.eq
          br_if 0 (;@3;)
          local.get 6
          local.get 2
          i32.load8_s offset=1
          i32.const -65
          i32.gt_s
          i32.add
          local.set 6
          local.get 5
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get 6
          local.get 2
          i32.load8_s offset=2
          i32.const -65
          i32.gt_s
          i32.add
          local.set 6
        end
        local.get 4
        i32.const 2
        i32.shr_u
        local.set 3
        local.get 6
        local.get 1
        i32.add
        local.set 7
        loop ;; label = @3
          local.get 8
          local.set 6
          local.get 3
          i32.eqz
          br_if 2 (;@1;)
          local.get 3
          i32.const 192
          local.get 3
          i32.const 192
          i32.lt_u
          select
          local.tee 4
          i32.const 3
          i32.and
          local.set 5
          block ;; label = @4
            block ;; label = @5
              local.get 4
              i32.const 2
              i32.shl
              local.tee 9
              i32.const 1008
              i32.and
              local.tee 8
              br_if 0 (;@5;)
              i32.const 0
              local.set 2
              br 1 (;@4;)
            end
            i32.const 0
            local.set 2
            local.get 6
            local.set 1
            loop ;; label = @5
              local.get 1
              i32.const 12
              i32.add
              i32.load
              local.tee 0
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 0
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 1
              i32.const 8
              i32.add
              i32.load
              local.tee 0
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 0
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 1
              i32.const 4
              i32.add
              i32.load
              local.tee 0
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 0
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 1
              i32.load
              local.tee 0
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 0
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 2
              i32.add
              i32.add
              i32.add
              i32.add
              local.set 2
              local.get 1
              i32.const 16
              i32.add
              local.set 1
              local.get 8
              i32.const -16
              i32.add
              local.tee 8
              br_if 0 (;@5;)
            end
          end
          local.get 3
          local.get 4
          i32.sub
          local.set 3
          local.get 6
          local.get 9
          i32.add
          local.set 8
          local.get 2
          i32.const 8
          i32.shr_u
          i32.const 16711935
          i32.and
          local.get 2
          i32.const 16711935
          i32.and
          i32.add
          i32.const 65537
          i32.mul
          i32.const 16
          i32.shr_u
          local.get 7
          i32.add
          local.set 7
          local.get 5
          i32.eqz
          br_if 0 (;@3;)
        end
        local.get 6
        local.get 4
        i32.const 252
        i32.and
        i32.const 2
        i32.shl
        i32.add
        local.tee 2
        i32.load
        local.tee 1
        i32.const -1
        i32.xor
        i32.const 7
        i32.shr_u
        local.get 1
        i32.const 6
        i32.shr_u
        i32.or
        i32.const 16843009
        i32.and
        local.set 1
        block ;; label = @3
          local.get 5
          i32.const 1
          i32.eq
          br_if 0 (;@3;)
          local.get 2
          i32.load offset=4
          local.tee 8
          i32.const -1
          i32.xor
          i32.const 7
          i32.shr_u
          local.get 8
          i32.const 6
          i32.shr_u
          i32.or
          i32.const 16843009
          i32.and
          local.get 1
          i32.add
          local.set 1
          local.get 5
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get 2
          i32.load offset=8
          local.tee 2
          i32.const -1
          i32.xor
          i32.const 7
          i32.shr_u
          local.get 2
          i32.const 6
          i32.shr_u
          i32.or
          i32.const 16843009
          i32.and
          local.get 1
          i32.add
          local.set 1
        end
        local.get 1
        i32.const 8
        i32.shr_u
        i32.const 459007
        i32.and
        local.get 1
        i32.const 16711935
        i32.and
        i32.add
        i32.const 65537
        i32.mul
        i32.const 16
        i32.shr_u
        local.get 7
        i32.add
        local.set 7
        br 1 (;@1;)
      end
      block ;; label = @2
        local.get 1
        br_if 0 (;@2;)
        i32.const 0
        return
      end
      local.get 1
      i32.const 3
      i32.and
      local.set 8
      block ;; label = @2
        block ;; label = @3
          local.get 1
          i32.const 4
          i32.ge_u
          br_if 0 (;@3;)
          i32.const 0
          local.set 2
          i32.const 0
          local.set 7
          br 1 (;@2;)
        end
        local.get 1
        i32.const -4
        i32.and
        local.set 3
        i32.const 0
        local.set 2
        i32.const 0
        local.set 7
        loop ;; label = @3
          local.get 7
          local.get 0
          local.get 2
          i32.add
          local.tee 1
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.get 1
          i32.const 1
          i32.add
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.get 1
          i32.const 2
          i32.add
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.get 1
          i32.const 3
          i32.add
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set 7
          local.get 3
          local.get 2
          i32.const 4
          i32.add
          local.tee 2
          i32.ne
          br_if 0 (;@3;)
        end
      end
      local.get 8
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      local.get 2
      i32.add
      local.set 1
      loop ;; label = @2
        local.get 7
        local.get 1
        i32.load8_s
        i32.const -65
        i32.gt_s
        i32.add
        local.set 7
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        local.get 8
        i32.const -1
        i32.add
        local.tee 8
        br_if 0 (;@2;)
      end
    end
    local.get 7
  )
  (func $_ZN4core3fmt9Formatter9write_str17hb5ca0e988d371786E (;60;) (type 1) (param i32 i32 i32) (result i32)
    local.get 0
    i32.load
    local.get 1
    local.get 2
    local.get 0
    i32.load offset=4
    i32.load offset=12
    call_indirect (type 1)
  )
  (data $.rodata (;0;) (i32.const 1048576) "library/alloc/src/raw_vec/mod.rs\00/rust/deps/dlmalloc-0.2.10/src/dlmalloc.rs\00library/std/src/alloc.rs\00/Users/mnaeraxr/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/itoa-1.0.18/src/lib.rs\00\00\00\00e\00\10\00[\00\00\00\bc\00\00\00\01\00\00\00e\00\10\00[\00\00\00L\01\00\00\01\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899|\fd\8b2W\e6W\f9\02\dfD\bf\e3H\e7\afm]\cb\d6,P\ebcxA\a6Wq\1b\8b\b9memory allocation of  bytes failed\00\00\cc\01\10\00\15\00\00\00\e1\01\10\00\0d\00\00\00L\00\10\00\18\00\00\00d\01\00\00\09\00\00\00\03\00\00\00\0c\00\00\00\04\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\00\00\00\00\08\00\00\00\04\00\00\00\07\00\00\00\08\00\00\00\09\00\00\00\0a\00\00\00\0b\00\00\00\10\00\00\00\04\00\00\00\0c\00\00\00\0d\00\00\00\0e\00\00\00\0f\00\00\00\00\00\00\00\08\00\00\00\04\00\00\00\10\00\00\00assertion failed: psize >= size + min_overhead\00\00!\00\10\00*\00\00\00\b1\04\00\00\09\00\00\00assertion failed: psize <= size + max_overhead\00\00!\00\10\00*\00\00\00\b7\04\00\00\0d\00\00\00\03\00\00\00\0c\00\00\00\04\00\00\00\11\00\00\00capacity overflow\00\00\00\00\03\10\00\11\00\00\00\00\00\10\00 \00\00\00\1c\00\00\00\05\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899index out of bounds: the len is  but the index is \00\00\f4\03\10\00 \00\00\00\14\04\10\00\12\00\00\00")
  (@producers
    (language "Rust" "")
    (processed-by "rustc" "1.92.0 (ded5c06cf 2025-12-08)")
  )
  (@custom "target_features" (after data) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
)
