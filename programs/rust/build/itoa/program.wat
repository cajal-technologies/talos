(module $itoa.wasm
  (type (;0;) (func (param i32 i32)))
  (type (;1;) (func (param i32 i32 i32) (result i32)))
  (type (;2;) (func (param i32 i32) (result i32)))
  (type (;3;) (func (param i32 i32 i64)))
  (type (;4;) (func (param i64 i32 i32) (result i32)))
  (type (;5;) (func (param i64) (result i32)))
  (type (;6;) (func (param i32 i32 i32)))
  (type (;7;) (func (param i32 i32 i32 i32) (result i32)))
  (type (;8;) (func))
  (type (;9;) (func (param i64 i32) (result i32)))
  (type (;10;) (func (param i32 i32 i32 i32)))
  (type (;11;) (func (param i32 i32 i32 i32 i32)))
  (type (;12;) (func (param i32)))
  (type (;13;) (func (param i32 i32 i32 i32 i32 i32)))
  (type (;14;) (func (param i32) (result i32)))
  (type (;15;) (func (param i32 i32 i32 i32 i32 i32) (result i32)))
  (type (;16;) (func (param i32 i32 i32 i32 i32) (result i32)))
  (table (;0;) 18 18 funcref)
  (memory (;0;) 17)
  (global $__stack_pointer (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1050193)
  (global (;2;) i32 i32.const 1050208)
  (export "memory" (memory 0))
  (export "itoa_i64" (func $itoa_i64))
  (export "itoa_i64_len" (func $itoa_i64_len))
  (export "itoa_u64" (func $itoa_u64))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (elem (;0;) (i32.const 1) func $_RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook $_RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeNtNtCs5cOc02OMXlo_5alloc6string6StringECsebHcaeoSrxy_3std $_RNvXsZ_NtCs5cOc02OMXlo_5alloc6stringNtB5_6StringNtNtCsgXGp5Oqx2Ny_4core3fmt5Write9write_str $_RNvXsZ_NtCs5cOc02OMXlo_5alloc6stringNtB5_6StringNtNtCsgXGp5Oqx2Ny_4core3fmt5Write10write_char $_RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2Ny_4core3fmt5Write9write_fmtCsebHcaeoSrxy_3std $_RNvXs2_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core3fmt7Display3fmt $_RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload8take_box $_RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload3get $_RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload6as_str $_RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeNtNvNtCsebHcaeoSrxy_3std9panicking13panic_handler19FormatStringPayloadEBM_ $_RNvXs0_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_19FormatStringPayloadNtNtCsgXGp5Oqx2Ny_4core3fmt7Display3fmt $_RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_19FormatStringPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload8take_box $_RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_19FormatStringPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload3get $_RNvYINtNvNtCsebHcaeoSrxy_3std9panicking11begin_panic7PayloadReENtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload6as_strB9_ $_RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoSrxy_3std $_RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6string6StringNtB2_3Any7type_idCsebHcaeoSrxy_3std $_RNvXs8_NtNtNtCsgXGp5Oqx2Ny_4core3fmt3num3impmNtB9_7Display3fmt)
  (func $_ZN4itoa6Buffer6format17h7e2727548709bcfcE (;0;) (type 3) (param i32 i32 i64)
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
    call $_ZN38_$LT$u64$u20$as$u20$itoa..Unsigned$GT$3fmt17h0420962a4d08346dE
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
      call $_ZN4itoa19slice_buffer_to_str17hd1d69bf2c6555a17E
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
    i32.const 1048940
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check
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
    call $_ZN4itoa6Buffer6format17h7e2727548709bcfcE
    i32.const -1
    local.set 4
    block ;; label = @1
      local.get 3
      i32.load offset=4
      local.tee 5
      local.get 2
      i32.gt_s
      br_if 0 (;@1;)
      local.get 1
      local.get 5
      local.get 3
      i32.load
      local.get 5
      i32.const 1048956
      call $_RINvNtCsgXGp5Oqx2Ny_4core5slice20copy_from_slice_implhECs4wvrbUR2I4G_11miniz_oxide
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
    call $_ZN4itoa6Buffer6format17h7e2727548709bcfcE
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
    call $_ZN38_$LT$u64$u20$as$u20$itoa..Unsigned$GT$3fmt17h0420962a4d08346dE
    call $_ZN4itoa19slice_buffer_to_str17hd1d69bf2c6555a17E
    i32.const -1
    local.set 4
    block ;; label = @1
      local.get 3
      i32.load offset=4
      local.tee 5
      local.get 2
      i32.gt_s
      br_if 0 (;@1;)
      local.get 1
      local.get 5
      local.get 3
      i32.load
      local.get 5
      i32.const 1048972
      call $_RINvNtCsgXGp5Oqx2Ny_4core5slice20copy_from_slice_implhECs4wvrbUR2I4G_11miniz_oxide
      local.get 5
      local.set 4
    end
    local.get 3
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get 4
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc12___rust_alloc (;4;) (type 2) (param i32 i32) (result i32)
    local.get 0
    local.get 1
    call $_RNvCsfLfy6EI15iL_7___rustc11___rdl_alloc
    return
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc14___rust_dealloc (;5;) (type 6) (param i32 i32 i32)
    local.get 0
    local.get 1
    local.get 2
    call $_RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc
    return
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc14___rust_realloc (;6;) (type 7) (param i32 i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    call $_RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc
    return
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc35___rust_no_alloc_shim_is_unstable_v2 (;7;) (type 8)
    return
  )
  (func $_ZN38_$LT$u64$u20$as$u20$itoa..Unsigned$GT$3fmt17h0420962a4d08346dE (;8;) (type 9) (param i64 i32) (result i32)
    (local i32 i64 i32 i64 i32 i32)
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
            i32.const -4
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
            i32.load16_u offset=1049004
            i32.store16 align=1
            local.get 4
            i32.const -2
            i32.add
            local.get 7
            i32.const -100
            i32.mul
            local.get 6
            i32.add
            i32.const 1
            i32.shl
            i32.load16_u offset=1049004
            i32.store16 align=1
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
          i32.load8_u offset=1049005
          i32.store8
          local.get 1
          local.get 4
          i32.add
          local.get 2
          i32.load8_u offset=1049004
          i32.store8
          local.get 6
          i64.extend_i32_u
          local.set 3
          br 2 (;@1;)
        end
        local.get 4
        i32.const 20
        i32.const 1048988
        call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check
        unreachable
      end
      i32.const -4
      i32.const 20
      i32.const 1048988
      call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check
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
    i32.const 1048988
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check
    unreachable
  )
  (func $_ZN4itoa19slice_buffer_to_str17hd1d69bf2c6555a17E (;9;) (type 10) (param i32 i32 i32 i32)
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
  (func $_RNvCsfLfy6EI15iL_7___rustc18___rust_start_panic (;10;) (type 2) (param i32 i32) (result i32)
    call $_RNvCsfLfy6EI15iL_7___rustc12___rust_abort
    unreachable
  )
  (func $_RINvNvMs2_NtCs5cOc02OMXlo_5alloc7raw_vecINtB8_11RawVecInnerpE7reserve21do_reserve_and_handleNtNtBa_5alloc6GlobalECsebHcaeoSrxy_3std (;11;) (type 11) (param i32 i32 i32 i32 i32)
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
      call $_RNvNtCs5cOc02OMXlo_5alloc7raw_vec12handle_error
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
    call $_RNvMs4_NtCs5cOc02OMXlo_5alloc7raw_vecNtB5_11RawVecInner11finish_growCsebHcaeoSrxy_3std
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
      call $_RNvNtCs5cOc02OMXlo_5alloc7raw_vec12handle_error
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
  (func $_RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeINtNtB4_6option6OptionINtNtCs5cOc02OMXlo_5alloc3vec3VechEEECsebHcaeoSrxy_3std (;12;) (type 0) (param i32 i32)
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
      call $_RNvCsfLfy6EI15iL_7___rustc14___rust_dealloc
    end
  )
  (func $_RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeNtNtCs5cOc02OMXlo_5alloc6string6StringECsebHcaeoSrxy_3std (;13;) (type 12) (param i32)
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
      call $_RNvCsfLfy6EI15iL_7___rustc14___rust_dealloc
    end
  )
  (func $_RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeNtNvNtCsebHcaeoSrxy_3std9panicking13panic_handler19FormatStringPayloadEBM_ (;14;) (type 12) (param i32)
    (local i32)
    block ;; label = @1
      local.get 0
      i32.load
      local.tee 1
      i32.const 1
      i32.lt_s
      br_if 0 (;@1;)
      local.get 0
      i32.load offset=4
      local.get 1
      i32.const 1
      call $_RNvCsfLfy6EI15iL_7___rustc14___rust_dealloc
    end
  )
  (func $_RINvNtNtCsebHcaeoSrxy_3std3sys9backtrace26___rust_end_short_backtraceNCNvNtB6_5alloc8rust_oom0zEB6_ (;15;) (type 12) (param i32)
    local.get 0
    call $_RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_
    unreachable
  )
  (func $_RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ (;16;) (type 12) (param i32)
    local.get 0
    i32.load
    local.get 0
    i32.load offset=4
    i32.const 0
    i32.load offset=1049720
    local.tee 0
    i32.const 1
    local.get 0
    select
    call_indirect (type 0)
    unreachable
  )
  (func $_RINvNtNtCsebHcaeoSrxy_3std3sys9backtrace26___rust_end_short_backtraceNCNvNtB6_9panicking13panic_handler0zEB6_ (;17;) (type 12) (param i32)
    local.get 0
    call $_RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_
    unreachable
  )
  (func $_RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ (;18;) (type 12) (param i32)
    (local i32 i32 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 1
    global.set $__stack_pointer
    block ;; label = @1
      local.get 0
      i32.load
      local.tee 2
      i32.load offset=4
      local.tee 3
      i32.const 1
      i32.and
      i32.eqz
      br_if 0 (;@1;)
      local.get 2
      i32.load
      local.set 2
      local.get 1
      local.get 3
      i32.const 1
      i32.shr_u
      i32.store offset=4
      local.get 1
      local.get 2
      i32.store
      local.get 1
      i32.const 1049228
      local.get 0
      i32.load offset=4
      local.get 0
      i32.load offset=8
      local.tee 0
      i32.load8_u offset=8
      local.get 0
      i32.load8_u offset=9
      call $_RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook
      unreachable
    end
    local.get 1
    i32.const -2147483648
    i32.store
    local.get 1
    local.get 0
    i32.store offset=12
    local.get 1
    i32.const 1049256
    local.get 0
    i32.load offset=4
    local.get 0
    i32.load offset=8
    local.tee 0
    i32.load8_u offset=8
    local.get 0
    i32.load8_u offset=9
    call $_RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook
    unreachable
  )
  (func $_RNvMs4_NtCs5cOc02OMXlo_5alloc7raw_vecNtB5_11RawVecInner11finish_growCsebHcaeoSrxy_3std (;19;) (type 13) (param i32 i32 i32 i32 i32 i32)
    (local i32 i32 i64)
    i32.const 1
    local.set 6
    i32.const 4
    local.set 7
    block ;; label = @1
      block ;; label = @2
        local.get 5
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
              call $_RNvCsfLfy6EI15iL_7___rustc14___rust_realloc
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
            call $_RNvCsfLfy6EI15iL_7___rustc35___rust_no_alloc_shim_is_unstable_v2
            local.get 3
            local.get 4
            call $_RNvCsfLfy6EI15iL_7___rustc12___rust_alloc
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
  (func $_RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook (;20;) (type 11) (param i32 i32 i32 i32 i32)
    (local i32 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 5
    global.set $__stack_pointer
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              i32.const 1
              call $_RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase
              i32.const 255
              i32.and
              br_table 4 (;@1;) 1 (;@4;) 0 (;@5;) 1 (;@4;)
            end
            i32.const 0
            i32.load offset=1049724
            local.tee 6
            i32.const -1
            i32.le_s
            br_if 3 (;@1;)
            i32.const 0
            local.get 6
            i32.const 1
            i32.add
            i32.store offset=1049724
            i32.const 0
            i32.load offset=1049728
            i32.eqz
            br_if 1 (;@3;)
            local.get 5
            i32.const 8
            i32.add
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
            i64.load offset=8
            i64.store offset=16 align=4
            i32.const 0
            i32.load offset=1049728
            local.get 5
            i32.const 16
            i32.add
            i32.const 0
            i32.load offset=1049732
            i32.load offset=20
            call_indirect (type 0)
            br 2 (;@2;)
          end
          local.get 5
          local.get 0
          local.get 1
          i32.load offset=24
          call_indirect (type 0)
          br 2 (;@1;)
        end
        i32.const -2147483648
        local.get 5
        call $_RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeINtNtB4_6option6OptionINtNtCs5cOc02OMXlo_5alloc3vec3VechEEECsebHcaeoSrxy_3std
      end
      i32.const 0
      i32.const 0
      i32.load offset=1049724
      i32.const -1
      i32.add
      i32.store offset=1049724
      i32.const 0
      i32.const 0
      i32.store8 offset=1049716
      local.get 3
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      local.get 1
      call $_RNvCsfLfy6EI15iL_7___rustc10rust_panic
      unreachable
    end
    unreachable
  )
  (func $_RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook (;21;) (type 0) (param i32 i32)
    i32.const 0
    i32.const 1
    i32.store8 offset=1050192
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc10rust_panic (;22;) (type 0) (param i32 i32)
    local.get 0
    local.get 1
    call $_RNvCsfLfy6EI15iL_7___rustc18___rust_start_panic
    drop
    unreachable
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc11___rdl_alloc (;23;) (type 2) (param i32 i32) (result i32)
    block ;; label = @1
      local.get 1
      i32.const 9
      i32.lt_u
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCsebHcaeoSrxy_3std
      return
    end
    local.get 0
    call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCsebHcaeoSrxy_3std
  )
  (func $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCsebHcaeoSrxy_3std (;24;) (type 2) (param i32 i32) (result i32)
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
      call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCsebHcaeoSrxy_3std
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
          call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCsebHcaeoSrxy_3std
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
        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCsebHcaeoSrxy_3std
      end
      local.get 0
      i32.const 8
      i32.add
      local.set 2
    end
    local.get 2
  )
  (func $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCsebHcaeoSrxy_3std (;25;) (type 14) (param i32) (result i32)
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
            local.get 0
            i32.const 245
            i32.lt_u
            br_if 0 (;@4;)
            block ;; label = @5
              local.get 0
              i32.const -65588
              i32.le_u
              br_if 0 (;@5;)
              i32.const 0
              local.set 0
              br 4 (;@1;)
            end
            local.get 0
            i32.const 11
            i32.add
            local.tee 2
            i32.const -8
            i32.and
            local.set 3
            i32.const 0
            i32.load offset=1050152
            local.tee 4
            i32.eqz
            br_if 2 (;@2;)
            i32.const 31
            local.set 5
            local.get 0
            i32.const 16777205
            i32.ge_u
            br_if 1 (;@3;)
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
            br 1 (;@3;)
          end
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    block ;; label = @9
                      i32.const 0
                      i32.load offset=1050148
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
                      br_if 0 (;@9;)
                      local.get 0
                      i32.const -1
                      i32.xor
                      i32.const 1
                      i32.and
                      local.get 2
                      i32.add
                      local.tee 7
                      i32.const 3
                      i32.shl
                      local.tee 3
                      i32.const 1049884
                      i32.add
                      local.tee 0
                      local.get 3
                      i32.const 1049892
                      i32.add
                      i32.load
                      local.tee 2
                      i32.load offset=8
                      local.tee 8
                      i32.eq
                      br_if 1 (;@8;)
                      local.get 8
                      local.get 0
                      i32.store offset=12
                      local.get 0
                      local.get 8
                      i32.store offset=8
                      br 2 (;@7;)
                    end
                    local.get 3
                    i32.const 0
                    i32.load offset=1050156
                    i32.le_u
                    br_if 6 (;@2;)
                    local.get 0
                    br_if 2 (;@6;)
                    i32.const 0
                    i32.load offset=1050152
                    local.tee 0
                    i32.eqz
                    br_if 6 (;@2;)
                    local.get 0
                    i32.ctz
                    i32.const 2
                    i32.shl
                    i32.const 1049740
                    i32.add
                    i32.load
                    local.tee 8
                    i32.load offset=4
                    i32.const -8
                    i32.and
                    local.get 3
                    i32.sub
                    local.set 2
                    local.get 8
                    local.set 6
                    loop ;; label = @9
                      block ;; label = @10
                        local.get 8
                        i32.load offset=16
                        local.tee 0
                        br_if 0 (;@10;)
                        local.get 8
                        i32.load offset=20
                        local.tee 0
                        br_if 0 (;@10;)
                        local.get 6
                        i32.load offset=24
                        local.set 5
                        block ;; label = @11
                          block ;; label = @12
                            block ;; label = @13
                              local.get 6
                              i32.load offset=12
                              local.tee 0
                              local.get 6
                              i32.ne
                              br_if 0 (;@13;)
                              local.get 6
                              i32.const 20
                              i32.const 16
                              local.get 6
                              i32.load offset=20
                              local.tee 0
                              select
                              i32.add
                              i32.load
                              local.tee 8
                              br_if 1 (;@12;)
                              i32.const 0
                              local.set 0
                              br 2 (;@11;)
                            end
                            local.get 6
                            i32.load offset=8
                            local.tee 8
                            local.get 0
                            i32.store offset=12
                            local.get 0
                            local.get 8
                            i32.store offset=8
                            br 1 (;@11;)
                          end
                          local.get 6
                          i32.const 20
                          i32.add
                          local.get 6
                          i32.const 16
                          i32.add
                          local.get 0
                          select
                          local.set 7
                          loop ;; label = @12
                            local.get 7
                            local.set 9
                            local.get 8
                            local.tee 0
                            i32.const 20
                            i32.add
                            local.get 0
                            i32.const 16
                            i32.add
                            local.get 0
                            i32.load offset=20
                            local.tee 8
                            select
                            local.set 7
                            local.get 0
                            i32.const 20
                            i32.const 16
                            local.get 8
                            select
                            i32.add
                            i32.load
                            local.tee 8
                            br_if 0 (;@12;)
                          end
                          local.get 9
                          i32.const 0
                          i32.store
                        end
                        local.get 5
                        i32.eqz
                        br_if 6 (;@4;)
                        block ;; label = @11
                          block ;; label = @12
                            local.get 6
                            local.get 6
                            i32.load offset=28
                            i32.const 2
                            i32.shl
                            i32.const 1049740
                            i32.add
                            local.tee 8
                            i32.load
                            i32.eq
                            br_if 0 (;@12;)
                            block ;; label = @13
                              local.get 5
                              i32.load offset=16
                              local.get 6
                              i32.eq
                              br_if 0 (;@13;)
                              local.get 5
                              local.get 0
                              i32.store offset=20
                              local.get 0
                              br_if 2 (;@11;)
                              br 9 (;@4;)
                            end
                            local.get 5
                            local.get 0
                            i32.store offset=16
                            local.get 0
                            br_if 1 (;@11;)
                            br 8 (;@4;)
                          end
                          local.get 8
                          local.get 0
                          i32.store
                          local.get 0
                          i32.eqz
                          br_if 6 (;@5;)
                        end
                        local.get 0
                        local.get 5
                        i32.store offset=24
                        block ;; label = @11
                          local.get 6
                          i32.load offset=16
                          local.tee 8
                          i32.eqz
                          br_if 0 (;@11;)
                          local.get 0
                          local.get 8
                          i32.store offset=16
                          local.get 8
                          local.get 0
                          i32.store offset=24
                        end
                        local.get 6
                        i32.load offset=20
                        local.tee 8
                        i32.eqz
                        br_if 6 (;@4;)
                        local.get 0
                        local.get 8
                        i32.store offset=20
                        local.get 8
                        local.get 0
                        i32.store offset=24
                        br 6 (;@4;)
                      end
                      local.get 0
                      i32.load offset=4
                      i32.const -8
                      i32.and
                      local.get 3
                      i32.sub
                      local.tee 8
                      local.get 2
                      local.get 8
                      local.get 2
                      i32.lt_u
                      local.tee 8
                      select
                      local.set 2
                      local.get 0
                      local.get 6
                      local.get 8
                      select
                      local.set 6
                      local.get 0
                      local.set 8
                      br 0 (;@9;)
                    end
                  end
                  i32.const 0
                  local.get 6
                  i32.const -2
                  local.get 7
                  i32.rotl
                  i32.and
                  i32.store offset=1050148
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
                br 5 (;@1;)
              end
              block ;; label = @6
                block ;; label = @7
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
                  i32.const 1049884
                  i32.add
                  local.tee 8
                  local.get 2
                  i32.const 1049892
                  i32.add
                  i32.load
                  local.tee 0
                  i32.load offset=8
                  local.tee 7
                  i32.eq
                  br_if 0 (;@7;)
                  local.get 7
                  local.get 8
                  i32.store offset=12
                  local.get 8
                  local.get 7
                  i32.store offset=8
                  br 1 (;@6;)
                end
                i32.const 0
                local.get 6
                i32.const -2
                local.get 9
                i32.rotl
                i32.and
                i32.store offset=1050148
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
              local.tee 8
              i32.const 1
              i32.or
              i32.store offset=4
              local.get 0
              local.get 2
              i32.add
              local.get 8
              i32.store
              block ;; label = @6
                i32.const 0
                i32.load offset=1050156
                local.tee 2
                i32.eqz
                br_if 0 (;@6;)
                i32.const 0
                i32.load offset=1050164
                local.set 3
                block ;; label = @7
                  block ;; label = @8
                    i32.const 0
                    i32.load offset=1050148
                    local.tee 7
                    i32.const 1
                    local.get 2
                    i32.const 3
                    i32.shr_u
                    i32.shl
                    local.tee 9
                    i32.and
                    br_if 0 (;@8;)
                    i32.const 0
                    local.get 7
                    local.get 9
                    i32.or
                    i32.store offset=1050148
                    local.get 2
                    i32.const -8
                    i32.and
                    i32.const 1049884
                    i32.add
                    local.tee 2
                    local.set 7
                    br 1 (;@7;)
                  end
                  local.get 2
                  i32.const -8
                  i32.and
                  local.tee 2
                  i32.const 1049884
                  i32.add
                  local.set 7
                  local.get 2
                  i32.const 1049892
                  i32.add
                  i32.load
                  local.set 2
                end
                local.get 7
                local.get 3
                i32.store offset=8
                local.get 2
                local.get 3
                i32.store offset=12
                local.get 3
                local.get 7
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
              i32.store offset=1050164
              i32.const 0
              local.get 8
              i32.store offset=1050156
              br 4 (;@1;)
            end
            i32.const 0
            i32.const 0
            i32.load offset=1050152
            i32.const -2
            local.get 6
            i32.load offset=28
            i32.rotl
            i32.and
            i32.store offset=1050152
          end
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                local.get 2
                i32.const 16
                i32.lt_u
                br_if 0 (;@6;)
                local.get 6
                local.get 3
                i32.const 3
                i32.or
                i32.store offset=4
                local.get 6
                local.get 3
                i32.add
                local.tee 8
                local.get 2
                i32.const 1
                i32.or
                i32.store offset=4
                local.get 8
                local.get 2
                i32.add
                local.get 2
                i32.store
                i32.const 0
                i32.load offset=1050156
                local.tee 7
                i32.eqz
                br_if 1 (;@5;)
                i32.const 0
                i32.load offset=1050164
                local.set 0
                block ;; label = @7
                  block ;; label = @8
                    i32.const 0
                    i32.load offset=1050148
                    local.tee 9
                    i32.const 1
                    local.get 7
                    i32.const 3
                    i32.shr_u
                    i32.shl
                    local.tee 5
                    i32.and
                    br_if 0 (;@8;)
                    i32.const 0
                    local.get 9
                    local.get 5
                    i32.or
                    i32.store offset=1050148
                    local.get 7
                    i32.const -8
                    i32.and
                    i32.const 1049884
                    i32.add
                    local.tee 7
                    local.set 9
                    br 1 (;@7;)
                  end
                  local.get 7
                  i32.const -8
                  i32.and
                  local.tee 7
                  i32.const 1049884
                  i32.add
                  local.set 9
                  local.get 7
                  i32.const 1049892
                  i32.add
                  i32.load
                  local.set 7
                end
                local.get 9
                local.get 0
                i32.store offset=8
                local.get 7
                local.get 0
                i32.store offset=12
                local.get 0
                local.get 9
                i32.store offset=12
                local.get 0
                local.get 7
                i32.store offset=8
                br 1 (;@5;)
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
              br 1 (;@4;)
            end
            i32.const 0
            local.get 8
            i32.store offset=1050164
            i32.const 0
            local.get 2
            i32.store offset=1050156
          end
          local.get 6
          i32.const 8
          i32.add
          local.tee 0
          i32.eqz
          br_if 1 (;@2;)
          br 2 (;@1;)
        end
        i32.const 0
        local.get 3
        i32.sub
        local.set 2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                local.get 5
                i32.const 2
                i32.shl
                i32.const 1049740
                i32.add
                i32.load
                local.tee 6
                br_if 0 (;@6;)
                i32.const 0
                local.set 8
                i32.const 0
                local.set 0
                br 1 (;@5;)
              end
              i32.const 0
              local.set 8
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
              local.set 7
              i32.const 0
              local.set 0
              loop ;; label = @6
                block ;; label = @7
                  local.get 6
                  local.tee 6
                  i32.load offset=4
                  i32.const -8
                  i32.and
                  local.tee 9
                  local.get 3
                  i32.lt_u
                  br_if 0 (;@7;)
                  local.get 9
                  local.get 3
                  i32.sub
                  local.tee 9
                  local.get 2
                  i32.ge_u
                  br_if 0 (;@7;)
                  local.get 6
                  local.set 8
                  local.get 9
                  local.set 2
                  local.get 9
                  br_if 0 (;@7;)
                  i32.const 0
                  local.set 2
                  local.get 6
                  local.set 0
                  local.get 6
                  local.set 8
                  br 3 (;@4;)
                end
                local.get 6
                i32.load offset=20
                local.tee 9
                local.get 0
                local.get 9
                local.get 6
                local.get 7
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
                local.get 7
                i32.const 1
                i32.shl
                local.set 7
                local.get 6
                br_if 0 (;@6;)
              end
            end
            block ;; label = @5
              local.get 0
              local.get 8
              i32.or
              br_if 0 (;@5;)
              i32.const 0
              local.set 8
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
              i32.const 1049740
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
            local.tee 7
            local.get 2
            local.get 7
            local.get 2
            i32.lt_u
            local.tee 9
            select
            local.set 5
            local.get 6
            local.get 3
            i32.lt_u
            local.set 7
            local.get 0
            local.get 8
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
            local.get 7
            select
            local.set 2
            local.get 8
            local.get 9
            local.get 7
            select
            local.set 8
            local.get 6
            local.set 0
            local.get 6
            br_if 0 (;@4;)
          end
        end
        local.get 8
        i32.eqz
        br_if 0 (;@2;)
        block ;; label = @3
          i32.const 0
          i32.load offset=1050156
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
        local.get 8
        i32.load offset=24
        local.set 5
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 8
              i32.load offset=12
              local.tee 0
              local.get 8
              i32.ne
              br_if 0 (;@5;)
              local.get 8
              i32.const 20
              i32.const 16
              local.get 8
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
            local.get 8
            i32.load offset=8
            local.tee 6
            local.get 0
            i32.store offset=12
            local.get 0
            local.get 6
            i32.store offset=8
            br 1 (;@3;)
          end
          local.get 8
          i32.const 20
          i32.add
          local.get 8
          i32.const 16
          i32.add
          local.get 0
          select
          local.set 7
          loop ;; label = @4
            local.get 7
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
            local.set 7
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
                local.get 8
                local.get 8
                i32.load offset=28
                i32.const 2
                i32.shl
                i32.const 1049740
                i32.add
                local.tee 6
                i32.load
                i32.eq
                br_if 0 (;@6;)
                block ;; label = @7
                  local.get 5
                  i32.load offset=16
                  local.get 8
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
              local.get 8
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
            local.get 8
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
          i32.load offset=1050152
          i32.const -2
          local.get 8
          i32.load offset=28
          i32.rotl
          i32.and
          i32.store offset=1050152
        end
        block ;; label = @3
          block ;; label = @4
            local.get 2
            i32.const 16
            i32.lt_u
            br_if 0 (;@4;)
            local.get 8
            local.get 3
            i32.const 3
            i32.or
            i32.store offset=4
            local.get 8
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
              call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCsebHcaeoSrxy_3std
              br 2 (;@3;)
            end
            block ;; label = @5
              block ;; label = @6
                i32.const 0
                i32.load offset=1050148
                local.tee 6
                i32.const 1
                local.get 2
                i32.const 3
                i32.shr_u
                i32.shl
                local.tee 7
                i32.and
                br_if 0 (;@6;)
                i32.const 0
                local.get 6
                local.get 7
                i32.or
                i32.store offset=1050148
                local.get 2
                i32.const 248
                i32.and
                i32.const 1049884
                i32.add
                local.tee 2
                local.set 6
                br 1 (;@5;)
              end
              local.get 2
              i32.const 248
              i32.and
              local.tee 2
              i32.const 1049884
              i32.add
              local.set 6
              local.get 2
              i32.const 1049892
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
          local.get 8
          local.get 2
          local.get 3
          i32.add
          local.tee 0
          i32.const 3
          i32.or
          i32.store offset=4
          local.get 8
          local.get 0
          i32.add
          local.tee 0
          local.get 0
          i32.load offset=4
          i32.const 1
          i32.or
          i32.store offset=4
        end
        local.get 8
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
                  i32.load offset=1050156
                  local.tee 0
                  local.get 3
                  i32.ge_u
                  br_if 0 (;@7;)
                  block ;; label = @8
                    i32.const 0
                    i32.load offset=1050160
                    local.tee 0
                    local.get 3
                    i32.gt_u
                    br_if 0 (;@8;)
                    local.get 1
                    i32.const 4
                    i32.add
                    i32.const 1050192
                    local.get 3
                    i32.const 65583
                    i32.add
                    i32.const -65536
                    i32.and
                    call $_RNvXs_NtCsjqx8TIyZbP9_8dlmalloc3sysNtB4_6SystemNtB6_9Allocator5alloc
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
                    i32.load offset=1050172
                    local.get 1
                    i32.load offset=8
                    local.tee 9
                    i32.add
                    local.tee 0
                    i32.store offset=1050172
                    i32.const 0
                    local.get 0
                    i32.const 0
                    i32.load offset=1050176
                    local.tee 2
                    local.get 0
                    local.get 2
                    i32.gt_u
                    select
                    i32.store offset=1050176
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          i32.const 0
                          i32.load offset=1050168
                          local.tee 2
                          i32.eqz
                          br_if 0 (;@11;)
                          i32.const 1049868
                          local.set 0
                          loop ;; label = @12
                            local.get 6
                            local.get 0
                            i32.load
                            local.tee 8
                            local.get 0
                            i32.load offset=4
                            local.tee 7
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
                            i32.load offset=1050184
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
                          i32.store offset=1050184
                        end
                        i32.const 0
                        i32.const 4095
                        i32.store offset=1050188
                        i32.const 0
                        local.get 5
                        i32.store offset=1049880
                        i32.const 0
                        local.get 9
                        i32.store offset=1049872
                        i32.const 0
                        local.get 6
                        i32.store offset=1049868
                        i32.const 0
                        i32.const 1049884
                        i32.store offset=1049896
                        i32.const 0
                        i32.const 1049892
                        i32.store offset=1049904
                        i32.const 0
                        i32.const 1049884
                        i32.store offset=1049892
                        i32.const 0
                        i32.const 1049900
                        i32.store offset=1049912
                        i32.const 0
                        i32.const 1049892
                        i32.store offset=1049900
                        i32.const 0
                        i32.const 1049908
                        i32.store offset=1049920
                        i32.const 0
                        i32.const 1049900
                        i32.store offset=1049908
                        i32.const 0
                        i32.const 1049916
                        i32.store offset=1049928
                        i32.const 0
                        i32.const 1049908
                        i32.store offset=1049916
                        i32.const 0
                        i32.const 1049924
                        i32.store offset=1049936
                        i32.const 0
                        i32.const 1049916
                        i32.store offset=1049924
                        i32.const 0
                        i32.const 1049932
                        i32.store offset=1049944
                        i32.const 0
                        i32.const 1049924
                        i32.store offset=1049932
                        i32.const 0
                        i32.const 1049940
                        i32.store offset=1049952
                        i32.const 0
                        i32.const 1049932
                        i32.store offset=1049940
                        i32.const 0
                        i32.const 1049948
                        i32.store offset=1049960
                        i32.const 0
                        i32.const 1049940
                        i32.store offset=1049948
                        i32.const 0
                        i32.const 1049948
                        i32.store offset=1049956
                        i32.const 0
                        i32.const 1049956
                        i32.store offset=1049968
                        i32.const 0
                        i32.const 1049956
                        i32.store offset=1049964
                        i32.const 0
                        i32.const 1049964
                        i32.store offset=1049976
                        i32.const 0
                        i32.const 1049964
                        i32.store offset=1049972
                        i32.const 0
                        i32.const 1049972
                        i32.store offset=1049984
                        i32.const 0
                        i32.const 1049972
                        i32.store offset=1049980
                        i32.const 0
                        i32.const 1049980
                        i32.store offset=1049992
                        i32.const 0
                        i32.const 1049980
                        i32.store offset=1049988
                        i32.const 0
                        i32.const 1049988
                        i32.store offset=1050000
                        i32.const 0
                        i32.const 1049988
                        i32.store offset=1049996
                        i32.const 0
                        i32.const 1049996
                        i32.store offset=1050008
                        i32.const 0
                        i32.const 1049996
                        i32.store offset=1050004
                        i32.const 0
                        i32.const 1050004
                        i32.store offset=1050016
                        i32.const 0
                        i32.const 1050004
                        i32.store offset=1050012
                        i32.const 0
                        i32.const 1050012
                        i32.store offset=1050024
                        i32.const 0
                        i32.const 1050020
                        i32.store offset=1050032
                        i32.const 0
                        i32.const 1050012
                        i32.store offset=1050020
                        i32.const 0
                        i32.const 1050028
                        i32.store offset=1050040
                        i32.const 0
                        i32.const 1050020
                        i32.store offset=1050028
                        i32.const 0
                        i32.const 1050036
                        i32.store offset=1050048
                        i32.const 0
                        i32.const 1050028
                        i32.store offset=1050036
                        i32.const 0
                        i32.const 1050044
                        i32.store offset=1050056
                        i32.const 0
                        i32.const 1050036
                        i32.store offset=1050044
                        i32.const 0
                        i32.const 1050052
                        i32.store offset=1050064
                        i32.const 0
                        i32.const 1050044
                        i32.store offset=1050052
                        i32.const 0
                        i32.const 1050060
                        i32.store offset=1050072
                        i32.const 0
                        i32.const 1050052
                        i32.store offset=1050060
                        i32.const 0
                        i32.const 1050068
                        i32.store offset=1050080
                        i32.const 0
                        i32.const 1050060
                        i32.store offset=1050068
                        i32.const 0
                        i32.const 1050076
                        i32.store offset=1050088
                        i32.const 0
                        i32.const 1050068
                        i32.store offset=1050076
                        i32.const 0
                        i32.const 1050084
                        i32.store offset=1050096
                        i32.const 0
                        i32.const 1050076
                        i32.store offset=1050084
                        i32.const 0
                        i32.const 1050092
                        i32.store offset=1050104
                        i32.const 0
                        i32.const 1050084
                        i32.store offset=1050092
                        i32.const 0
                        i32.const 1050100
                        i32.store offset=1050112
                        i32.const 0
                        i32.const 1050092
                        i32.store offset=1050100
                        i32.const 0
                        i32.const 1050108
                        i32.store offset=1050120
                        i32.const 0
                        i32.const 1050100
                        i32.store offset=1050108
                        i32.const 0
                        i32.const 1050116
                        i32.store offset=1050128
                        i32.const 0
                        i32.const 1050108
                        i32.store offset=1050116
                        i32.const 0
                        i32.const 1050124
                        i32.store offset=1050136
                        i32.const 0
                        i32.const 1050116
                        i32.store offset=1050124
                        i32.const 0
                        i32.const 1050132
                        i32.store offset=1050144
                        i32.const 0
                        i32.const 1050124
                        i32.store offset=1050132
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
                        i32.store offset=1050168
                        i32.const 0
                        i32.const 1050132
                        i32.store offset=1050140
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
                        local.tee 8
                        i32.store offset=1050160
                        local.get 2
                        local.get 8
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
                        i32.store offset=1050180
                        br 8 (;@2;)
                      end
                      local.get 2
                      local.get 6
                      i32.ge_u
                      br_if 0 (;@9;)
                      local.get 8
                      local.get 2
                      i32.gt_u
                      br_if 0 (;@9;)
                      local.get 0
                      i32.load offset=12
                      local.tee 8
                      i32.const 1
                      i32.and
                      br_if 0 (;@9;)
                      local.get 8
                      i32.const 1
                      i32.shr_u
                      local.get 5
                      i32.eq
                      br_if 3 (;@6;)
                    end
                    i32.const 0
                    i32.const 0
                    i32.load offset=1050184
                    local.tee 0
                    local.get 6
                    local.get 0
                    local.get 6
                    i32.lt_u
                    select
                    i32.store offset=1050184
                    local.get 6
                    local.get 9
                    i32.add
                    local.set 8
                    i32.const 1049868
                    local.set 0
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          loop ;; label = @12
                            local.get 0
                            i32.load
                            local.tee 7
                            local.get 8
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
                        local.tee 8
                        i32.const 1
                        i32.and
                        br_if 0 (;@10;)
                        local.get 8
                        i32.const 1
                        i32.shr_u
                        local.get 5
                        i32.eq
                        br_if 1 (;@9;)
                      end
                      i32.const 1049868
                      local.set 0
                      block ;; label = @10
                        loop ;; label = @11
                          block ;; label = @12
                            local.get 0
                            i32.load
                            local.tee 8
                            local.get 2
                            i32.gt_u
                            br_if 0 (;@12;)
                            local.get 2
                            local.get 8
                            local.get 0
                            i32.load offset=4
                            i32.add
                            local.tee 8
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
                      local.tee 7
                      i32.store offset=1050168
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
                      i32.store offset=1050160
                      local.get 7
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
                      i32.store offset=1050180
                      local.get 2
                      local.get 8
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
                      local.tee 7
                      i32.const 27
                      i32.store offset=4
                      i32.const 0
                      i64.load offset=1049868 align=4
                      local.set 10
                      local.get 7
                      i32.const 16
                      i32.add
                      i32.const 0
                      i64.load offset=1049876 align=4
                      i64.store align=4
                      local.get 7
                      i32.const 8
                      i32.add
                      local.tee 0
                      local.get 10
                      i64.store align=4
                      i32.const 0
                      local.get 5
                      i32.store offset=1049880
                      i32.const 0
                      local.get 9
                      i32.store offset=1049872
                      i32.const 0
                      local.get 6
                      i32.store offset=1049868
                      i32.const 0
                      local.get 0
                      i32.store offset=1049876
                      local.get 7
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
                        local.get 8
                        i32.lt_u
                        br_if 0 (;@10;)
                      end
                      local.get 7
                      local.get 2
                      i32.eq
                      br_if 7 (;@2;)
                      local.get 7
                      local.get 7
                      i32.load offset=4
                      i32.const -2
                      i32.and
                      i32.store offset=4
                      local.get 2
                      local.get 7
                      local.get 2
                      i32.sub
                      local.tee 0
                      i32.const 1
                      i32.or
                      i32.store offset=4
                      local.get 7
                      local.get 0
                      i32.store
                      block ;; label = @10
                        local.get 0
                        i32.const 256
                        i32.lt_u
                        br_if 0 (;@10;)
                        local.get 2
                        local.get 0
                        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCsebHcaeoSrxy_3std
                        br 8 (;@2;)
                      end
                      block ;; label = @10
                        block ;; label = @11
                          i32.const 0
                          i32.load offset=1050148
                          local.tee 8
                          i32.const 1
                          local.get 0
                          i32.const 3
                          i32.shr_u
                          i32.shl
                          local.tee 6
                          i32.and
                          br_if 0 (;@11;)
                          i32.const 0
                          local.get 8
                          local.get 6
                          i32.or
                          i32.store offset=1050148
                          local.get 0
                          i32.const 248
                          i32.and
                          i32.const 1049884
                          i32.add
                          local.tee 0
                          local.set 8
                          br 1 (;@10;)
                        end
                        local.get 0
                        i32.const 248
                        i32.and
                        local.tee 0
                        i32.const 1049884
                        i32.add
                        local.set 8
                        local.get 0
                        i32.const 1049892
                        i32.add
                        i32.load
                        local.set 0
                      end
                      local.get 8
                      local.get 2
                      i32.store offset=8
                      local.get 0
                      local.get 2
                      i32.store offset=12
                      local.get 2
                      local.get 8
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
                    local.tee 8
                    local.get 3
                    i32.const 3
                    i32.or
                    i32.store offset=4
                    local.get 7
                    i32.const 15
                    i32.add
                    i32.const -8
                    i32.and
                    i32.const -8
                    i32.add
                    local.tee 2
                    local.get 8
                    local.get 3
                    i32.add
                    local.tee 0
                    i32.sub
                    local.set 3
                    local.get 2
                    i32.const 0
                    i32.load offset=1050168
                    i32.eq
                    br_if 3 (;@5;)
                    local.get 2
                    i32.const 0
                    i32.load offset=1050164
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
                      call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std
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
                      call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCsebHcaeoSrxy_3std
                      br 6 (;@3;)
                    end
                    block ;; label = @9
                      block ;; label = @10
                        i32.const 0
                        i32.load offset=1050148
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
                        i32.store offset=1050148
                        local.get 3
                        i32.const 248
                        i32.and
                        i32.const 1049884
                        i32.add
                        local.tee 3
                        local.set 2
                        br 1 (;@9;)
                      end
                      local.get 3
                      i32.const 248
                      i32.and
                      local.tee 3
                      i32.const 1049884
                      i32.add
                      local.set 2
                      local.get 3
                      i32.const 1049892
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
                  i32.store offset=1050160
                  i32.const 0
                  i32.const 0
                  i32.load offset=1050168
                  local.tee 0
                  local.get 3
                  i32.add
                  local.tee 8
                  i32.store offset=1050168
                  local.get 8
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
                i32.load offset=1050164
                local.set 2
                block ;; label = @7
                  block ;; label = @8
                    local.get 0
                    local.get 3
                    i32.sub
                    local.tee 8
                    i32.const 15
                    i32.gt_u
                    br_if 0 (;@8;)
                    i32.const 0
                    i32.const 0
                    i32.store offset=1050164
                    i32.const 0
                    i32.const 0
                    i32.store offset=1050156
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
                  local.get 8
                  i32.store offset=1050156
                  i32.const 0
                  local.get 2
                  local.get 3
                  i32.add
                  local.tee 6
                  i32.store offset=1050164
                  local.get 6
                  local.get 8
                  i32.const 1
                  i32.or
                  i32.store offset=4
                  local.get 2
                  local.get 0
                  i32.add
                  local.get 8
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
              local.get 7
              local.get 9
              i32.add
              i32.store offset=4
              i32.const 0
              i32.const 0
              i32.load offset=1050168
              local.tee 0
              i32.const 15
              i32.add
              i32.const -8
              i32.and
              local.tee 2
              i32.const -8
              i32.add
              local.tee 8
              i32.store offset=1050168
              i32.const 0
              local.get 0
              local.get 2
              i32.sub
              i32.const 0
              i32.load offset=1050160
              local.get 9
              i32.add
              local.tee 2
              i32.add
              i32.const 8
              i32.add
              local.tee 6
              i32.store offset=1050160
              local.get 8
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
              i32.store offset=1050180
              br 3 (;@2;)
            end
            i32.const 0
            local.get 0
            i32.store offset=1050168
            i32.const 0
            i32.const 0
            i32.load offset=1050160
            local.get 3
            i32.add
            local.tee 3
            i32.store offset=1050160
            local.get 0
            local.get 3
            i32.const 1
            i32.or
            i32.store offset=4
            br 1 (;@3;)
          end
          i32.const 0
          local.get 0
          i32.store offset=1050164
          i32.const 0
          i32.const 0
          i32.load offset=1050156
          local.get 3
          i32.add
          local.tee 3
          i32.store offset=1050156
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
        local.get 8
        i32.const 8
        i32.add
        local.set 0
        br 1 (;@1;)
      end
      i32.const 0
      local.set 0
      i32.const 0
      i32.load offset=1050160
      local.tee 2
      local.get 3
      i32.le_u
      br_if 0 (;@1;)
      i32.const 0
      local.get 2
      local.get 3
      i32.sub
      local.tee 2
      i32.store offset=1050160
      i32.const 0
      i32.const 0
      i32.load offset=1050168
      local.tee 0
      local.get 3
      i32.add
      local.tee 8
      i32.store offset=1050168
      local.get 8
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
  (func $_RNvCsfLfy6EI15iL_7___rustc12___rust_abort (;26;) (type 8)
    unreachable
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc (;27;) (type 6) (param i32 i32 i32)
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
        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCsebHcaeoSrxy_3std
        return
      end
      i32.const 1049316
      i32.const 46
      i32.const 1049364
      call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic
      unreachable
    end
    i32.const 1049380
    i32.const 46
    i32.const 1049428
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic
    unreachable
  )
  (func $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCsebHcaeoSrxy_3std (;28;) (type 12) (param i32)
    (local i32 i32 i32 i32)
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
          i32.load offset=1050164
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
          i32.store offset=1050156
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
        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std
      end
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    block ;; label = @9
                      local.get 3
                      i32.load offset=4
                      local.tee 2
                      i32.const 2
                      i32.and
                      br_if 0 (;@9;)
                      local.get 3
                      i32.const 0
                      i32.load offset=1050168
                      i32.eq
                      br_if 2 (;@7;)
                      local.get 3
                      i32.const 0
                      i32.load offset=1050164
                      i32.eq
                      br_if 3 (;@6;)
                      local.get 3
                      local.get 2
                      i32.const -8
                      i32.and
                      local.tee 2
                      call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std
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
                      i32.load offset=1050164
                      i32.ne
                      br_if 1 (;@8;)
                      i32.const 0
                      local.get 0
                      i32.store offset=1050156
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
                  br_if 4 (;@3;)
                  local.get 1
                  local.get 0
                  call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCsebHcaeoSrxy_3std
                  i32.const 0
                  i32.const 0
                  i32.load offset=1050188
                  i32.const -1
                  i32.add
                  local.tee 1
                  i32.store offset=1050188
                  local.get 1
                  br_if 6 (;@1;)
                  i32.const 0
                  i32.load offset=1049876
                  local.tee 0
                  br_if 2 (;@5;)
                  i32.const 4095
                  local.set 1
                  br 3 (;@4;)
                end
                i32.const 0
                local.get 1
                i32.store offset=1050168
                i32.const 0
                i32.const 0
                i32.load offset=1050160
                local.get 0
                i32.add
                local.tee 0
                i32.store offset=1050160
                local.get 1
                local.get 0
                i32.const 1
                i32.or
                i32.store offset=4
                block ;; label = @7
                  local.get 1
                  i32.const 0
                  i32.load offset=1050164
                  i32.ne
                  br_if 0 (;@7;)
                  i32.const 0
                  i32.const 0
                  i32.store offset=1050156
                  i32.const 0
                  i32.const 0
                  i32.store offset=1050164
                end
                local.get 0
                i32.const 0
                i32.load offset=1050180
                local.tee 2
                i32.le_u
                br_if 5 (;@1;)
                i32.const 0
                i32.load offset=1050168
                local.tee 0
                i32.eqz
                br_if 5 (;@1;)
                i32.const 0
                i32.load offset=1050160
                local.tee 4
                i32.const 41
                i32.lt_u
                br_if 4 (;@2;)
                i32.const 1049868
                local.set 1
                loop ;; label = @7
                  block ;; label = @8
                    local.get 1
                    i32.load
                    local.tee 3
                    local.get 0
                    i32.gt_u
                    br_if 0 (;@8;)
                    local.get 0
                    local.get 3
                    local.get 1
                    i32.load offset=4
                    i32.add
                    i32.lt_u
                    br_if 6 (;@2;)
                  end
                  local.get 1
                  i32.load offset=8
                  local.set 1
                  br 0 (;@7;)
                end
              end
              i32.const 0
              local.get 1
              i32.store offset=1050164
              i32.const 0
              i32.const 0
              i32.load offset=1050156
              local.get 0
              i32.add
              local.tee 0
              i32.store offset=1050156
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
            i32.const 0
            local.set 1
            loop ;; label = @5
              local.get 1
              i32.const 1
              i32.add
              local.set 1
              local.get 0
              i32.load offset=8
              local.tee 0
              br_if 0 (;@5;)
            end
            local.get 1
            i32.const 4095
            local.get 1
            i32.const 4095
            i32.gt_u
            select
            local.set 1
          end
          i32.const 0
          local.get 1
          i32.store offset=1050188
          return
        end
        block ;; label = @3
          block ;; label = @4
            i32.const 0
            i32.load offset=1050148
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
            i32.store offset=1050148
            local.get 0
            i32.const 248
            i32.and
            i32.const 1049884
            i32.add
            local.tee 0
            local.set 3
            br 1 (;@3;)
          end
          local.get 0
          i32.const 248
          i32.and
          local.tee 0
          i32.const 1049884
          i32.add
          local.set 3
          local.get 0
          i32.const 1049892
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
        block ;; label = @3
          i32.const 0
          i32.load offset=1049876
          local.tee 0
          br_if 0 (;@3;)
          i32.const 4095
          local.set 1
          br 1 (;@2;)
        end
        i32.const 0
        local.set 1
        loop ;; label = @3
          local.get 1
          i32.const 1
          i32.add
          local.set 1
          local.get 0
          i32.load offset=8
          local.tee 0
          br_if 0 (;@3;)
        end
        local.get 1
        i32.const 4095
        local.get 1
        i32.const 4095
        i32.gt_u
        select
        local.set 1
      end
      i32.const 0
      local.get 1
      i32.store offset=1050188
      local.get 4
      local.get 2
      i32.le_u
      br_if 0 (;@1;)
      i32.const 0
      i32.const -1
      i32.store offset=1050180
    end
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc (;29;) (type 7) (param i32 i32 i32 i32) (result i32)
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
                        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE8memalignCsebHcaeoSrxy_3std
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
                          i32.load offset=1050168
                          i32.eq
                          br_if 1 (;@10;)
                          block ;; label = @12
                            local.get 7
                            i32.const 0
                            i32.load offset=1050164
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
                            call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std
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
                              call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCsebHcaeoSrxy_3std
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
                          i32.load offset=1050156
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
                          i32.store offset=1050164
                          i32.const 0
                          local.get 6
                          i32.store offset=1050156
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
                        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCsebHcaeoSrxy_3std
                        br 6 (;@4;)
                      end
                      i32.const 0
                      i32.load offset=1050160
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
                    i32.const 1049380
                    i32.const 46
                    i32.const 1049428
                    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic
                    unreachable
                  end
                  i32.const 1049316
                  i32.const 46
                  i32.const 1049364
                  call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic
                  unreachable
                end
                i32.const 1049380
                i32.const 46
                i32.const 1049428
                call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic
                unreachable
              end
              i32.const 1049316
              i32.const 46
              i32.const 1049364
              call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic
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
            i32.store offset=1050160
            i32.const 0
            local.get 5
            i32.store offset=1050168
          end
          local.get 8
          i32.eqz
          br_if 0 (;@3;)
          local.get 0
          return
        end
        local.get 3
        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE6mallocCsebHcaeoSrxy_3std
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
      call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE4freeCsebHcaeoSrxy_3std
    end
    local.get 2
  )
  (func $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std (;30;) (type 0) (param i32 i32)
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
                i32.const 1049740
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
          i32.load offset=1050148
          i32.const -2
          local.get 1
          i32.const 3
          i32.shr_u
          i32.rotl
          i32.and
          i32.store offset=1050148
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
    i32.load offset=1050152
    i32.const -2
    local.get 0
    i32.load offset=28
    i32.rotl
    i32.and
    i32.store offset=1050152
  )
  (func $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE13dispose_chunkCsebHcaeoSrxy_3std (;31;) (type 0) (param i32 i32)
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
          i32.load offset=1050164
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
          i32.store offset=1050156
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
        call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std
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
              i32.load offset=1050168
              i32.eq
              br_if 2 (;@3;)
              local.get 2
              i32.const 0
              i32.load offset=1050164
              i32.eq
              br_if 3 (;@2;)
              local.get 2
              local.get 3
              i32.const -8
              i32.and
              local.tee 3
              call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE12unlink_chunkCsebHcaeoSrxy_3std
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
              i32.load offset=1050164
              i32.ne
              br_if 1 (;@4;)
              i32.const 0
              local.get 1
              i32.store offset=1050156
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
            call $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCsebHcaeoSrxy_3std
            return
          end
          block ;; label = @4
            block ;; label = @5
              i32.const 0
              i32.load offset=1050148
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
              i32.store offset=1050148
              local.get 1
              i32.const 248
              i32.and
              i32.const 1049884
              i32.add
              local.tee 1
              local.set 2
              br 1 (;@4;)
            end
            local.get 1
            i32.const 248
            i32.and
            local.tee 1
            i32.const 1049884
            i32.add
            local.set 2
            local.get 1
            i32.const 1049892
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
        i32.store offset=1050168
        i32.const 0
        i32.const 0
        i32.load offset=1050160
        local.get 1
        i32.add
        local.tee 1
        i32.store offset=1050160
        local.get 0
        local.get 1
        i32.const 1
        i32.or
        i32.store offset=4
        local.get 0
        i32.const 0
        i32.load offset=1050164
        i32.ne
        br_if 1 (;@1;)
        i32.const 0
        i32.const 0
        i32.store offset=1050156
        i32.const 0
        i32.const 0
        i32.store offset=1050164
        return
      end
      i32.const 0
      local.get 0
      i32.store offset=1050164
      i32.const 0
      i32.const 0
      i32.load offset=1050156
      local.get 1
      i32.add
      local.tee 1
      i32.store offset=1050156
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
  (func $_RNvCsfLfy6EI15iL_7___rustc17rust_begin_unwind (;32;) (type 12) (param i32)
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
    call $_RINvNtNtCsebHcaeoSrxy_3std3sys9backtrace26___rust_end_short_backtraceNCNvNtB6_9panicking13panic_handler0zEB6_
    unreachable
  )
  (func $_RNvCsfLfy6EI15iL_7___rustc26___rust_alloc_error_handler (;33;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call $_RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom
    unreachable
  )
  (func $_RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom (;34;) (type 0) (param i32 i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 2
    global.set $__stack_pointer
    local.get 2
    local.get 1
    i32.store offset=12
    local.get 2
    local.get 0
    i32.store offset=8
    local.get 2
    i32.const 8
    i32.add
    call $_RINvNtNtCsebHcaeoSrxy_3std3sys9backtrace26___rust_end_short_backtraceNCNvNtB6_5alloc8rust_oom0zEB6_
    unreachable
  )
  (func $_RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNtNtB7_3sys6SystemE18insert_large_chunkCsebHcaeoSrxy_3std (;35;) (type 0) (param i32 i32)
    (local i32 i32 i32 i32)
    i32.const 0
    local.set 2
    block ;; label = @1
      local.get 1
      i32.const 8
      i32.shr_u
      local.tee 3
      i32.eqz
      br_if 0 (;@1;)
      i32.const 31
      local.set 2
      local.get 1
      i32.const 16777216
      i32.ge_u
      br_if 0 (;@1;)
      local.get 1
      i32.const 38
      local.get 3
      i32.clz
      local.tee 2
      i32.sub
      i32.shr_u
      i32.const 1
      i32.and
      local.get 2
      i32.const 1
      i32.shl
      i32.or
      i32.const 62
      i32.xor
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
    i32.const 1049740
    i32.add
    local.set 3
    block ;; label = @1
      i32.const 0
      i32.load offset=1050152
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
      i32.load offset=1050152
      local.get 4
      i32.or
      i32.store offset=1050152
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
  (func $_RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase (;36;) (type 14) (param i32) (result i32)
    (local i32 i32)
    i32.const 0
    local.set 1
    i32.const 0
    i32.const 0
    i32.load offset=1049736
    local.tee 2
    i32.const 1
    i32.add
    i32.store offset=1049736
    block ;; label = @1
      local.get 2
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      i32.const 1
      local.set 1
      i32.const 0
      i32.load8_u offset=1049716
      br_if 0 (;@1;)
      i32.const 0
      local.get 0
      i32.store8 offset=1049716
      i32.const 0
      i32.const 0
      i32.load offset=1049712
      i32.const 1
      i32.add
      i32.store offset=1049712
      i32.const 2
      local.set 1
    end
    local.get 1
  )
  (func $_RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6string6StringNtB2_3Any7type_idCsebHcaeoSrxy_3std (;37;) (type 0) (param i32 i32)
    local.get 0
    i32.const 0
    i64.load offset=1049308 align=4
    i64.store offset=8 align=4
    local.get 0
    i32.const 0
    i64.load offset=1049300 align=4
    i64.store align=4
  )
  (func $_RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoSrxy_3std (;38;) (type 0) (param i32 i32)
    local.get 0
    i32.const 0
    i64.load offset=1049292 align=4
    i64.store offset=8 align=4
    local.get 0
    i32.const 0
    i64.load offset=1049284 align=4
    i64.store align=4
  )
  (func $_RNvXs0_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_19FormatStringPayloadNtNtCsgXGp5Oqx2Ny_4core3fmt7Display3fmt (;39;) (type 2) (param i32 i32) (result i32)
    block ;; label = @1
      local.get 0
      i32.load
      i32.const -2147483648
      i32.eq
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      i32.load offset=4
      local.get 0
      i32.load offset=8
      call $_RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter9write_str
      return
    end
    local.get 1
    i32.load
    local.get 1
    i32.load offset=4
    local.get 0
    i32.load offset=12
    i32.load
    local.tee 0
    i32.load
    local.get 0
    i32.load offset=4
    call $_RNvNtCsgXGp5Oqx2Ny_4core3fmt5write
  )
  (func $_RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload3get (;40;) (type 0) (param i32 i32)
    local.get 0
    i32.const 1049444
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
  )
  (func $_RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload6as_str (;41;) (type 0) (param i32 i32)
    local.get 0
    local.get 1
    i64.load align=4
    i64.store
  )
  (func $_RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload8take_box (;42;) (type 0) (param i32 i32)
    (local i32 i32)
    local.get 1
    i32.load offset=4
    local.set 2
    local.get 1
    i32.load
    local.set 3
    call $_RNvCsfLfy6EI15iL_7___rustc35___rust_no_alloc_shim_is_unstable_v2
    block ;; label = @1
      i32.const 8
      i32.const 4
      call $_RNvCsfLfy6EI15iL_7___rustc12___rust_alloc
      local.tee 1
      br_if 0 (;@1;)
      i32.const 4
      i32.const 8
      call $_RNvNtCs5cOc02OMXlo_5alloc5alloc18handle_alloc_error
      unreachable
    end
    local.get 1
    local.get 2
    i32.store offset=4
    local.get 1
    local.get 3
    i32.store
    local.get 0
    i32.const 1049444
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
  )
  (func $_RNvXs2_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5_16StaticStrPayloadNtNtCsgXGp5Oqx2Ny_4core3fmt7Display3fmt (;43;) (type 2) (param i32 i32) (result i32)
    local.get 1
    local.get 0
    i32.load
    local.get 0
    i32.load offset=4
    call $_RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter9write_str
  )
  (func $_RNvXsZ_NtCs5cOc02OMXlo_5alloc6stringNtB5_6StringNtNtCsgXGp5Oqx2Ny_4core3fmt5Write10write_char (;44;) (type 2) (param i32 i32) (result i32)
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
      call $_RINvNvMs2_NtCs5cOc02OMXlo_5alloc7raw_vecINtB8_11RawVecInnerpE7reserve21do_reserve_and_handleNtNtBa_5alloc6GlobalECsebHcaeoSrxy_3std
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
  (func $_RNvXsZ_NtCs5cOc02OMXlo_5alloc6stringNtB5_6StringNtNtCsgXGp5Oqx2Ny_4core3fmt5Write9write_str (;45;) (type 1) (param i32 i32 i32) (result i32)
    (local i32)
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 2
          local.get 0
          i32.load
          local.get 0
          i32.load offset=8
          local.tee 3
          i32.sub
          i32.le_u
          br_if 0 (;@3;)
          local.get 0
          local.get 3
          local.get 2
          i32.const 1
          i32.const 1
          call $_RINvNvMs2_NtCs5cOc02OMXlo_5alloc7raw_vecINtB8_11RawVecInnerpE7reserve21do_reserve_and_handleNtNtBa_5alloc6GlobalECsebHcaeoSrxy_3std
          local.get 0
          i32.load offset=8
          local.set 3
          br 1 (;@2;)
        end
        local.get 2
        i32.eqz
        br_if 1 (;@1;)
      end
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
  (func $_RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_19FormatStringPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload3get (;46;) (type 0) (param i32 i32)
    (local i32 i32 i64)
    global.get $__stack_pointer
    i32.const 32
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
      i32.const 0
      i32.store offset=28
      local.get 2
      i64.const 4294967296
      i64.store offset=20 align=4
      local.get 2
      i32.const 20
      i32.add
      i32.const 1049204
      local.get 3
      i32.load
      local.tee 3
      i32.load
      local.get 3
      i32.load offset=4
      call $_RNvNtCsgXGp5Oqx2Ny_4core3fmt5write
      drop
      local.get 2
      local.get 2
      i32.load offset=28
      local.tee 3
      i32.store offset=16
      local.get 2
      local.get 2
      i64.load offset=20 align=4
      local.tee 4
      i64.store offset=8
      local.get 1
      local.get 3
      i32.store offset=8
      local.get 1
      local.get 4
      i64.store align=4
    end
    local.get 0
    i32.const 1049460
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
    local.get 2
    i32.const 32
    i32.add
    global.set $__stack_pointer
  )
  (func $_RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_19FormatStringPayloadNtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload8take_box (;47;) (type 0) (param i32 i32)
    (local i32 i32 i64)
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
      i32.const 0
      i32.store offset=44
      local.get 2
      i64.const 4294967296
      i64.store offset=36 align=4
      local.get 2
      i32.const 36
      i32.add
      i32.const 1049204
      local.get 3
      i32.load
      local.tee 3
      i32.load
      local.get 3
      i32.load offset=4
      call $_RNvNtCsgXGp5Oqx2Ny_4core3fmt5write
      drop
      local.get 2
      local.get 2
      i32.load offset=44
      local.tee 3
      i32.store offset=32
      local.get 2
      local.get 2
      i64.load offset=36 align=4
      local.tee 4
      i64.store offset=24
      local.get 1
      local.get 3
      i32.store offset=8
      local.get 1
      local.get 4
      i64.store align=4
    end
    local.get 1
    i32.load offset=8
    local.set 3
    local.get 1
    i32.const 0
    i32.store offset=8
    local.get 1
    i64.load align=4
    local.set 4
    local.get 1
    i64.const 4294967296
    i64.store align=4
    local.get 2
    local.get 3
    i32.store offset=16
    local.get 2
    local.get 4
    i64.store offset=8
    call $_RNvCsfLfy6EI15iL_7___rustc35___rust_no_alloc_shim_is_unstable_v2
    block ;; label = @1
      i32.const 12
      i32.const 4
      call $_RNvCsfLfy6EI15iL_7___rustc12___rust_alloc
      local.tee 1
      br_if 0 (;@1;)
      i32.const 4
      i32.const 12
      call $_RNvNtCs5cOc02OMXlo_5alloc5alloc18handle_alloc_error
      unreachable
    end
    local.get 1
    local.get 2
    i32.load offset=16
    i32.store offset=8
    local.get 1
    local.get 2
    i64.load offset=8
    i64.store align=4
    local.get 0
    i32.const 1049460
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
    local.get 2
    i32.const 48
    i32.add
    global.set $__stack_pointer
  )
  (func $_RNvYINtNvNtCsebHcaeoSrxy_3std9panicking11begin_panic7PayloadReENtNtCsgXGp5Oqx2Ny_4core5panic12PanicPayload6as_strB9_ (;48;) (type 0) (param i32 i32)
    local.get 0
    i32.const 0
    i32.store
  )
  (func $_RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2Ny_4core3fmt5Write9write_fmtCsebHcaeoSrxy_3std (;49;) (type 1) (param i32 i32 i32) (result i32)
    local.get 0
    i32.const 1049204
    local.get 1
    local.get 2
    call $_RNvNtCsgXGp5Oqx2Ny_4core3fmt5write
  )
  (func $_RNvXs_NtCsjqx8TIyZbP9_8dlmalloc3sysNtB4_6SystemNtB6_9Allocator5alloc (;50;) (type 6) (param i32 i32 i32)
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
  (func $_RINvNtCsgXGp5Oqx2Ny_4core5slice20copy_from_slice_implhECs4wvrbUR2I4G_11miniz_oxide (;51;) (type 11) (param i32 i32 i32 i32 i32)
    block ;; label = @1
      local.get 1
      local.get 3
      i32.ne
      br_if 0 (;@1;)
      block ;; label = @2
        local.get 1
        i32.eqz
        br_if 0 (;@2;)
        local.get 0
        local.get 2
        local.get 1
        memory.copy
      end
      return
    end
    local.get 1
    local.get 3
    local.get 4
    call $_RNvNvNtCsgXGp5Oqx2Ny_4core5slice20copy_from_slice_impl17len_mismatch_fail
    unreachable
  )
  (func $_RNvNtCs5cOc02OMXlo_5alloc7raw_vec12handle_error (;52;) (type 0) (param i32 i32)
    block ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      local.get 1
      call $_RNvNtCs5cOc02OMXlo_5alloc5alloc18handle_alloc_error
      unreachable
    end
    call $_RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow
    unreachable
  )
  (func $_RNvNtCs5cOc02OMXlo_5alloc5alloc18handle_alloc_error (;53;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call $_RNvCsfLfy6EI15iL_7___rustc26___rust_alloc_error_handler
    unreachable
  )
  (func $_RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow (;54;) (type 8)
    i32.const 1049476
    i32.const 35
    i32.const 1049496
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking9panic_fmt
    unreachable
  )
  (func $_RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic (;55;) (type 6) (param i32 i32 i32)
    local.get 0
    local.get 1
    i32.const 1
    i32.shl
    i32.const 1
    i32.or
    local.get 2
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking9panic_fmt
    unreachable
  )
  (func $_RNvNtCsgXGp5Oqx2Ny_4core9panicking9panic_fmt (;56;) (type 6) (param i32 i32 i32)
    (local i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 1
    i32.store offset=16
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    i32.const 1
    i32.store16 offset=28
    local.get 3
    local.get 2
    i32.store offset=24
    local.get 3
    local.get 3
    i32.const 12
    i32.add
    i32.store offset=20
    local.get 3
    i32.const 20
    i32.add
    call $_RNvCsfLfy6EI15iL_7___rustc17rust_begin_unwind
    unreachable
  )
  (func $_RNvNtCsgXGp5Oqx2Ny_4core3fmt5write (;57;) (type 7) (param i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 4
    global.set $__stack_pointer
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 3
          i32.const 1
          i32.and
          br_if 0 (;@3;)
          local.get 2
          i32.load8_u
          local.tee 5
          br_if 1 (;@2;)
          i32.const 0
          local.set 5
          br 2 (;@1;)
        end
        local.get 0
        local.get 2
        local.get 3
        i32.const 1
        i32.shr_u
        local.get 1
        i32.load offset=12
        call_indirect (type 1)
        local.set 5
        br 1 (;@1;)
      end
      local.get 1
      i32.load offset=12
      local.set 6
      i32.const 0
      local.set 7
      loop ;; label = @2
        local.get 2
        i32.const 1
        i32.add
        local.set 8
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  local.get 5
                  i32.extend8_s
                  i32.const -1
                  i32.gt_s
                  br_if 0 (;@7;)
                  local.get 5
                  i32.const 255
                  i32.and
                  local.tee 9
                  i32.const 128
                  i32.eq
                  br_if 1 (;@6;)
                  local.get 9
                  i32.const 192
                  i32.ne
                  br_if 3 (;@4;)
                  local.get 4
                  local.get 1
                  i32.store offset=4
                  local.get 4
                  local.get 0
                  i32.store
                  local.get 4
                  i64.const 1610612768
                  i64.store offset=8 align=4
                  local.get 3
                  local.get 7
                  i32.const 3
                  i32.shl
                  i32.add
                  local.tee 5
                  i32.load
                  local.get 4
                  local.get 5
                  i32.load offset=4
                  call_indirect (type 2)
                  i32.eqz
                  br_if 2 (;@5;)
                  i32.const 1
                  local.set 5
                  br 6 (;@1;)
                end
                block ;; label = @7
                  local.get 0
                  local.get 8
                  local.get 5
                  i32.const 255
                  i32.and
                  local.tee 5
                  local.get 6
                  call_indirect (type 1)
                  br_if 0 (;@7;)
                  local.get 8
                  local.get 5
                  i32.add
                  local.set 2
                  br 4 (;@3;)
                end
                i32.const 1
                local.set 5
                br 5 (;@1;)
              end
              block ;; label = @6
                local.get 0
                local.get 2
                i32.const 3
                i32.add
                local.tee 5
                local.get 2
                i32.load16_u offset=1 align=1
                local.tee 2
                local.get 6
                call_indirect (type 1)
                br_if 0 (;@6;)
                local.get 5
                local.get 2
                i32.add
                local.set 2
                br 3 (;@3;)
              end
              i32.const 1
              local.set 5
              br 4 (;@1;)
            end
            local.get 7
            i32.const 1
            i32.add
            local.set 7
            local.get 8
            local.set 2
            br 1 (;@3;)
          end
          i32.const 1610612768
          local.set 10
          block ;; label = @4
            local.get 5
            i32.const 1
            i32.and
            i32.eqz
            br_if 0 (;@4;)
            local.get 2
            i32.const 5
            i32.add
            local.set 8
            local.get 2
            i32.load offset=1 align=1
            local.set 10
          end
          i32.const 0
          local.set 9
          block ;; label = @4
            block ;; label = @5
              local.get 5
              i32.const 2
              i32.and
              br_if 0 (;@5;)
              i32.const 0
              local.set 11
              local.get 8
              local.set 2
              br 1 (;@4;)
            end
            local.get 8
            i32.const 2
            i32.add
            local.set 2
            local.get 8
            i32.load16_u align=1
            local.set 11
          end
          block ;; label = @4
            block ;; label = @5
              local.get 5
              i32.const 4
              i32.and
              br_if 0 (;@5;)
              local.get 2
              local.set 8
              br 1 (;@4;)
            end
            local.get 2
            i32.const 2
            i32.add
            local.set 8
            local.get 2
            i32.load16_u align=1
            local.set 9
          end
          block ;; label = @4
            block ;; label = @5
              local.get 5
              i32.const 8
              i32.and
              br_if 0 (;@5;)
              local.get 8
              local.set 2
              br 1 (;@4;)
            end
            local.get 8
            i32.const 2
            i32.add
            local.set 2
            local.get 8
            i32.load16_u align=1
            local.set 7
          end
          block ;; label = @4
            local.get 5
            i32.const 16
            i32.and
            i32.eqz
            br_if 0 (;@4;)
            local.get 3
            local.get 11
            i32.const 65535
            i32.and
            i32.const 3
            i32.shl
            i32.add
            i32.load16_u offset=4
            local.set 11
          end
          block ;; label = @4
            local.get 5
            i32.const 32
            i32.and
            i32.eqz
            br_if 0 (;@4;)
            local.get 3
            local.get 9
            i32.const 65535
            i32.and
            i32.const 3
            i32.shl
            i32.add
            i32.load16_u offset=4
            local.set 9
          end
          local.get 4
          local.get 9
          i32.store16 offset=14
          local.get 4
          local.get 11
          i32.store16 offset=12
          local.get 4
          local.get 10
          i32.store offset=8
          local.get 4
          local.get 1
          i32.store offset=4
          local.get 4
          local.get 0
          i32.store
          block ;; label = @4
            local.get 3
            local.get 7
            i32.const 3
            i32.shl
            i32.add
            local.tee 5
            i32.load
            local.get 4
            local.get 5
            i32.load offset=4
            call_indirect (type 2)
            i32.eqz
            br_if 0 (;@4;)
            i32.const 1
            local.set 5
            br 3 (;@1;)
          end
          local.get 7
          i32.const 1
          i32.add
          local.set 7
        end
        local.get 2
        i32.load8_u
        local.tee 5
        br_if 0 (;@2;)
      end
      i32.const 0
      local.set 5
    end
    local.get 4
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get 5
  )
  (func $_RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check (;58;) (type 6) (param i32 i32 i32)
    (local i32 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 1
    i32.store offset=12
    local.get 3
    local.get 0
    i32.store offset=8
    local.get 3
    i32.const 17
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.tee 4
    local.get 3
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=24
    local.get 3
    local.get 4
    local.get 3
    i32.const 12
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=16
    i32.const 1048576
    local.get 3
    i32.const 16
    i32.add
    local.get 2
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking9panic_fmt
    unreachable
  )
  (func $_RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter12pad_integral (;59;) (type 15) (param i32 i32 i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i64)
    i32.const 43
    i32.const 1114112
    local.get 0
    i32.load offset=8
    local.tee 6
    i32.const 2097152
    i32.and
    local.tee 7
    select
    local.set 8
    local.get 7
    i32.const 21
    i32.shr_u
    i32.const 1
    local.get 1
    select
    local.get 5
    i32.add
    local.set 9
    block ;; label = @1
      block ;; label = @2
        local.get 6
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
          call $_RNvNtNtCsgXGp5Oqx2Ny_4core3str5count14do_count_chars
          local.set 7
          br 1 (;@2;)
        end
        block ;; label = @3
          local.get 3
          br_if 0 (;@3;)
          i32.const 0
          local.set 7
          br 1 (;@2;)
        end
        local.get 3
        i32.const 3
        i32.and
        local.set 10
        i32.const 0
        local.set 11
        i32.const 0
        local.set 7
        block ;; label = @3
          local.get 3
          i32.const 4
          i32.lt_u
          br_if 0 (;@3;)
          local.get 3
          i32.const 12
          i32.and
          local.set 12
          i32.const 0
          local.set 11
          i32.const 0
          local.set 7
          loop ;; label = @4
            local.get 7
            local.get 2
            local.get 11
            i32.add
            local.tee 13
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get 13
            i32.const 1
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get 13
            i32.const 2
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get 13
            i32.const 3
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set 7
            local.get 12
            local.get 11
            i32.const 4
            i32.add
            local.tee 11
            i32.ne
            br_if 0 (;@4;)
          end
          local.get 10
          i32.eqz
          br_if 1 (;@2;)
        end
        local.get 2
        local.get 11
        i32.add
        local.set 13
        loop ;; label = @3
          local.get 7
          local.get 13
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set 7
          local.get 13
          i32.const 1
          i32.add
          local.set 13
          local.get 10
          i32.const -1
          i32.add
          local.tee 10
          br_if 0 (;@3;)
        end
      end
      local.get 7
      local.get 9
      i32.add
      local.set 9
    end
    local.get 8
    i32.const 45
    local.get 1
    select
    local.set 12
    block ;; label = @1
      block ;; label = @2
        local.get 9
        local.get 0
        i32.load16_u offset=12
        local.tee 1
        i32.ge_u
        br_if 0 (;@2;)
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 6
              i32.const 16777216
              i32.and
              br_if 0 (;@5;)
              local.get 1
              local.get 9
              i32.sub
              local.set 8
              i32.const 0
              local.set 7
              i32.const 0
              local.set 1
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    local.get 6
                    i32.const 29
                    i32.shr_u
                    i32.const 3
                    i32.and
                    br_table 2 (;@6;) 0 (;@8;) 1 (;@7;) 0 (;@8;) 2 (;@6;)
                  end
                  local.get 8
                  local.set 1
                  br 1 (;@6;)
                end
                local.get 8
                i32.const 65534
                i32.and
                i32.const 1
                i32.shr_u
                local.set 1
              end
              local.get 6
              i32.const 2097151
              i32.and
              local.set 9
              local.get 0
              i32.load offset=4
              local.set 11
              local.get 0
              i32.load
              local.set 10
              loop ;; label = @6
                local.get 7
                i32.const 65535
                i32.and
                local.get 1
                i32.const 65535
                i32.and
                i32.ge_u
                br_if 2 (;@4;)
                i32.const 1
                local.set 13
                local.get 7
                i32.const 1
                i32.add
                local.set 7
                local.get 10
                local.get 9
                local.get 11
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
            local.set 13
            local.get 0
            i32.load
            local.tee 10
            local.get 0
            i32.load offset=4
            local.tee 11
            local.get 12
            local.get 2
            local.get 3
            call $_RNvNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB7_9Formatter12pad_integral12write_prefix
            br_if 3 (;@1;)
            i32.const 0
            local.set 7
            local.get 1
            local.get 9
            i32.sub
            i32.const 65535
            i32.and
            local.set 2
            loop ;; label = @5
              local.get 7
              i32.const 65535
              i32.and
              local.get 2
              i32.ge_u
              br_if 2 (;@3;)
              i32.const 1
              local.set 13
              local.get 7
              i32.const 1
              i32.add
              local.set 7
              local.get 10
              i32.const 48
              local.get 11
              i32.load offset=16
              call_indirect (type 2)
              i32.eqz
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
          end
          i32.const 1
          local.set 13
          local.get 10
          local.get 11
          local.get 12
          local.get 2
          local.get 3
          call $_RNvNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB7_9Formatter12pad_integral12write_prefix
          br_if 2 (;@1;)
          local.get 10
          local.get 4
          local.get 5
          local.get 11
          i32.load offset=12
          call_indirect (type 1)
          br_if 2 (;@1;)
          i32.const 0
          local.set 7
          local.get 8
          local.get 1
          i32.sub
          i32.const 65535
          i32.and
          local.set 0
          loop ;; label = @4
            local.get 7
            i32.const 65535
            i32.and
            local.tee 2
            local.get 0
            i32.lt_u
            local.set 13
            local.get 2
            local.get 0
            i32.ge_u
            br_if 3 (;@1;)
            local.get 7
            i32.const 1
            i32.add
            local.set 7
            local.get 10
            local.get 9
            local.get 11
            i32.load offset=16
            call_indirect (type 2)
            i32.eqz
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        i32.const 1
        local.set 13
        local.get 10
        local.get 4
        local.get 5
        local.get 11
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
      local.set 13
      local.get 0
      i32.load
      local.tee 7
      local.get 0
      i32.load offset=4
      local.tee 10
      local.get 12
      local.get 2
      local.get 3
      call $_RNvNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB7_9Formatter12pad_integral12write_prefix
      br_if 0 (;@1;)
      local.get 7
      local.get 4
      local.get 5
      local.get 10
      i32.load offset=12
      call_indirect (type 1)
      local.set 13
    end
    local.get 13
  )
  (func $_RNvNtNtCsgXGp5Oqx2Ny_4core3str5count14do_count_chars (;60;) (type 2) (param i32 i32) (result i32)
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
        i32.const 2
        i32.shr_u
        local.tee 5
        i32.eqz
        br_if 0 (;@2;)
        local.get 4
        i32.const 3
        i32.and
        local.set 6
        i32.const 0
        local.set 7
        i32.const 0
        local.set 1
        block ;; label = @3
          local.get 2
          local.get 0
          i32.eq
          br_if 0 (;@3;)
          i32.const 0
          local.set 8
          i32.const 0
          local.set 1
          block ;; label = @4
            local.get 0
            local.get 2
            i32.sub
            local.tee 9
            i32.const -4
            i32.gt_u
            br_if 0 (;@4;)
            i32.const 0
            local.set 8
            i32.const 0
            local.set 1
            loop ;; label = @5
              local.get 1
              local.get 0
              local.get 8
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
              local.get 8
              i32.const 4
              i32.add
              local.tee 8
              br_if 0 (;@5;)
            end
          end
          local.get 0
          local.get 8
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
            local.get 9
            i32.const 1
            i32.add
            local.tee 9
            br_if 0 (;@4;)
          end
        end
        local.get 0
        local.get 3
        i32.add
        local.set 9
        block ;; label = @3
          local.get 6
          i32.eqz
          br_if 0 (;@3;)
          local.get 9
          local.get 4
          i32.const 2147483644
          i32.and
          i32.add
          local.tee 2
          i32.load8_s
          i32.const -65
          i32.gt_s
          local.set 7
          local.get 6
          i32.const 1
          i32.eq
          br_if 0 (;@3;)
          local.get 7
          local.get 2
          i32.load8_s offset=1
          i32.const -65
          i32.gt_s
          i32.add
          local.set 7
          local.get 6
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get 7
          local.get 2
          i32.load8_s offset=2
          i32.const -65
          i32.gt_s
          i32.add
          local.set 7
        end
        local.get 7
        local.get 1
        i32.add
        local.set 8
        loop ;; label = @3
          local.get 9
          local.set 3
          local.get 5
          i32.eqz
          br_if 2 (;@1;)
          local.get 5
          i32.const 192
          local.get 5
          i32.const 192
          i32.lt_u
          select
          local.tee 7
          i32.const 3
          i32.and
          local.set 6
          block ;; label = @4
            block ;; label = @5
              local.get 7
              i32.const 2
              i32.shl
              local.tee 4
              i32.const 1008
              i32.and
              local.tee 1
              br_if 0 (;@5;)
              i32.const 0
              local.set 2
              br 1 (;@4;)
            end
            local.get 3
            local.get 1
            i32.add
            local.set 0
            i32.const 0
            local.set 2
            local.get 3
            local.set 1
            loop ;; label = @5
              local.get 1
              i32.const 12
              i32.add
              i32.load
              local.tee 9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 1
              i32.const 8
              i32.add
              i32.load
              local.tee 9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 1
              i32.const 4
              i32.add
              i32.load
              local.tee 9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get 1
              i32.load
              local.tee 9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get 9
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
              local.tee 1
              local.get 0
              i32.ne
              br_if 0 (;@5;)
            end
          end
          local.get 5
          local.get 7
          i32.sub
          local.set 5
          local.get 3
          local.get 4
          i32.add
          local.set 9
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
          local.get 8
          i32.add
          local.set 8
          local.get 6
          i32.eqz
          br_if 0 (;@3;)
        end
        local.get 3
        local.get 7
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
          local.get 6
          i32.const 1
          i32.eq
          br_if 0 (;@3;)
          local.get 2
          i32.load offset=4
          local.tee 9
          i32.const -1
          i32.xor
          i32.const 7
          i32.shr_u
          local.get 9
          i32.const 6
          i32.shr_u
          i32.or
          i32.const 16843009
          i32.and
          local.get 1
          i32.add
          local.set 1
          local.get 6
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
        local.get 8
        i32.add
        local.set 8
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
      local.set 2
      i32.const 0
      local.set 9
      i32.const 0
      local.set 8
      block ;; label = @2
        local.get 1
        i32.const 4
        i32.lt_u
        br_if 0 (;@2;)
        local.get 1
        i32.const -4
        i32.and
        local.set 5
        i32.const 0
        local.set 8
        i32.const 0
        local.set 9
        loop ;; label = @3
          local.get 8
          local.get 0
          local.get 9
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
          local.set 8
          local.get 5
          local.get 9
          i32.const 4
          i32.add
          local.tee 9
          i32.ne
          br_if 0 (;@3;)
        end
        local.get 2
        i32.eqz
        br_if 1 (;@1;)
      end
      local.get 0
      local.get 9
      i32.add
      local.set 1
      loop ;; label = @2
        local.get 8
        local.get 1
        i32.load8_s
        i32.const -65
        i32.gt_s
        i32.add
        local.set 8
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        local.get 2
        i32.const -1
        i32.add
        local.tee 2
        br_if 0 (;@2;)
      end
    end
    local.get 8
  )
  (func $_RNvNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB7_9Formatter12pad_integral12write_prefix (;61;) (type 16) (param i32 i32 i32 i32 i32) (result i32)
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
  (func $_RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter9write_str (;62;) (type 1) (param i32 i32 i32) (result i32)
    local.get 0
    i32.load
    local.get 1
    local.get 2
    local.get 0
    i32.load offset=4
    i32.load offset=12
    call_indirect (type 1)
  )
  (func $_RNvXs8_NtNtNtCsgXGp5Oqx2Ny_4core3fmt3num3impmNtB9_7Display3fmt (;63;) (type 2) (param i32 i32) (result i32)
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
      local.set 5
      loop ;; label = @2
        local.get 2
        i32.const 6
        i32.add
        local.get 3
        i32.add
        local.tee 6
        i32.const -4
        i32.add
        local.get 5
        local.tee 0
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
        i32.load16_u offset=1049512 align=1
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
        i32.load16_u offset=1049512 align=1
        i32.store16 align=1
        local.get 3
        i32.const -4
        i32.add
        local.set 3
        local.get 0
        i32.const 9999999
        i32.gt_u
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
      i32.load16_u offset=1049512 align=1
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
      i32.load8_u offset=1049513
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
    call $_RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter12pad_integral
    local.set 3
    local.get 2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get 3
  )
  (func $_RNvNvNtCsgXGp5Oqx2Ny_4core5slice20copy_from_slice_impl17len_mismatch_fail (;64;) (type 6) (param i32 i32 i32)
    (local i32 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee 3
    global.set $__stack_pointer
    local.get 3
    local.get 1
    i32.store offset=8
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    i32.const 17
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.tee 4
    local.get 3
    i32.const 12
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=24
    local.get 3
    local.get 4
    local.get 3
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=16
    i32.const 1048852
    local.get 3
    i32.const 16
    i32.add
    local.get 2
    call $_RNvNtCsgXGp5Oqx2Ny_4core9panicking9panic_fmt
    unreachable
  )
  (data $.rodata (;0;) (i32.const 1048576) " index out of bounds: the len is \c0\12 but the index is \c0\00/rustc/59807616e1fa2540724bfbac14d7976d7e4a3860/library/alloc/src/raw_vec/mod.rs\00/rust/deps/dlmalloc-0.2.11/src/dlmalloc.rs\00itoa/src/lib.rs\00/cargo-home/registry/src/index.crates.io-1949cf8c6b5b557f/itoa-1.0.18/src/lib.rs\00&copy_from_slice: source slice length (\c0+) does not match destination slice length (\c0\01)\00\c3\00\10\00P\00\00\00\bc\00\00\00\01\00\00\00\b3\00\10\00\0f\00\00\00\11\00\00\001\00\00\00\b3\00\10\00\0f\00\00\00\1e\00\00\001\00\00\00\c3\00\10\00P\00\00\00L\01\00\00\01\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899\02\00\00\00\0c\00\00\00\04\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\00\00\00\00\08\00\00\00\04\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00\09\00\00\00\0a\00\00\00\10\00\00\00\04\00\00\00\0b\00\00\00\0c\00\00\00\0d\00\00\00\0e\00\00\00m]\cb\d6,P\ebcxA\a6Wq\1b\8b\b9\15\a2\5cU4U\07\d4Sx\ad\81Q\f0\a3\f7assertion failed: psize >= size + min_overhead\00\00\88\00\10\00*\00\00\00\b1\04\00\00\09\00\00\00assertion failed: psize <= size + max_overhead\00\00\88\00\10\00*\00\00\00\b7\04\00\00\0d\00\00\00\00\00\00\00\08\00\00\00\04\00\00\00\0f\00\00\00\02\00\00\00\0c\00\00\00\04\00\00\00\10\00\00\00capacity overflow\00\00\007\00\10\00P\00\00\00\1c\00\00\00\05\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899")
)
