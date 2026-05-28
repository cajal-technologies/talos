(module
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
  (global (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1050136)
  (global (;2;) i32 i32.const 1050144)
  (export "memory" (memory 0))
  (export "itoa_i64" (func 1))
  (export "itoa_i64_len" (func 2))
  (export "itoa_u64" (func 3))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (elem (;0;) (i32.const 1) func 25 53 35 39 38 34 40 45 43 44 36 41 47 46 37 27 26)
  (func (;0;) (type 3) (param i32 i32 i64)
    (local i32 i64 i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 3
    global.set 0
    local.get 2
    local.get 2
    i64.const 63
    i64.shr_s
    local.tee 4
    i64.xor
    local.get 4
    i64.sub
    local.get 1
    call 9
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
      call 10
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
      global.set 0
      return
    end
    local.get 5
    i32.const 20
    i32.const 1048772
    call 56
    unreachable
  )
  (func (;1;) (type 4) (param i64 i32 i32) (result i32)
    (local i32 i32 i32)
    global.get 0
    i32.const 48
    i32.sub
    local.tee 3
    global.set 0
    local.get 3
    local.get 3
    i32.const 8
    i32.add
    local.get 0
    call 0
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
    global.set 0
    local.get 4
  )
  (func (;2;) (type 5) (param i64) (result i32)
    (local i32 i32)
    global.get 0
    i32.const 48
    i32.sub
    local.tee 1
    global.set 0
    local.get 1
    local.get 1
    i32.const 8
    i32.add
    local.get 0
    call 0
    local.get 1
    i32.load offset=4
    local.set 2
    local.get 1
    i32.const 48
    i32.add
    global.set 0
    local.get 2
  )
  (func (;3;) (type 4) (param i64 i32 i32) (result i32)
    (local i32 i32 i32)
    global.get 0
    i32.const 48
    i32.sub
    local.tee 3
    global.set 0
    local.get 3
    local.get 3
    i32.const 8
    i32.add
    i32.const 20
    local.get 0
    local.get 3
    i32.const 8
    i32.add
    call 9
    call 10
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
    global.set 0
    local.get 4
  )
  (func (;4;) (type 2) (param i32 i32) (result i32)
    local.get 0
    local.get 1
    call 13
    return
  )
  (func (;5;) (type 6) (param i32 i32 i32)
    local.get 0
    local.get 1
    local.get 2
    call 17
    return
  )
  (func (;6;) (type 7) (param i32 i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    call 19
    return
  )
  (func (;7;) (type 8) (result i32)
    i32.const 0
    return
  )
  (func (;8;) (type 9)
    return
  )
  (func (;9;) (type 10) (param i64 i32) (result i32)
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
        call 56
        unreachable
      end
      i32.const -4
      i32.const 20
      i32.const 1048788
      call 56
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
    call 56
    unreachable
  )
  (func (;10;) (type 11) (param i32 i32 i32 i32)
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
  (func (;11;) (type 2) (param i32 i32) (result i32)
    call 16
    unreachable
  )
  (func (;12;) (type 0) (param i32 i32)
    local.get 0
    local.get 1
    call 11
    drop
    unreachable
  )
  (func (;13;) (type 2) (param i32 i32) (result i32)
    block ;; label = @1
      local.get 1
      i32.const 9
      i32.lt_u
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      call 14
      return
    end
    local.get 0
    call 15
  )
  (func (;14;) (type 2) (param i32 i32) (result i32)
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
      call 15
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
          call 21
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
        call 21
      end
      local.get 0
      i32.const 8
      i32.add
      local.set 2
    end
    local.get 2
  )
  (func (;15;) (type 12) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i64)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 1
    global.set 0
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
              call 42
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
                    call 48
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
                        call 42
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
                      call 20
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
                      call 42
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
    global.set 0
    local.get 0
  )
  (func (;16;) (type 9)
    unreachable
  )
  (func (;17;) (type 6) (param i32 i32 i32)
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
        call 18
        return
      end
      i32.const 1049200
      i32.const 46
      i32.const 1049248
      call 57
      unreachable
    end
    i32.const 1049264
    i32.const 46
    i32.const 1049312
    call 57
    unreachable
  )
  (func (;18;) (type 13) (param i32)
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
        call 20
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
                  call 20
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
              call 42
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
  (func (;19;) (type 7) (param i32 i32 i32 i32) (result i32)
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
                        call 14
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
                            call 20
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
                              call 21
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
                        call 21
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
                    call 57
                    unreachable
                  end
                  i32.const 1049200
                  i32.const 46
                  i32.const 1049248
                  call 57
                  unreachable
                end
                i32.const 1049264
                i32.const 46
                i32.const 1049312
                call 57
                unreachable
              end
              i32.const 1049200
              i32.const 46
              i32.const 1049248
              call 57
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
        call 15
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
      call 18
    end
    local.get 2
  )
  (func (;20;) (type 0) (param i32 i32)
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
  (func (;21;) (type 0) (param i32 i32)
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
        call 20
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
              call 20
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
            call 42
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
  (func (;22;) (type 13) (param i32)
    (local i32 i64)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 1
    global.set 0
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
    call 23
    unreachable
  )
  (func (;23;) (type 13) (param i32)
    local.get 0
    call 29
    unreachable
  )
  (func (;24;) (type 0) (param i32 i32)
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
  (func (;25;) (type 0) (param i32 i32)
    (local i32)
    global.get 0
    i32.const 48
    i32.sub
    local.tee 2
    global.set 0
    block ;; label = @1
      call 7
      i32.const 255
      i32.and
      br_if 0 (;@1;)
      local.get 2
      i32.const 48
      i32.add
      global.set 0
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
    call 55
    unreachable
  )
  (func (;26;) (type 0) (param i32 i32)
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
  (func (;27;) (type 0) (param i32 i32)
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
  (func (;28;) (type 14) (param i32 i32 i32 i32 i32)
    (local i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 5
    global.set 0
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
      call 49
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
    call 30
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
      call 49
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
    global.set 0
  )
  (func (;29;) (type 13) (param i32)
    (local i32 i32 i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 1
    global.set 0
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
      call 31
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
    call 31
    unreachable
  )
  (func (;30;) (type 15) (param i32 i32 i32 i32 i32 i32)
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
              call 6
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
            call 8
            local.get 3
            local.get 4
            call 4
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
  (func (;31;) (type 14) (param i32 i32 i32 i32 i32)
    (local i32 i32)
    global.get 0
    i32.const 32
    i32.sub
    local.tee 5
    global.set 0
    block ;; label = @1
      block ;; label = @2
        i32.const 1
        call 32
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
        call 33
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
      call 12
      unreachable
    end
    unreachable
  )
  (func (;32;) (type 12) (param i32) (result i32)
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
  (func (;33;) (type 0) (param i32 i32)
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
      call 5
    end
  )
  (func (;34;) (type 2) (param i32 i32) (result i32)
    local.get 0
    i32.const 1049104
    local.get 1
    call 52
  )
  (func (;35;) (type 13) (param i32)
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
      call 5
    end
  )
  (func (;36;) (type 13) (param i32)
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
      call 5
    end
  )
  (func (;37;) (type 0) (param i32 i32)
    local.get 0
    i32.const 0
    i32.store
  )
  (func (;38;) (type 2) (param i32 i32) (result i32)
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
      call 28
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
  (func (;39;) (type 1) (param i32 i32 i32) (result i32)
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
      call 28
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
  (func (;40;) (type 2) (param i32 i32) (result i32)
    local.get 1
    local.get 0
    i32.load
    local.get 0
    i32.load offset=4
    call 60
  )
  (func (;41;) (type 2) (param i32 i32) (result i32)
    (local i32)
    global.get 0
    i32.const 32
    i32.sub
    local.tee 2
    global.set 0
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
        call 60
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
      call 52
      local.set 0
    end
    local.get 2
    i32.const 32
    i32.add
    global.set 0
    local.get 0
  )
  (func (;42;) (type 0) (param i32 i32)
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
  (func (;43;) (type 0) (param i32 i32)
    local.get 0
    i32.const 1049184
    i32.store offset=4
    local.get 0
    local.get 1
    i32.store
  )
  (func (;44;) (type 0) (param i32 i32)
    local.get 0
    local.get 1
    i64.load align=4
    i64.store
  )
  (func (;45;) (type 0) (param i32 i32)
    (local i32 i32)
    local.get 1
    i32.load offset=4
    local.set 2
    local.get 1
    i32.load
    local.set 3
    call 8
    block ;; label = @1
      i32.const 8
      i32.const 4
      call 4
      local.tee 1
      br_if 0 (;@1;)
      i32.const 4
      i32.const 8
      call 50
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
  (func (;46;) (type 0) (param i32 i32)
    (local i32 i32 i32 i64)
    global.get 0
    i32.const 48
    i32.sub
    local.tee 2
    global.set 0
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
      call 52
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
    global.set 0
  )
  (func (;47;) (type 0) (param i32 i32)
    (local i32 i32 i32 i64)
    global.get 0
    i32.const 64
    i32.sub
    local.tee 2
    global.set 0
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
      call 52
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
    call 8
    block ;; label = @1
      i32.const 12
      i32.const 4
      call 4
      local.tee 1
      br_if 0 (;@1;)
      i32.const 4
      i32.const 12
      call 50
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
    global.set 0
  )
  (func (;48;) (type 6) (param i32 i32 i32)
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
  (func (;49;) (type 0) (param i32 i32)
    block ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      local.get 1
      call 50
      unreachable
    end
    call 51
    unreachable
  )
  (func (;50;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 24
    unreachable
  )
  (func (;51;) (type 9)
    (local i32)
    global.get 0
    i32.const 32
    i32.sub
    local.tee 0
    global.set 0
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
    call 55
    unreachable
  )
  (func (;52;) (type 1) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 3
    global.set 0
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
    global.set 0
    local.get 1
  )
  (func (;53;) (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 2
    global.set 0
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
    call 54
    local.set 0
    local.get 2
    i32.const 16
    i32.add
    global.set 0
    local.get 0
  )
  (func (;54;) (type 16) (param i32 i32 i32 i32 i32 i32) (result i32)
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
          call 59
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
            call 58
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
          call 58
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
      call 58
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
  (func (;55;) (type 0) (param i32 i32)
    (local i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 2
    global.set 0
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
    call 22
    unreachable
  )
  (func (;56;) (type 6) (param i32 i32 i32)
    (local i32 i64)
    global.get 0
    i32.const 48
    i32.sub
    local.tee 3
    global.set 0
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
    call 55
    unreachable
  )
  (func (;57;) (type 6) (param i32 i32 i32)
    (local i32)
    global.get 0
    i32.const 32
    i32.sub
    local.tee 3
    global.set 0
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
    call 55
    unreachable
  )
  (func (;58;) (type 17) (param i32 i32 i32 i32 i32) (result i32)
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
  (func (;59;) (type 2) (param i32 i32) (result i32)
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
  (func (;60;) (type 1) (param i32 i32 i32) (result i32)
    local.get 0
    i32.load
    local.get 1
    local.get 2
    local.get 0
    i32.load offset=4
    i32.load offset=12
    call_indirect (type 1)
  )
  (data (;0;) (i32.const 1048576) "library/alloc/src/raw_vec/mod.rs\00/rust/deps/dlmalloc-0.2.10/src/dlmalloc.rs\00library/std/src/alloc.rs\00/Users/mnaeraxr/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/itoa-1.0.18/src/lib.rs\00\00\00\00e\00\10\00[\00\00\00\bc\00\00\00\01\00\00\00e\00\10\00[\00\00\00L\01\00\00\01\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899|\fd\8b2W\e6W\f9\02\dfD\bf\e3H\e7\afm]\cb\d6,P\ebcxA\a6Wq\1b\8b\b9memory allocation of  bytes failed\00\00\cc\01\10\00\15\00\00\00\e1\01\10\00\0d\00\00\00L\00\10\00\18\00\00\00d\01\00\00\09\00\00\00\03\00\00\00\0c\00\00\00\04\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\00\00\00\00\08\00\00\00\04\00\00\00\07\00\00\00\08\00\00\00\09\00\00\00\0a\00\00\00\0b\00\00\00\10\00\00\00\04\00\00\00\0c\00\00\00\0d\00\00\00\0e\00\00\00\0f\00\00\00\00\00\00\00\08\00\00\00\04\00\00\00\10\00\00\00assertion failed: psize >= size + min_overhead\00\00!\00\10\00*\00\00\00\b1\04\00\00\09\00\00\00assertion failed: psize <= size + max_overhead\00\00!\00\10\00*\00\00\00\b7\04\00\00\0d\00\00\00\03\00\00\00\0c\00\00\00\04\00\00\00\11\00\00\00capacity overflow\00\00\00\00\03\10\00\11\00\00\00\00\00\10\00 \00\00\00\1c\00\00\00\05\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899index out of bounds: the len is  but the index is \00\00\f4\03\10\00 \00\00\00\14\04\10\00\12\00\00\00")
)
