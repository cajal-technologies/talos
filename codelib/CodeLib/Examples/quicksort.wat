;; quicksort.wat
;; Lomuto partition quicksort — hand-matched to Quicksort.lean.
;; String-inlined copy lives in Quicksort.lean (quicksortWat); keep in sync.
(module
  (memory 1)

  ;; func 0: partition arr lo hi -> pivotIdx
  ;; locals: arr=0 lo=1 hi=2 pivot=3 i=4 j=5 hiMinusOne=6 tmp=7
  (func (param i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32)
    local.get 2
    i32.const 1
    i32.sub
    local.set 6
    local.get 0
    local.get 6
    i32.const 4
    i32.mul
    i32.add
    i32.load
    local.set 3
    local.get 1
    local.set 4
    local.get 1
    local.set 5
    block
      loop
        local.get 5
        local.get 6
        i32.lt_u
        i32.eqz
        br_if 1
        local.get 3
        local.get 0
        local.get 5
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.lt_u
        if
        else
          local.get 0
          local.get 4
          i32.const 4
          i32.mul
          i32.add
          i32.load
          local.set 7
          local.get 0
          local.get 4
          i32.const 4
          i32.mul
          i32.add
          local.get 0
          local.get 5
          i32.const 4
          i32.mul
          i32.add
          i32.load
          i32.store
          local.get 0
          local.get 5
          i32.const 4
          i32.mul
          i32.add
          local.get 7
          i32.store
          local.get 4
          i32.const 1
          i32.add
          local.set 4
        end
        local.get 5
        i32.const 1
        i32.add
        local.set 5
        br 0
      end
    end
    local.get 0
    local.get 4
    i32.const 4
    i32.mul
    i32.add
    i32.load
    local.set 7
    local.get 0
    local.get 4
    i32.const 4
    i32.mul
    i32.add
    local.get 0
    local.get 6
    i32.const 4
    i32.mul
    i32.add
    i32.load
    i32.store
    local.get 0
    local.get 6
    i32.const 4
    i32.mul
    i32.add
    local.get 7
    i32.store
    local.get 4
    return)

  ;; func 1: quicksort arr lo hi
  ;; locals: arr=0 lo=1 hi=2 pivotIdx=3
  (func (param i32 i32 i32) (local i32)
    local.get 2
    local.get 1
    i32.sub
    i32.const 2
    i32.lt_u
    if
      return
    end
    local.get 0
    local.get 1
    local.get 2
    call 0
    local.set 3
    local.get 0
    local.get 1
    local.get 3
    call 1
    local.get 0
    local.get 3
    i32.const 1
    i32.add
    local.get 2
    call 1
    return))
