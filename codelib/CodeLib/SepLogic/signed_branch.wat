(module
  (func (param i32 i32) (result i32)
    block
      local.get 0
      local.get 1
      i32.ge_s
      br_if 0
      i32.const 0
      return
    end
    i32.const 1
    return))
