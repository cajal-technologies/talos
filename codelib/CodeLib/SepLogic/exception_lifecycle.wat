(module
  (tag $t0 (param i32))
  (func (param i32) (result i32)
    try_table (result i32) (catch $t0 0)
      local.get 0
      throw $t0
    end
    i32.const 99))
