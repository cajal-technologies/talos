(module
  (memory 1)
  (func (param i32) (result i32)
    i32.const 0
    local.get 0
    i32.const 4
    memory.fill
    i32.const 0
    i32.load))
