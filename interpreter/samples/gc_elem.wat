(module
  (type $arr (array i32))
  (type $anyrefs (array anyref))
  (table $t 1 anyref)
  (elem $passive anyref (item (array.new_default $arr (i32.const 3))))
  (elem (table $t) (i32.const 0) anyref (item (ref.i31 (i32.const 70))))
  (func (export "passive_len") (result i32)
    (array.len
      (ref.cast (ref $arr)
        (array.get $anyrefs
          (array.new_elem $anyrefs $passive (i32.const 0) (i32.const 1))
          (i32.const 0)))))
  (func (export "active_i31") (result i32)
    (i31.get_s (ref.cast (ref i31) (table.get $t (i32.const 0))))))
