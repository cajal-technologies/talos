(module
  (func $gcd (export "gcd") (param i32 i32) (result i32)
    (local i32)
    (loop $outer
      (block $break
        (local.get 1)
        (i32.eqz)
        (br_if $break)
        (local.get 0)
        (local.get 1)
        (i32.rem_u)
        (local.set 2)
        (local.get 1)
        (local.set 0)
        (local.get 2)
        (local.set 1)
        (br $outer)
      )
    )
    (local.get 0)
  )
)
 