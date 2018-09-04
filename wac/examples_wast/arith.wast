(module
  (func $add (param i32 i32) (result i32)
    (i32.add
      (get_local 0)
      (get_local 1)))
  (func $sub (param i32 i32) (result i32)
    (i32.sub
      (get_local 0)
      (get_local 1)))
  (func $mul (param i32 i32) (result i32)
    (i32.mul
      (get_local 0)
      (get_local 1)))
  (func $div (param i32 i32) (result i32)
    (i32.div_u
      (get_local 0)
      (get_local 1)))
  (export "add" (func $add))
  (export "sub" (func $sub))
  (export "mul" (func $mul))
  (export "div" (func $div)))
