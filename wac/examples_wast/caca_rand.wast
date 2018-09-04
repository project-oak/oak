(module
  (import "libcaca.so.0" "caca_rand"
    (func $caca_rand (param i32 i32) (result i32)))
  (func $doRand (param i32 i32) (result i32)
    (call $caca_rand
      (get_local 0) (get_local 1)))
  (export "rand" (func $doRand)))
