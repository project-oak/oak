(module
  (type (;0;) (func (param i64) (result i32)))
  (type (;1;) (func (param i64 i32 i32 i32 i32) (result i32)))
  (type (;2;) (func (param i64 i32 i32 i32 i32 i32 i32) (result i32)))
  (import "oak" "channel_write" (func $channel_write (type 1)))
  (import "oak" "channel_read" (func $channel_read (type 2)))
  (func $oak_main (type 0)
    i32.const 1)
  (memory (;0;) 18)
  (export "memory" (memory 0))
  (export "oak_main" (func $oak_main)))