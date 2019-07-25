(module
  (type (;0;) (func (result i32)))
  (type (;1;) (func (param i64 i32 i32) (result i32)))
  (type (;2;) (func (param i64 i32 i32 i32) (result i32)))
  (import "oak" "channel_write" (func $channel_write (type 1)))
  (import "oak" "channel_read" (func $channel_read (type 2)))
  (func $oak_initialize (type 2)
    i32.const 0)
  (func $oak_handle_grpc_call (type 0)
    i32.const 0)
  (memory (;0;) 18)
  (export "memory" (memory 0))
  (export "oak_initialize" (func $oak_initialize))
  (export "oak_handle_grpc_call" (func $oak_handle_grpc_call)))