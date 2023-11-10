# Oak Functions WebAssembly ABI

An Oak Functions WebAssembly module interacts with Oak Functions through the
**Oak Functions WebAssembly ABI**. The Oak Functions WebAssembly module can
interact with the client _only_ through the Oak Functions runtime.

The Oak Functions WebAssembly module

- [exports functions](#exported-functions) to the Oak Functions runtime, and
- [imports functions](#imported-functions) from the Oak Functions runtime.

The Oak Functions WebAssembly ABI is quite low-level, and it is mostly a way to
allow building a more expressive API based on an invocation-bsaed
[microRPC](/micro_rpc/) transport on top of it.

Oak Functions WebAssembly modules will typically use more convenient (and safer)
wrappers from the higher-level [Oak Functions SDK](/oak_functions_sdk/).

For a description of the API, see the
[protobuf definition](/proto/oak_functions/sdk/oak_functions_wasm.proto).

## Exported Functions

Each Oak Functions WebAssembly module exposes the following functions as
[WebAssembly exports](https://webassembly.github.io/spec/core/syntax/modules.html#exports)
to the Oak Functions runtime:

### `main`

- no params
- no results

The Oak Functions runtime invokes `main` to start the Oak Functions WebAssembly
module.

### `alloc`

- `param[0]: len: i32`: number of bytes to allocate.
- `result[0]: i32`: address of the newly allocated buffer.

The Oak Functions runtime invokes `alloc` when it needs to allocate `len` number
of bytes of memory from the Oak Functions WebAssembly module to fulfill an Oak
Functions WebAssembly ABI invocation. The Oak Functions WebAssembly module
returns the address of the newly allocated buffer. Then, to fulfill the
invocation the Oak Functions runtime copies the data in the allocated buffer,
i.e., the memory of the Oak Functions WebAssembly module.

The allocated memory is owned by the Oak Functions WebAssembly module originally
invoking the WebAssembly ABI. The Oak Functions runtime never directly frees
memory allocated from the WebAssembly module through `alloc`.

A canonical implementation of `alloc` is
[provided in the Oak Functions Rust SDK](/oak_functions/sdk/oak_functions/src/lib.rs).

## Imported Functions

Each Oak Functions WebAssembly module can rely on the the Oak Functions runtime
providing the following functions as
[WebAssembly imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports):

### `invoke`

- `param[0]: request_ptr: i32`: address of the request buffer.
- `param[1]: request_len: i32`: number of bytes of the request buffer.
- `param[2]: response_ptr_ptr: i32`: address where the Oak Functions runtime
  will write the address of the buffer containing the response.
- `param[3]: response_len_ptr: i32`: address where the Oak Functions runtime
  will write the number of bytes of the newly allocated response buffer (as a
  little-endian u32).
- `result[0]: i32`: numeric
  [`StatusCode`](https://github.com/grpc/grpc/blob/master/doc/statuscodes.md#status-codes-and-their-use-in-grpc)
  reprsenting the result of the invocation. Note that this is in addition to any
  status code that the API implementation may return; it only represents the
  success or failure of the Wasm invocation itself as a transport.

The Oak Functions WebAssembly module invokes `invoke` to send a request to the
API of the Oak Functions runtime. The Oak Functions runtime reads the request
from the request buffer `request_ptr` with the corresponding number of bytes
`request_len` from the WebAssembly module's memory. The request is passed to the
API implementation, which implements a micro RPC transport. The Oak Functions
runtime uses `alloc` to allocate a buffer of the exact size to contain the
response and writes it in the allocated buffer. Then the Oak Functions runtime
writes the address of the allocated buffer to `response_ptr_ptr` together with
the address of the corresponding size to `response_len_ptr`. The Oak Functions
runtime returns a numeric
[`StatusCode`](https://github.com/grpc/grpc/blob/master/doc/statuscodes.md#status-codes-and-their-use-in-grpc).
