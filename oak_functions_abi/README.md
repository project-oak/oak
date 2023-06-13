# Oak Functions WebAssembly ABI

An Oak Functions WebAssembly module interacts with Oak Functions through the
**Oak Functions WebAssembly ABI**. The Oak Functions WebAssembly module can
interact with the client _only_ through the Oak Functions runtime.

The Oak Functions WebAssembly module

- [exports functions](#exported-functions) to the Oak Functions runtime, and
- [imports functions](#imported-functions) from the Oak Functions runtime.

As the Oak Functions WebAssembly ABI is quite low-level, an Oak Functions
WebAssembly modules will typically use more convenient (and safer) wrappers from
the higher-level [Oak Functions SDK](/oak_functions_sdk/).

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

### `read_request`

- `param[0]: dest_ptr_ptr: i32`: address where the Oak Functions runtime will
  write the address of the request buffer.
- `param[1]: dest_len_ptr: i32`: address where the Oak Functions runtime will
  write the number of bytes of the request buffer (as a little-endian u32).
- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation

The Oak Functions WebAssembly module invokes `read_request` to read a request
from the client. The Oak Functions WebAssembly module provides an address where
the Oak Functions runtime will write the address of the request buffer
(`dest_ptr_ptr`) and an address to write the corresponding number of bytes
(`dest_len_ptr`). The Oak Functions runtime uses `alloc` to allocate the request
buffer from the Oak Functions WebAssembly module and writes the request buffers
address and length in `dest_ptr_ptr` and `dest_len_ptr`. The Oak Functions
runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

`read_request` is idempotent. Multiple calls result in the same values in the
request buffer and return the same status.

### `write_response`

- `param[0]: buf_ptr: i32`: address of the response buffer.
- `param[1]: buf_len: i32`: number of bytes of the response buffer.
- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation

The Oak Functions WebAssembly module invokes `write_response` to write a
response in the response buffer at address `buf_prt` with the corresponding
number of bytes `buf_len`. The Oak Functions runtime reads the response from the
Oak Functions WebAssembly module's memory and sends it back to the client. The
Oak Functions runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

Multiple calls overwrite the response buffer, and only the last invocation is
sent to the client. If the Oak Functions WebAssembly module never invokes
`write_response`, the Oak Functions runtime sends an empty response to the
client.

### `invoke`

- `param[0]: handle: i32`:
  [`ExtensionHandle`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  to address the extension.
- `param[1]: request_ptr: i32`: address of the request buffer.
- `param[2]: request_len: i32`: number of bytes of the request buffer.
- `param[3]: response_ptr_ptr: i32`: address where the Oak Functions runtime
  will write the address of the buffer containing the response.
- `param[4]: response_len_ptr: i32`: address where the Oak Functions runtime
  will write the number of bytes of the newly allocated response buffer (as a
  little-endian u32).
- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation

The Oak Functions WebAssembly module invokes `invoke` to send a reqeuest to an
extension of the Oak Functions runtime. The Oak Functions runtime reads the
request from the request buffer `request_ptr` with the corresponding number of
bytes `request_len` from the WebAssembly module's memory. The request is passed
to the extension addressed by the given `handle`. If the extension returns a
response, the Oak Functions runtime uses `alloc` to allocate a buffer of the
exact size to contain the item and writes the item in the allocated buffer. Then
the Oak Functions runtime writes the address of the allocated buffer to
`response_ptr_ptr` together with the address of the corresponding size to
`response_len_ptr`. The Oak Functions runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

The following
[`ExtensionHandles`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
are currently supported:

- `LookupHandle`: The Oak Functions runtime retrieves a single (optional) item
  for the given key from the lookup data in-memory store of the Oak Functions
  runtime. If no item with the given key is found, it returns `None`.
- `LoggingHandle`: The Oak Functions runtime attempts to interpret the bytes in
  the log message buffer as a UTF-8 encoded string. If successful, the string is
  logged as a debug message. If the bytes are not a valid UTF-8 string a warning
  message containing the UTF-8 decoding error and the raw bytes is logged. Each
  invocation produces a log message. Log messages are considered sensitive, so
  logging is only possible if the `oak_unsafe` feature is enabled.
