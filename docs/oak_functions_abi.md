# Oak WebAssembly ABI

Oak functions workloads are implemented as WebAssembly modules, and so can only
interact with things outside of the WebAssembly environment through specific
entrypoints which form the **Oak ABI**:

- The Oak functions server handles each incoming request via a single
  [exported function](#exported-function).
- The workload can make use of functionality provided by the Oak functions TCB
  by invoking [host functions](#host-functions), available as WebAssembly
  imports.

These host functions provided by the Oak TCB allow reading the request and
returning a response.

Note also that the Oak ABI interactions are quite low-level; for example, they
involve manual management of linear memory. WebAssembly workloads will typically
use the higher-level
[Oak Functions SDK](https://project-oak.github.io/oak/oak_functions/sdk/) which
provides more convenient (and safer) wrappers around this functionality.

## Exported Function

Each Oak functions WebAssembly module must expose exactly one **exported
function** as a
[WebAssembly export](https://webassembly.github.io/spec/core/syntax/modules.html#exports),
with signature `fn() -> ()` and name `main`. This function is invoked when the
Oak Manager executes the workload to serve a user request.

## Host Functions

Each Oak Module may also optionally rely on zero or more of the following **host
functions** as
[WebAssembly imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports)
(all of them defined in the `oak_functions` module):

### `read_request`

Reads the request sent by the client.

The low-level operation involves writing the request into the provided space on
the WebAssembly module's memory.

If the provided space for data (`param[0]` and `param[1]`) is not large enough
for the read operation, then no data is written to the destination buffer, and
the function returns `ERR_BUFFER_TOO_SMALL`. In this case, the required size is
written in the space provided by `param[2]`, so that the operation can be
repeated with a larger buffer.

Multiple calls all result in the same values in the destination buffer, and
return the same status.

- `param[0]: usize`: Destination buffer address
- `param[1]: usize`: Destination buffer size in bytes
- `param[2]: usize`: Address of a 4-byte location that will receive the number
  of bytes in the request (as a little-endian u32).
- `result[0]: u32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `write_response`

Writes the response to be sent back to the client.

The low-level operation involves reading the response from the WebAssembly
module's memory.

Multiple calls overwrite the response bytes, and only the last invocation is
considered for the actual response sent to the client.

If this function is never invoked, then an empty response is returned to the
client.

- `param[0]: usize`: Source buffer address holding message
- `param[1]: usize`: Source buffer size in bytes
- `result[0]: u32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `storage_get_item`

Retrieves a single item by key from the lookup data in-memory store.

If no item with the provided key is present, returns
`ERR_STORAGE_ITEM_NOT_FOUND`.

The in-memory store may be periodically refreshed, so multiple calls to this
function, even with identical arguments, may result in different outcomes,
including flipping from success to error or vice versa. In particular, retrying
calling this method after re-allocating the destination buffer based on the
`param[4]` reported size may still fail, for instance if the entry was changed
to have a larger value in the meanwhile; in fact, the entry may even have been
deleted entirely between calls.

- `param[0]: usize`: Source buffer address holding key
- `param[1]: usize`: Source buffer size in bytes
- `param[2]: usize`: Destination buffer address
- `param[3]: usize`: Destination buffer size in bytes
- `param[4]: usize`: Address of a 4-byte location that will receive the number
  of bytes of the value (as a little-endian u32).
- `result[0]: u32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
