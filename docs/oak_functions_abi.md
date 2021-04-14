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

Reads the user request. The low-level operation involves writing the request
into the provided space on the WebAssembly module's memory. If the provided
space for data (`param[0]` and `param[1]`) is not large enough for the read
operation, then no data is written to the destination buffer, and the function
returns `BUFFER_TOO_SMALL`. In this case, the required size is written in the
space provided by `param[2]`, so that the operation can be repeated with a
larger buffer.

- `param[0]: usize`: Destination buffer address
- `param[1]: usize`: Destination buffer size in bytes
- `param[2]: usize`: Address of a 4-byte location that will receive the number
  of bytes in the request (as a little-endian u32).
- `result[0]: u32`: Status of operation

### `write_response`

Writes the response that should be sent to the user. The low-level operation
involves reading the response from the WebAssembly module's memory.

- `param[0]: usize`: Source buffer address holding message
- `param[1]: usize`: Source buffer size in bytes
- `result[0]: u32`: Status of operation
