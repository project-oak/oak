# Oak WebAssembly ABI

Oak functions workloads are implemented as WebAssembly modules, and so can only
interact with things outside of the WebAssembly environment through specific
entrypoints which form the **Oak ABI**:

- The Oak functions server handles each incoming request via the required
  [exported functions](#exported-functions).
- The workload may make use of functionality provided by the Oak functions TCB
  by invoking [imported functions](#imported-functions), available as
  WebAssembly imports.

These imported functions provided by the Oak TCB allow reading the request and
returning a response.

Note also that the Oak ABI interactions are quite low-level; for example, they
involve manual management of linear memory. WebAssembly workloads will typically
use the higher-level
[Oak Functions SDK](https://project-oak.github.io/oak/oak_functions/sdk/) which
provides more convenient (and safer) wrappers around this functionality.

## Exported Functions

Each Oak Functions WebAssembly module must expose the following functions as
[WebAssembly exports](https://webassembly.github.io/spec/core/syntax/modules.html#exports).

### `main`

This function is invoked when the Oak Functions Loader executes the workload to
serve a user request.

- no params

- no results

### `alloc`

This function is invoked when the Oak Functions Loader needs to allocate memory
for an additional buffer to be returned as part of fulfilling an ABI invocation.

The implementation of this function must allocate exactly `len` bytes of memory
and return the address of the newly allocated buffer, which is then used by the
Oak Functions Loader to copy data in the memory of the currently executing
module, and returned as part of the original ABI invocation.

Once allocated, the memory is considered owned by the caller of the ABI call
being invoked, and the caller is responsible for freeing it if and when
necessary. The Oak Functions Loader never directly frees any previously
allocated memory.

A canonical implementation of this function is already
[provided in the Oak Functions Rust SDK](/oak_functions/sdk/oak_functions/src/lib.rs),
so if using that, there is no need to implement it manually.

- `param[0]: len: i32`: Number of bytes to allocate.

- `result[0]: i32`: Address of the newly allocated buffer.

## Imported Functions

Each Oak Module may also optionally rely on the following **host functions** as
[WebAssembly imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports)
(all of them defined in the `oak_functions` module):

### `read_request`

Reads the request sent by the client.

The low-level operation involves allocating a buffer of the exact size needed to
contain the request buffer.

Multiple calls all result in the same values in the returned buffer, and return
the same status.

- `param[0]: dest_ptr_ptr: i32`: Address of a location that will receive the
  address of the newly allocated request buffer.
- `param[1]: dest_len_ptr: i32`: Address of a location that will receive the
  number of bytes of the newly allocated request buffer (as a little-endian
  u32).

- `result[0]: i32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `write_response`

Writes the response to be sent back to the client.

The low-level operation involves reading the response from the WebAssembly
module's memory.

Multiple calls overwrite the response bytes, and only the last invocation is
considered for the actual response sent to the client.

If this function is never invoked, then an empty response is returned to the
client.

- `param[0]: buf_ptr: i32`: Address of the response buffer.
- `param[1]: buf_len: i32`: Number of bytes of the response buffer.

- `result[0]: i32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `write_log_message`

Writes a log message. This message is considered sensitive, so is only logged if
the `oak_unsafe` feature is enabled.

The low-level operation involves reading the message from the WebAssembly
module's memory. The system attempts to interpret the bytes as a UTF-8 encoded
string. If the decoding is successful, the string is logged as a debug message.
If the bytes are not a valid UTF-8 string a warning message containing the UTF-8
decoding error and the raw bytes is logged.

Multiple calls are each treated as a different log message.

- `param[0]: buf_ptr: i32`: Address of the log message buffer.
- `param[1]: buf_len: i32`: Number of bytes of the log message buffer.

- `result[0]: i32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `report_metric`

Reports a metric value for a specific bucket. The bucket is identified by a
label in the form of a UTF-8 encoded string. If differentially-private metrics
are enabled in the configuration the aggregated bucket totals per label will be
logged in batches after the required amount of noise has been added. Only
buckets that are explicitly allowed in the configuration will be tracked and
included in the results.

The low-level operation involves reading the label from the WebAssembly module's
memory. The system attempts to interpret the bytes as a UTF-8 encoded string. If
the decoding is successful, the string is used as a label to identify the
bucket. If the bytes are not a valid UTF-8 string or does not match the label of
a configured bucket the metric value will be ignored.

If metrics are reported for the same bucket multiple times in a single request
only the last reported value will be used for that request.

If values are not reported for some buckets during a request it will be treated
as if values of 0 were reported for those buckets.

- `param[0]: buf_ptr: i32`: Address of the label buffer.
- `param[1]: buf_len: i32`: Number of bytes of the label buffer.
- `param[2]: value: i64`: The metrics value to report.

- `result[0]: i32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `storage_get_item`

Retrieves a single item by key from the lookup data in-memory store.

If no item with the provided key is present, returns
`ERR_STORAGE_ITEM_NOT_FOUND`.

If an item is found, allocates a buffer of the exact size to contain it, writes
the value in that buffer, and returns it as part of `value_ptr_ptr` and
`value_len_ptr`.

- `param[0]: key_ptr: i32`: Address of the key buffer.
- `param[1]: key_len: i32`: Number of bytes of the key buffer.
- `param[2]: value_ptr_ptr: i32`: Address of a location that will receive the
  address of the newly allocated value buffer.
- `param[3]: value_len_ptr: i32`: Address of a location that will receive the
  number of bytes of the newly allocated value buffer (as a little-endian u32).

- `result[0]: i32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)

### `tf_model_infer`

Runs the TensorFlow model for the given input and returns the inference vector.

If a TensorFlow model is not present, returns `ERR_TENSOR_FLOW_MODEL_NOT_FOUND`.

If a TensorFlow model is present, gets the inference from the model, and
allocates a buffer of the exact size of the inference vector, writes the
inference vector in that buffer, and returns it as part of `inference_ptr_ptr`
and `inference_len_ptr`.

- `param[0]: input_ptr: i32`: Address of the input buffer.
- `param[1]: input_len: i32`: Number of bytes of the input buffer.
- `param[2]: inference_ptr_ptr: i32`: Address of a location that will receive
  the address of the newly allocated inference buffer.
- `param[3]: inference_len_ptr: i32`: Address of a location that will receive
  the number of bytes of the newly allocated inference buffer (as a
  little-endian u32).

- `result[0]: i32`: Status of operation as
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
