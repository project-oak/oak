# Oak Functions WebAssembly ABI

An Oak Functions WebAssembly module interacts with the client only through the
Oak Functions runtime through the **Oak Functions WebAssembly ABI**.

The Oak Functions WebAssembly module
- [exports functions](#exported-functions) to the Oak Functions runtime, and
- [imports functions](#imported-functions) from the Oak Functions runtime.

As the Oak Functions WebAssembly ABI interactions are quite low-level, an Oak
Functions WebAssembly modules will typically use more convenient (and safer)
wrappers from the higher-level [Oak Functions
SDK](https://project-oak.github.io/oak/oak_functions/sdk/).

## Exported Functions

Each Oak Functions WebAssembly module exposes the following functions as
[WebAssembly
exports](https://webassembly.github.io/spec/core/syntax/modules.html#exports) to
the Oak Functions runtime:

### `main() : `

The Oak Functions runtime invokes `main` to start the Oak Functions WebAssembly
module.

- no params
- no results

### `alloc(len: i32) : i32`

The Oak Functions runtime invokes `alloc` when it needs to allocate `len` bytes
of memory from the Oak Functions WebAssembly module to fulfill an Oak Functions
WebAssembly ABI invocation. The Oak Functions WebAssembly module returns the
address of the newly allocated buffer.

The Oak Functions runtime then copies the data in the allocated buffer, i.e.,
the memory of the Oak Functions WebAssembly module, and returns (?? the pointer to
the buffer) as part of the original Oak Functions WebAssembly ABI invocation.

The allocated memory is owned by the caller of the original Oak Functions
WebAssembly ABI invocation, which is responsible for freeing it. The Oak
Functions runtime never directly frees any previously allocated memory.

A canonical implementation of `alloc` is [provided in the Oak Functions Rust
SDK](/oak_functions/sdk/oak_functions/src/lib.rs).

- `param[0]: len: i32`: number of bytes to allocate.
- `result[0]: i32`: address of the newly allocated buffer.

## Imported Functions

Each Oak Functions WebAssembly module can rely on the the Oak functions runtime
providing the following functions as [WebAssembly
imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports):

### `read_request(dest_ptr_ptr: i32, dest_len_ptr: i32) : i32`

The Oak Functions WebAssembly module invokes `read_request` to read the request
from by the client by giving an address to receive the address of an request
buffer allocated by the Oak Functions runtime (`dest_ptr_ptr`) and an address to
receive the corresponding number of bytes (`dest_len_ptr`). The Oak Functions
runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

Multiple calls all result in the same values in the returned buffer, and return
the same status.

- `param[0]: dest_ptr_ptr: i32`: address where the Oak Functions runtime will
  write the address of the request buffer.
- `param[1]: dest_len_ptr: i32`: address where the Oak Functions runtime will
  write the number of bytes of the request buffer (as a little-endian u32).
- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation
  
### `write_response(buf_ptr: i32, buf_len: i32) : i32`

The Oak Functions WebAssembly module invokes `write_response` to write the
response in the response buffer at address `buf_prt` with the corresponding
number of bytes `buf_len`.  The Oak Functions runtime reads the response from
the Oak Functions WebAssembly module's memory and sends it back to the
client. The Oak Functions runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

Multiple calls overwrite the response buffer, and only the last invocation is
 sent to the client. If the Oak Functions WebAssembly module never invokes
 `write_response`, the Oak Functions runtime sends an empty response to the
 client.
 
- `param[0]: buf_ptr: i32`: address of the response buffer.
- `param[1]: buf_len: i32`: number of bytes of the response buffer.

- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation
  
### `write_log_message(buf_ptr: i32, buf_len: i32) : i32`

The Oak Functions WebAssembly module invokes `write_log_message` to write a log
message to the log message buffer at address `buf_ptr` with the corresponding
number of bytes `buf_len`. The Oak Functions runtime reads the log message from
the Oak Functions WebAssembly module's memory.  The Oak Functions runtime
returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

The Oak Functions runtime attempts to interpret the bytes in the log message
buffer as a UTF-8 encoded string. If successful, the string is logged as a debug
message.  If the bytes are not a valid UTF-8 string a warning message containing
the UTF-8 decoding error and the raw bytes is logged.

Multiple invocations produce different log message.

Log messages are considered sensitive, so logging is only possible if the
`oak_unsafe` feature is enabled.

- `param[0]: buf_ptr: i32`: address of the log message buffer.
- `param[1]: buf_len: i32`: number of bytes of the log message buffer.

- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation
  
### `report_metric(buf_ptr: i32, buf_len: i32, value: i64) : i32`

The Oak Functions WebAssembly module invokes `report_metric` to report the
metric value `value` for a sum-based metric bucket identifed by a label. The Oak
Functions runtime reads the label from the label buffer at address `buf_ptr`
with the corresponding number of bytes `buf_len` from the WebAssembly module's
memory. The Oak Functions runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto).

The Oak Functions runtime attempts to interpret the bytes in the label buffer
as a UTF-8 encoded string. If the decoding is successful, the string is used as
a label to identify the bucket. If the bytes are not a valid UTF-8 string or the
string does not match the label of a configured bucket the metric value will be
ignored.

If differentially-private metrics are enabled in the configuration the
aggregated bucket totals per label will be logged in batches after the required
amount of noise has been added. Only buckets that are explicitly allowed in the
configuration will be tracked and included in the results.

If metrics are reported for the same bucket multiple times in a single request
only the last reported value will be used for that request.

If values are not reported for some buckets during a request it will be treated
as if values of 0 were reported for those buckets.

- `param[0]: buf_ptr: i32`: address of the label buffer.
- `param[1]: buf_len: i32`: number of bytes of the label buffer.
- `param[2]: value: i64`: the metrics value to report.

- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation
  
### `storage_get_item(key_ptr: i32, key_len: i32, value_ptr_ptr: i32, value_len_ptr: i32) : i32`

The Oak Functions WebAssembly module invokes `storage_get_item` to retrieve a
single item for the given key from the lookup data in-memory store of the Oak
Functions runtime. The Oak Functions runtime reads the key from the key buffer
`key_ptr` with the corresponding number of bytes `key_len` from the WebAssembly
module's memory. If the item is found, the Oak Functions runtime uses `alloc` to
allocate a buffer of the exact size to contain the item. Then the Oak Functions
runtime writes the item in the allocated buffer and the address of the
allocated buffer to `value_ptr_ptr` together with the address for the size of
the allocated buffer to `value_len_ptr`.

The Oak Functions runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto). In
particular, if no item with the given key is found, the status is
`ERR_STORAGE_ITEM_NOT_FOUND`.

- `param[0]: key_ptr: i32`: address of the key buffer.
- `param[1]: key_len: i32`: number of bytes of the key buffer.
- `param[2]: value_ptr_ptr: i32`: address where the Oak Functions runtime will
  write the address of the buffer containing the item.
- `param[3]: value_len_ptr: i32`: address where the Oak Functions runtime will
  write the number of bytes of the newly allocated value buffer (as a
  little-endian u32).
- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation

### `tf_model_infer(input_ptr: i32, input_len: i32, inference_ptr_ptr, inference_len_ptr: i32) : i32`

The Oak Functions WebAssembly module invokes `tf_model_infer` to run the
specified TensorFlow model for the given input.

The Oak Functions runtime reads the input from the input buffer `input_ptr` with
the corresponding number of bytes `input_len` from the WebAssembly module's
memory to compute the inference vector and uses `alloc` to allocate a buffer of
the exact size to contain the inference vector. Then the Oak Functions runtime
writes the inference in the allocated buffer and the address of the allocated
buffer to `inference_ptr_ptr` together with the address for the size of the
allocated buffer to `inference_len_ptr`.

The Oak Functions runtime returns an
[`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto). In
particular, if no TensorFlow model is present, the status is
`ERR_TENSOR_FLOW_MODEL_NOT_FOUND`.

`tf_model_infer` is experimental, and is only available when the `oak-tf`
feature is enabled.

- `param[0]: input_ptr: i32`: address of the input buffer.
- `param[1]: input_len: i32`: number of bytes of the input buffer.
- `param[2]: inference_ptr_ptr: i32`: address where the Oak Functions runtime
  will write the address of the newly allocated inference buffer.
- `param[3]: inference_len_ptr: i32`: address where the Oak Functions runtime
  will write the number of bytes of the newly allocated inference buffer (as a
  little-endian u32).

- `result[0]: i32`:
  [`OakStatus`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/abi.proto)
  of the invocation

