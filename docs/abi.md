# Oak WebAssembly ABI

Oak [Nodes](concepts.md#oak-node) are implemented as WebAssembly modules, and so
can only interact with things outside of the WebAssembly environment through
specific entrypoints which form the **Oak ABI**:

- The [Oak Runtime](concepts.md#oak-runtime) invokes each Oak Node via a single
  [exported function](#exported-function).
- The Oak Node can make use of functionality provided by the Oak TCB by invoking
  [host functions](#host-functions), available as WebAssembly imports.

These host functions provided by the Oak TCB revolve around the creation of
other Nodes, and the use of [channels](concepts.md#channels) for inter-node
communication. This communication is further constrained by **flows-to** checks
based on the [labels](concepts.md#information-flow-control) associated with the
Nodes and channels.

To communicate with the outside world beyond the Oak system, a Node may also
create and communicate with [pseudo-Nodes](concepts.md#pseudo-nodes). The
messages exchanged with pseudo-Nodes are encoded as serialized protocol buffer
messages.

Note also that the Oak ABI interactions are quite low-level; for example, they
involve manual management of linear memory. Oak Applications will typically use
the higher-level [Oak SDK](sdk.md) which provides more convenient (and safer)
wrappers around this functionality.

## Integer Types

WebAssembly has two integer types (`i32` and `i64`) which are treated as
[signed or unsigned values depending on the context](https://webassembly.github.io/spec/core/syntax/types.html#value-types).

Integer types that are passed across the Wasm boundary that forms the Oak ABI
are written as `u32` or `u64` in this document, to make clear that the
corresponding Wasm `i32` or `i64` values are always treated as unsigned values.
(There are currently no uses of signed values in the ABI.)

Integer types that refer to:

- offsets in linear memory
- sizes of regions in linear memory

are written as the `usize` type, which is an alias for the `u32` type in the
current WebAsssembly implementation(s). However, in any future
[64-bit](https://github.com/WebAssembly/design/blob/master/FutureFeatures.md#linear-memory-bigger-than-4-gib)
version of WebAssembly this `usize` type would instead be an alias for the `u64`
type.

Three specific sets of integer values are also used in the ABI:

- Many operations take a `u64` **handle** value; these values are Node-specific
  and non-zero (zero is reserved to indicate an invalid handle), and reference
  one half &ndash; read or write &ndash; of a particular
  [channel](concepts.md#channels).
- Many ABI operations return a `u32` **status** value, indicating the result of
  the operation. The possible values for this are defined in the `OakStatus`
  enum in [oak_abi.proto](/oak/proto/oak_abi.proto).
- The `wait_on_channels` host function fills in a **channel status** value,
  indicating the readiness status of a particular channel. The possible values
  for this are defined in the `ChannelReadStatus` enum in
  [oak_abi.proto](/oak/proto/oak_abi.proto).

## Protocol Buffer Messages

The host functions described [below](#host-functions) allow opaque blobs of data
to be exchanged (along with handles to other channels). When communicating with
the Runtime, these opaque blobs of data are defined to take the form of
serialized protocol buffer messages:

- The label values included on Node and channel creation operations are in the
  form of a serialized [`Label`](/oak/proto/label.proto) message.
- The Node configuration information that is include on `node_create` operations
  is in the form of a serialized
  [`NodeConfiguration`](/oak/proto/application.proto) message.

Similarly, messages exchanged with the pseudo-Nodes provided by the Oak system
are also defined to take the form of serialized protocol buffer messages. These
include:

- [Structured logging messages](/oak/proto/log.proto).
- [Encapsulated gRPC requests and responses](/oak/proto/grpc_encap.proto).
- [Roughtime messages](/oak/proto/roughtime_service.proto).

## Exported Function

Each Oak WebAssembly module must expose at least one **exported function** as a
[WebAssembly export](https://webassembly.github.io/spec/core/syntax/modules.html#exports),
with signature `fn(u64) -> ()`. This function is invoked when the Oak Manager
executes the Oak Node; a handle for the read half of an initial channel is
passed in as a parameter. The name of this entrypoint function for a Node is
provided as part of the
[Application configuration](/oak/proto/application.proto).

The entrypoint function for each Node should perform its own event loop, reading
incoming messages that arrive on the read halves of its channels, sending
outgoing messages over the write halves of channels. The entrypoint function is
generally expected to run forever, but may return if the Node choses to
terminate (whether expectedly or unexpectedly).

Each Oak Application starts with a single initial Oak Node. This Node receives
an invalid handle as its initial handle, and will typically create a
[gRPC server pseudo-Node](concepts.md#pseudo-nodes) to allow communication from
the outside world to happen.

## Host Functions

Each Oak Module may also optionally rely on zero or more of the following **host
functions** as
[WebAssembly imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports)
(all of them defined in the `oak` module):

### `wait_on_channels`

Blocks until data is available for reading from one of the specified channel
handles, unless any of the channels is invalid, orphaned, or violates the
[information flow control](/docs/concepts.md#labels). The channel handles are
encoded in a buffer that holds N contiguous 9-byte chunks, each of which is made
up of an 8-byte channel handle value (little-endian u64) followed by a single
channel status byte. Invalid handles will have an `INVALID_CHANNEL`, `ORPHANED`,
or `PERMISSION_DENIED` status, but `wait_on_channels` return value will only
fail for internal errors or if the runtime is terminating.

- `param[0]: usize`: Address of handle status buffer
- `param[1]: u32`: Count N of handles provided
- `result[0]: u32`: Status of operation

### `channel_read`

Reads a single message and associated channel handles from the specified
channel, setting the size of the data in the location provided by `param[3]`,
and the count of returned handles in the location provided by `param[6]`.

If the provided spaces for data (`param[1]` and `param[2]`) or handles
(`param[4]` and `param[5]`) are not large enough for the read operation, then no
data is written to the destination buffers, and the function returns either
`BUFFER_TOO_SMALL` or `HANDLE_SPACE_TOO_SMALL`; in either case, the required
sizes are written in the spaces provided by `param[3]` and `param[6]`.

If no messages are available on the channel, returns `CHANNEL_EMPTY`.

If reading from the specified channel would violate
[information flow control](/docs/concepts.md#labels), returns
`ERR_PERMISSION_DENIED`.

- `param[0]: u64`: Handle to channel receive half
- `param[1]: usize`: Destination buffer address
- `param[2]: usize`: Destination buffer size in bytes
- `param[3]: usize`: Address of a 4-byte location that will receive the number
  of bytes in the message (as a little-endian u32).
- `param[4]: usize`: Destination handle array buffer (to receive little-endian
  u64 values)
- `param[5]: u32`: Destination handle array count
- `param[6]: usize`: Address of a 4-byte location that will receive the number
  of handles retrieved with the message (as a little-endian u32)
- `result[0]: u32`: Status of operation

### `channel_write`

Writes a single message to the specified channel, together with any associated
handles.

If writing to the specified channel would violate
[information flow control](/docs/concepts.md#labels), returns
`ERR_PERMISSION_DENIED`.

- `param[0]: u64`: Handle to channel send half
- `param[1]: usize`: Source buffer address holding message
- `param[2]: usize`: Source buffer size in bytes
- `param[3]: usize`: Source handle array (of little-endian u64 values)
- `param[4]: u32`: Source handle array count
- `result[0]: u32`: Status of operation

### `channel_create`

Creates a new unidirectional channel assigning the label specified by `param[2]`
and `param[3]` to the newly created Channel, and returns the channel handles for
its read and write halves as output parameters in `param[0]` and `param[1]`.

The label is a serialized [`Label`](/oak/proto/label.proto) protobuf message.

If creating the specified Channel would violate
[information flow control](/docs/concepts.md#labels), returns
`ERR_PERMISSION_DENIED`.

- `param[0]: usize`: Address of an 8-byte location that will receive the handle
  for the write half of the channel (as a little-endian u64).
- `param[1]: usize`: Address of an 8-byte location that will receive the handle
  for the read half of the channel (as a little-endian u64).
- `param[2]: usize`: Source buffer holding serialized `Label`
- `param[3]: usize`: Label size in bytes
- `result[0]: u32`: Status of operation

### `channel_close`

Closes the channel identified by `param[0]`.

- `param[0]: u64`: Handle to channel
- `result[0]: u32`: Status of operation

### `node_create`

Creates a new Node running the Node configuration identified by `param[0]` and
`param[1]`, assigning the label specified by `param[2]` and `param[3]` to the
newly created Node, passing in an initial handle to the read half of a channel
identified by `param[4]`.

The Node configuration is a serialized
[`NodeConfiguration`](/oak/proto/application.proto) protobuf message, and the
label is a serialized [`Label`](/oak/proto/label.proto) protobuf message.

If creating the specified Node would violate
[information flow control](/docs/concepts.md#labels), returns
`ERR_PERMISSION_DENIED`.

- `param[0]: usize`: Source buffer holding serialized `NodeConfiguration`
- `param[1]: usize`: Serialized NodeConfiguration size in bytes
- `param[2]: usize`: Source buffer holding serialized `Label`
- `param[3]: usize`: Label size in bytes
- `param[4]: usize`: Handle to channel
- `result[0]: u32`: Status of operation

### `random_get`

Fills a buffer with random bytes.

- `param[0]: usize`: Destination buffer
- `param[1]: usize`: Destination buffer size in bytes
- `result[0]: u32`: Status of operation
