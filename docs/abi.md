# Oak ABI

Oak [Nodes](concepts.md#oak-node) are implemented as WebAssembly modules, and so
can only interact with things outside of the WebAssembly environment through
specific entrypoints which form the **Oak ABI**:

- The [Oak Runtime](concepts.md#oak-runtime) invokes each Oak Node via a single
  [exported function](#exported-function).
- The Oak Node can make use of functionality provided by the Oak TCB by invoking
  [host functions](#host-functions), available as WebAssembly imports.

These host functions provided by the Oak TCB revolve around the creation of
other Nodes, and the use of [channels](concepts.md#channels) for inter-node
communication. To communicate with the outside world beyond the Oak system, a
Node may also create and communicate with
[pseudo-Nodes](concepts.md#pseudo-nodes).

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
  and non-zero (zero is reserved to indicate an invalid handle), and reference a
  particular [channel](concepts.md#channels).
- Many ABI operations return a `u32` **status** value, indicating the result of
  the operation. The possible values for this are defined in the `OakStatus`
  enum in [oak_api.proto](/oak/proto/oak_api.proto).
- The `wait_on_channels` host function fills in a **channel status** value,
  indicating the readiness status of a particular channel. The possible values
  for this are defined in the `ChannelReadStatus` enum in
  [oak_api.proto](/oak/proto/oak_api.proto).

## Exported Function

Each Oak Module must expose at least one **exported function** as a
[WebAssembly export](https://webassembly.github.io/spec/core/syntax/modules.html#exports),
with signature `fn(u64) -> ()`. This function is invoked when the Oak Manager
executes the Oak Node; a handle for the read half of an initial channel is
passed in as a parameter. The name of this entrypoint function for a Node is
provided as part of the Application configuration.

The entrypoint function for each Node should perform its own event loop, reading
incoming messages that arrive on the read halves of its channels, sending
outgoing messages over the write halves of channels. The entrypoint function is
generally expected to run forever, but may return if the Node choses to
terminate (whether expectedly or unexpectedly).

Each Oak Application starts with a single initial Oak Node; this Node receives
as its initial handle the read half of a channel that receives notifications of
gRPC method invocations from an implicit
[gRPC server pseudo-Node](concepts.md#pseudo-nodes).

## Host Functions

Each Oak Module may also optionally rely on zero or more of the following **host
functions** as
[WebAssembly imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports)
(all of them defined in the `oak` module):

### wait_on_channels

`wait_on_channels(usize, u32) -> u32` blocks until data is available for reading
from one of the specified channel handles. The channel handles are encoded in a
buffer that holds N contiguous 9-byte chunks, each of which is made up of an
8-byte channel handle value (little-endian u64) followed by a single channel
status byte. Invalid handles will have an `INVALID_CHANNEL` status, but
`wait_on_channels` return value will only fail for internal errors or if _all_
channels are invalid.

- arg 0: Address of handle status buffer
- arg 1: Count N of handles provided
- return 0: Status of operation

### channel_read

`channel_read(u64, usize, usize, usize, usize, u32, usize) -> u32` reads a
single message and associated channel handles from the specified channel,
setting the size of the data in the location provided by arg 3, and the count of
returned handles in the location provided by arg 6. If the provided spaces for
data (args 1 and 2) or handles (args 4 and 5) are not large enough for the read
operation, then no data will be returned and either `BUFFER_TOO_SMALL` or
`HANDLE_SPACE_TOO_SMALL` will be returned; in either case, the required sizes
will be returned in the spaces provided by args 3 and 6. If no messages are
available on the channel, `CHANNEL_EMPTY` will be returned.

- arg 0: Handle to channel receive half
- arg 1: Destination buffer address
- arg 2: Destination buffer size in bytes
- arg 3: Address of a 4-byte location that will receive the number of bytes in
  the message (as a little-endian u32).
- arg 4: Destination handle array buffer (to receive little-endian u64 values)
- arg 5: Destination handle array count
- arg 6: Address of a 4-byte location that will receive the number of handles
  retrieved with the message (as a little-endian u32)
- return 0: Status of operation

Similar to
[`zx_channel_read`](https://fuchsia.dev/fuchsia-src/zircon/syscalls/channel_read)
in Fuchsia.

### channel_write

`channel_write: (u64, usize, usize, usize, u32) -> u32` writes a single message
to the specified channel, together with any associated handles.

- arg 0: Handle to channel send half
- arg 1: Source buffer address holding message
- arg 2: Source buffer size in bytes
- arg 3: Source handle array (of little-endian u64 values)
- arg 4: Source handle array count
- return 0: Status of operation

Similar to
[`zx_channel_write`](https://fuchsia.dev/fuchsia-src/zircon/syscalls/channel_write)
in Fuchsia.

### channel_create

`channel_create: (usize, usize) -> u32` creates a new unidirectional channel and
return the channel handles for its read and write halves.

- arg 0: Address of an 8-byte location that will receive the handle for the
  write half of the channel (as a little-endian u64).
- arg 1: Address of an 8-byte location that will receive the handle for the read
  half of the channel (as a little-endian u64).
- return 0: Status of operation

### channel_close

`channel_close: (u64) -> u32` closes the channel identified by arg 0.

- arg 0: Handle to channel
- return 0: Status of operation

### node_create

`node_create: (usize, usize, usize, usize, u64) -> u32` creates a new Node
running the Node configuration identified by args 0 and 1, using the entrypoint
specified by args 2 and 3, passing in an initial handle to the read half of a
channel identified by arg 4. The entrypoint name is ignored when creating
non-WebAssembly Nodes.

- arg 0: Source buffer holding node configuration name
- arg 1: Node configuration name size in bytes
- arg 2: Source buffer holding entrypoint name.
- arg 3: Entrypoint name size in bytes
- arg 4: Handle to channel
- return 0: Status of operation

### random_get

`random_get: (usize, usize) -> u32` fills a buffer with random bytes.

- arg 0: Destination buffer
- arg 1: Destination buffer size in bytes
- return 0: Status of operation
