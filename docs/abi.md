# Oak ABI

### WebAssembly Interface

Each Oak Module must expose the following **exported function** as a
[WebAssembly export](https://webassembly.github.io/spec/core/syntax/modules.html#exports):

-   `oak_main: () -> i32`: Invoked when the Oak Manager executes the Oak Node.
    This function should perform its own event loop, reading incoming messages
    that arrive on the read halves of its channels, sending outgoing messages over
    the write halves of channels.  This function is generally expected to run
    forever, but may return a status if the Node choses to terminate (whether
    expectedly or unexpectedly).

Communication from the Oak Module to the Oak VM and to other modules is
implemented via **channels**. A channel represents a uni-directional stream of
messages, with a receive half and a send half that an Oak module can read from
or write to respectively. Each half of a channel is identified by a **handle**,
which is used as a parameter to the corresponding host function calls.

A collection of pre-configured channel halves are available to the Oak Node,
as specified in the `ApplicationConfiguration` used to create the Node.
The handles for these channels can be retrieved by using the `channel_find` host
function (below) to map a port name to the relevant channel handle.

The default port names that are configured by the `oak::DefaultConfig()`
[helper function](oak/common/app_config.h) and its ancillaries
(`oak::AddLoggingToConfig()`, `oak::AddStorageToConfig()`) are:

-   `log` (send): Messages sent to this channel will treated as
    UTF-8 strings to be logged.
-   `grpc_in` (receive): This channel will be populated with incoming
    gRPC request messages, for processing by the Oak Node.  Each message is a
    serialized `GrpcRequest` protocol buffer message (see
    [/oak/proto/grpc_encap.proto](oak/proto/grpc_encap.proto)).
-   `grpc_out` (send): This channel can be used to send gRPC response
    messages.  Each such message should be encoded as a serialized
    `GrpcResponse` protocol buffer message (see
    [/oak/proto/grpc_encap.proto](oak/proto/grpc_encap.proto)).
-   `storage_in` (receive): This channel will be populated with incoming
    storage response messages, for processing by the Oak Node.  Each message is a
    serialized `StorageOperationResponse` protocol buffer message (see
    [/oak/proto/storage.proto](oak/proto/storage.proto)).
-   `storage_out` (send): This channel can be used to send storage request
    messages.  Each such message should be encoded as a serialized
    `StorageOperationRequest` protocol buffer message (see
    [/oak/proto/storage.proto](oak/proto/storage.proto)).

Each Oak Module may also optionally rely on zero or more of the following **host
functions** as [WebAssembly
imports](https://webassembly.github.io/spec/core/syntax/modules.html#imports)
(all of them defined in the `oak` module):

-   `wait_on_channels: (i32, i32) -> i32`: Blocks until data is available for
    reading from one of the specified channel handles.  The channel handles are
    encoded in a buffer that holds N contiguous 9-byte chunks, each of which is
    made up of an 8-byte channel handle value (little-endian u64) followed by a
    single byte that is set on return if data is available on that channel.

    *   arg0: Address of handle status buffer
    *   arg1: Count N of handles provided
    *   return 0: Status of operation

-   `channel_read: (i64, i32, i32, i32, i32, i32, i32) -> i32`: Reads a single
    message and associated channel handles from the specified channel, setting
    the size of the data in the location provided by arg 3, and the count of
    returned handles in the location provided by arg 6.  If the provided spaces
    for data (args 1 and 2) or handles (args 4 and 5) are not large enough for
    the read operation, then no data will be returned and either
    `BUFFER_TOO_SMALL` or `HANDLE_SPACE_TOO_SMALL` will be returned; in either
    case, the required sizes will be returned in the spaces provided by args
    3 and 6.

    *   arg 0: Handle to channel receive half
    *   arg 1: Destination buffer address
    *   arg 2: Destination buffer size in bytes
    *   arg 3: Address of a 4-byte location that will receive the number of
               bytes in the message (as a little-endian u32).
    *   arg 4: Destination handle array buffer (to receive little-endian i64
               values)
    *   arg 5: Destination handle array count
    *   arg 6: Address of a 4-byte location that will receive the number of
               handles retrieved with the message (as a little-endian u32)
    *   return 0: Status of operation

    Similar to
    [`zx_channel_read`](https://fuchsia.dev/fuchsia-src/zircon/syscalls/channel_read)
    in Fuchsia.

-   `channel_write: (i64, i32, i32, i32, i32) -> i32`: Writes a single message
    to the specified channel, together with any associated handles.

    *   arg 0: Handle to channel send half
    *   arg 1: Source buffer address holding message
    *   arg 2: Source buffer size in bytes
    *   arg 3: Source handle array (of little-endian i64 values)
    *   arg 4: Source handle array count
    *   return 0: Status of operation

    Similar to
    [`zx_channel_write`](https://fuchsia.dev/fuchsia-src/zircon/syscalls/channel_write)
    in Fuchsia.

-   `channel_create: (i32, i32) -> i64`: Create a new unidirectional channel and
    return the channel handles for its read and write halves.

    *   arg 0: Address of an 8-byte location that will receive the handle for
               the write half of the channel (as a little-endian u64).
    *   arg 1: Address of an 8-byte location that will receive the handle for
               the read half of the channel (as a little-endian u64).
    *   return 0: Status of operation

-   `channel_close: (i64) -> i32`: Closes the channel identified by arg 0.

    *   arg 0: Handle to channel
    *   return 0: Status of operation

-   `channel_find: (i32, i32) -> i64`: Return the channel handle that
    corresponds to a provided port name, or zero if not found.

    *   arg 0: Source buffer holding port name
    *   arg 1: Source buffer size in bytes
    *   return 0: Channel handle, or zero if not found.
