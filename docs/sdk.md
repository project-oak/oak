# Oak SDK

Project Oak provides a Rust SDK with helper functions to facilitate interactions
with the Oak Runtime from Rust code compiled to WebAssembly. This provides
idiomatic Rust abstractions over the lower level
[WebAssembly interface](abi.md).

This page gives a summary of the functionality available in this SDK; refer to
the [generated documentation](https://project-oak.github.io/oak/sdk) for more
detailed information.

## `oak_abi` Crate

The
[`oak_abi`](https://project-oak.github.io/oak/oak_abi/doc/oak_abi/index.html)
crate provides Rust definitions that correspond to the [Oak ABI](abi.md). This
includes:

- `extern "C"` declarations of the low-level
  [host functions](abi.md#host-functions) provided by the ABI; the `u32`, `u64`
  and `usize` [integer types described in the Oak ABI](abi.md#integer-types)
  definition are mapped to the Rust integer types with the same names.
- A
  [`Handle`](https://project-oak.github.io/oak/oak_abi/doc/oak_abi/type.Handle.html)
  type alias for `u64` channel handle values.
- Constants used on the ABI (such as the
  [`INVALID_HANDLE`](https://project-oak.github.io/oak/oak_abi/doc/oak_abi/constant.INVALID_HANDLE.html)
  value).
- Enum types (generated from the
  [master protocol buffer definitions](/oak/proto/oak_abi.proto)) for
  [operation and channel status values](abi.md#integer-types).
- Generated Rust code corresponding to
  [protocol buffer message types](abi.md#protocol-buffer-messages) that are used
  as part of the Oak ABI.

## `oak` Crate

The majority of the Oak Rust SDK is provided by the top-level `oak` crate. This
includes wrapper functions for all of the
[host functions](abi.md#host-functions) provided by the Oak ABI, using Rust
types for easier use.

- Status values are returned as
  [`oak::OakStatus`](https://project-oak.github.io/oak/sdk/doc/oak/enum.OakStatus.html)
  `enum` values rather than `i32` values.
- Channel handles are held in the
  [`ReadHandle`](https://project-oak.github.io/oak/sdk/doc/oak/struct.ReadHandle.html)
  or
  [`WriteHandle`](https://project-oak.github.io/oak/sdk/doc/oak/struct.WriteHandle.html)
  wrapper `struct`s for handles whose directionality is known.
- Read channel readiness is handled with `Vec<oak::ReadHandle>` and
  `Vec<oak::ChannelReadStatus>` types rather than raw memory.
- Channel read operations automatically re-size the outputs to accommodate the
  contents of read messages.

The `oak` crate also provides the
[`oak::set_panic_hook()`](https://project-oak.github.io/oak/sdk/doc/oak/fn.set_panic_hook.html)
helper, to ensure that Rust `panic`s are logged.

### `oak::io` Module

The [`oak::io`](https://project-oak.github.io/oak/sdk/doc/oak/io/index.html)
module provides a higher level abstraction to allow Rust objects to be
communicated between Nodes.

The
[`oak::io::channel_create<T>`](https://project-oak.github.io/oak/sdk/doc/oak/io/fn.channel_create.html)
function creates
[`oak::io::Sender`](https://project-oak.github.io/oak/sdk/doc/oak/io/struct.Sender.html)
and
[`oak::io::Receiver`](https://project-oak.github.io/oak/sdk/doc/oak/io/struct.Receiver.html)
objects. These objects allow sending and receiving of values of type `T`,
provided that `T` implements the
[`oak::io::Encodable`](https://project-oak.github.io/oak/sdk/doc/oak/io/trait.Encodable.html)
and
[`oak::io::Decodable`](https://project-oak.github.io/oak/sdk/doc/oak/io/trait.Decodable.html)
traits.

### `oak::rand` Module

The `oak::rand` module provides an implementation of the
[`rand::RngCore`](https://rust-random.github.io/rand/rand/trait.RngCore.html)
trait, to allow use of the
[`rand`](https://rust-random.github.io/rand/rand/index.html) crate in Oak code.

### `oak::grpc` Module

The [`oak::grpc`](https://project-oak.github.io/oak/sdk/doc/oak/grpc/index.html)
module holds functionality that is helpful for interacting with the outside
world over gRPC, either via an explicitly created
[gRPC server pseudo-Node](concepts.md#pseudo-nodes), or via an explicitly
created gRPC client pseudo-Node.

An Oak Node that acts as a gRPC server typically implements the
[`oak::grpc::ServerNode`](https://project-oak.github.io/oak/sdk/doc/oak/grpc/trait.ServerNode.html)
trait, which is used with the
[`oak::run_event_loop()`](https://project-oak.github.io/oak/sdk/doc/oak/fn.run_event_loop.html)
function to services gRPC requests in a loop, invoking the trait's
[`invoke()`](https://project-oak.github.io/oak/sdk/doc/oak/grpc/trait.ServerNode.html#tymethod.invoke)
method for each request.

### `oak::storage` Module

The
[`oak::storage`](https://project-oak.github.io/oak/sdk/doc/oak/storage/index.html)
module holds functionality that is helpful for interacting with an external
provider of persistent storage.

### `oak::roughtime` Module

The
[`oak::roughtime`](https://project-oak.github.io/oak/sdk/doc/oak/roughtime/index.html)
module holds functionality for retrieving an approximate wall clock time via a
consensus of [Roughtime](https://roughtime.googlesource.com/roughtime) servers,
as a `Duration` since the UNIX epoch.

### `oak::proto` Module

The
[`oak::proto`](https://project-oak.github.io/oak/sdk/doc/oak/proto/index.html)
module holds auto-generated submodules for dealing with protocol buffers.

### `oak::logger` Module

The
[`oak::logger`](https://project-oak.github.io/oak/sdk/doc/oak/logger/index.html)
module is a logging implementation for the Rust
[log facade](https://crates.io/crates/log), which uses a channel to a
freshly-created logging pseudo-Node as the underlying logging mechanism.
