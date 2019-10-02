# Oak SDK

Project Oak provides a Rust SDK with helper functions to facilitate interactions
with the Oak VM from Rust code compiled to WebAssembly. This provides idiomatic
Rust abstractions over the lower level WebAssembly interface.

This page gives a summary of the functionality available in this SDK; refer to
the [generated documentation](https://project-oak.github.io/oak) for more
detailed information.

## `oak` Crate

The majority of the Oak Rust SDK is provided by the top-level `oak` crate. This
includes wrapper functions for all of the
[host functions](abi.md#host-functions) provided by the Oak ABI, using Rust
types for easier use.

- Status values are returned as
  [`oak::OakStatus`](https://project-oak.github.io/oak/sdk/oak/proto/oak_api/enum.OakStatus.html)
  `enum` values rather than `i32` values.
- Channel handles are held in the
  [`Handle`](https://project-oak.github.io/oak/sdk/oak/type.Handle.html) type,
  or in the
  [`ReadHandle`](https://project-oak.github.io/oak/sdk/oak/struct.ReadHandle.html)
  or
  [`WriteHandle`](https://project-oak.github.io/oak/sdk/oak/struct.WriteHandle.html)
  wrapper `struct`s for handles whose directionality is known.
- Read channel readiness is handled with `Vec<oak::ReadHandle>` types rather
  than raw memory.
- Channel read operations automatically re-size the outputs to accomodate the
  contents of read messages.

The `oak` crate also provides

- [`oak::logging_channel()`](https://project-oak.github.io/oak/sdk/oak/fn.logging_channel.html)
  to allow access to logging via the `std::io::Write` trait.
- [`oak::set_panic_hook()`](https://project-oak.github.io/oak/sdk/oak/fn.set_panic_hook.html)
  to ensure that Rust `panic`s are logged.

### `oak::wasm` Module

The lowest level of access to the [Oak ABI](abi.md) is provided by the
[`oak::wasm`](https://project-oak.github.io/oak/sdk/oak/wasm/index.html) module.
This module simply provides the Rust `extern "C"` declarations of the
[host functions](abi.md#host-functions) provided by the ABI.

### `oak::io` Module

The [`oak::io`](https://project-oak.github.io/oak/sdk/oak/io/index.html) module
provides the
[`oak::io::Channel`](https://project-oak.github.io/oak/sdk/oak/io/index.html)
wrapper for an
[`Oak::WriteHandle`](https://project-oak.github.io/oak/sdk/oak/struct.WriteHandle.html),
to allow outbound channel use in situations where an implementation of the Rust
`std::io::Write` trait is required.

### `oak::rand` Module

The `oak::rand` module provides an implementation of the
[`rand::RngCore`](https://rust-random.github.io/rand/rand/trait.RngCore.html)
trait, to allow use of the
[`rand`](https://rust-random.github.io/rand/rand/index.html) crate in Oak code.

### `oak::grpc` Module

The [`oak::grpc`](https://project-oak.github.io/oak/sdk/oak/grpc/index.html)
module holds functionality that is helpful for interacting with the outside
world over gRPC, via the [gRPC pseudo-Node](concepts.md#pseudo-nodes).

An Oak Node that interacts with gRPC typically implements the
[`oak::grpc::OakNode`](https://project-oak.github.io/oak/sdk/oak/grpc/trait.OakNode.html)
trait together with the
[`oak::grpc::event_loop()`](https://project-oak.github.io/oak/sdk/oak/grpc/fn.event_loop.html)
function; the latter services gRPC requests in a loop, invoking the former
trait's
[`invoke()`](https://project-oak.github.io/oak/sdk/oak/grpc/trait.OakNode.html#tymethod.invoke)
method for each request.

### `oak::storage` Module

The
[`oak::storage`](https://project-oak.github.io/oak/sdk/oak/storage/index.html)
module holds functionality that is helpful for interacting with an external
provider of persistent storage.

### `oak::proto` Module

The [`oak::proto`](https://project-oak.github.io/oak/sdk/oak/proto/index.html)
module holds auto-generated submodules for dealing with protocol buffers.

## `oak_log` Crate

The [`oak_log`](https://project-oak.github.io/oak/sdk/oak_log/index.html) crate
is a logging implementation for the Rust
[log facade](https://crates.io/crates/log), which uses an Oak logging channel
for the underlying logging mechanism.

## `oak_derive` Crate

The [`oak_derive`](https://project-oak.github.io/oak/sdk/oak_derive/index.html)
crate provides the
[`OakExports`](https://project-oak.github.io/oak/sdk/oak_derive/index.html)
[derive macro](https://doc.rust-lang.org/reference/procedural-macros.html#derive-macros).
This macro annotates a `struct` that implements the `oak::grpc::OakNode` trait,
so that it serves as the Node's overall `oak_main` entrypoint.
