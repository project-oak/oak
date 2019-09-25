# Oak SDK

Project Oak provides a Rust SDK with helper functions to facilitate interactions
with the Oak VM from Rust code compiled to WebAssembly. This provides idiomatic
Rust abstractions over the lower level WebAssembly interface.

This page gives a summary of the functionality available in this SDK; refer to
the generated documentation for more detailed information.

TODO: Link to a canonical location for generated docs throughout

## `oak` Crate

The majority of the Oak Rust SDK is provided by the top-level `oak` crate.  This
includes wrapper functions for all of the  [host
functions](abi.md#host-functions) provided by the Oak ABI, using Rust types for
easier use.

 - Status values are returned as `oak::OakStatus` `enum` values rather than
   `i32` values.
 - Channel handles are held in the `Handle` type, or in the `ReadHandle` or
   `WriteHandle` wrapper `struct`s for handles whose directionality is known.
 - Read channel readiness is handled with `Vec<oak::ReadHandle>` types rather
   than raw memory.
 - Channel read operations automatically re-size the outputs to accomodate the
   contents of read messages.

The `oak` crate also provides

 - `oak::logging_channel()` to allow access to logging via the `Write` trait.
 - `oak::set_panic_hook()` to ensure that Rust `panic`s are logged.

### `oak::wasm` Module

The lowest level of access to the [Oak ABI](abi.md) is provided by the
`oak::wasm` module.  This module simply provides the Rust `extern "C"` declarations
of the [host functions](abi.md#host-functions) provided by the ABI.

### `oak::io` Module

The `oak::io` module provides the `oak::io::Channel` wrapper for an
`Oak::WriteHandle`, to allow outbound channel use in situations where an
implementation of the Rust `Write` trait is required.

### `oak::grpc` Module

The `oak::grpc` module holds functionality that is helpful for interacting with
the outside world over gRPC, via the [gRPC
pseudo-Node](concepts.md#pseudo-nodes).

An Oak Node that interacts with gRPC typically implements the
`oak::grpc::OakNode` trait together with the `oak::grpc::event_loop()` function;
the latter services gRPC requests in a loop, invoking the former trait's
`invoke()` method for each request.

### `oak::storage` Module

The `oak::storage` module holds functionality that is helpful for interacting
with an external provider of persistent storage.

### `oak::proto` Module

The `oak::proto` module holds auto-generated submodules for dealing with
protocol buffers.

## `oak_log` Crate

The `oak_log` crate is a logging implementation for the Rust [log
facade](https://crates.io/crates/log), which uses an Oak logging channel for the
underlying logging mechanism.

## `oak_derive` Crate

The `oak_derive` crate provides the `OakExports` [derive
macro](https://doc.rust-lang.org/reference/procedural-macros.html#derive-macros).
This macro annotates a `struct` that implements the `oak::grpc::OakNode` trait,
so that it serves as the Node's overall `oak_main` entrypoint.
