# Proposal for making Oak Functions Extensions more general

We currently have ExtensionFactories that generate Extensions. Extensions
provide the functions available to the per-request Wasm business logic
instances. This document proposes a generalisation of extensions and the ideas
mentioned in issue [#2551](https://github.com/project-oak/oak/issues/2551).

## Naming

We have previously discussed using a more general term, such as "Service" rather
than "Extension". My suggestion is to use `Service` as a replacement for
`ExtensionFactory` and `ServiceProxy` as a replacement for `Extension`.

The shared state used by an extension is generally owned and managed by the
extension factory, and each extension is specific to a single `WasmState`
instance that manages the Wasm execution for a single request. I also considered
`ServiceFactory` and `Service` as respective replacements, but seeing that the
`ServiceFactory` would also manage shared state it seems somewhat inaccurate.

## Design Approach

The `Service` implementation for a feature would manage shared state and create
`ServiceProxy` instances that can be used to perform per-request service-related
actions, and interact with the shared state owned by its parent service where
needed.

Each service implementation would decide whether it must be able to call other
services, and if so provide the ability to inject these services into a
constructor. Each service will also be able to receive configuration information
through a standardised interface.

This single approach would support most of the existing components in the Oak
Functions runtime, but we will need some additional services for things that do
not operate at the same per-request level. One example is a stream
demultiplexer. The external untrusted loader will multiplex all requests and
configuration messages over a single stream, so the demultiplexer It will
receive one multiplexed stream and split it into per-request streams. As it will
not need to provide per-request proxies, the service implementation would
directly provide the ability to process messages and not implement proxy
creation.

## Implemenation Outline

The Rust source code in this directory contains a simple outline implementation
of these ideas to show how this might be applied to compose an Oak Functions
runtime implementation with support for logging and looking up data. This
approach can easily be extended to support the experimental services such as
differentially private metrics and ML inference.

All services are currently implemented to do passthrough or echo just to show
how data might flow through the system.

In a real implementation each module will be implemented in a separate crate,
and, where possible, will be `no_std`-compatible.

The implementation starts with a configuration process, faking control frames to
go to each of the configurable services:

- IoListener
  - Demux
    - LogService
    - LookupService
    - PolicyService
    - SessionService
    - WasmiService

After the configuration, a single data frame is sent through the system. The
flow of data through the runtime is:

- IoListener
  - Demux
    - SessionProxy
      - PolicyProxy
        - WasmiProxy
          - LogProxy
          - LookupProxy
      - PolicyProxy
    - SessionProxy
  - Demux
- IoListener
