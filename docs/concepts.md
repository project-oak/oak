# Oak Concepts

- [Oak Runtime](#oak-runtime)
- [Oak Application](#oak-application)
- [Oak Nodes](#oak-nodes)
  - [WebAssembly Nodes](#webassembly-nodes)
  - [gRPC Server Nodes](#grpc-server-nodes)
  - [gRPC Client Nodes](#grpc-client-nodes)
  - [Logging Nodes](#logging-nodes)
  - [Storage Nodes](#storage-nodes)
- [Channels](#channels)
  - [Pre-Defined Channels and Port Names](#pre-defined-channels-and-port-names)
- [Oak Manager](#oak-manager)
  - [Workflow](#workflow)
- [Remote Attestation](#remote-attestation)
- [Oak Runtime Updates](#oak-runtime-updates)
- [Time](#time)

## Oak Runtime

The **Oak Runtime** is the core software component of Project Oak; it is
responsible for processing, communication, storage of data, enforcing policies
on top of data, and producing remote attestations for clients.

Each Oak Runtime instance lives in its own dedicated enclave and is isolated
from both the host as well as other enclaves and Oak Runtime instances on the
same machine.

## Oak Application

An **Oak Application** is a set of [Nodes](#oak-nodes) running on the same
[Oak Runtime](#oak-runtime), and connected by unidirectional
[Channels](#oak-channels). The initial connectivity graph is specified by an
[Application Configuration](/oak/proto/manager.proto). Once the Application is
running, new channels may be created and handles to either half of the channel
may be passed between Nodes, but no new Nodes can be instantiated
([this will probably change in the future](https://github.com/project-oak/oak/issues/300)).

An Application may have one or more entry points from which it can be invoked by
clients over a gRPC connection; this is specified in the connectivity graph by
including a pair of pre-defined channels to a [gRPC Node](#grpc-nodes).

Once a new Application is initialized and its endpoint available, clients may
connect to it using individually end-to-end encrypted, authenticated and
attested channels. The remote attestation process proves to the client that the
remote enclave is indeed running a genuine Oak Runtime and will therefore obey
the labels set on the incoming data.

## Oak Nodes

An **Oak Node** is the unit of execution in Oak.

Each type of Node is implemented by the Oak Runtime, but Node instances may be
parametrized with data or code that it executes at runtime, or with constraints
or configuration details.

An Oak Application which intends to use any type of Nodes must include them (and
channels to/from them) in its
[Application Configuration](/oak/proto/manager.proto). An example configuration
that includes all type of Nodes is depicted below.

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1gRCOzXWCEhp1-GF6Rnd9N6be8hs1sENfleCzXdQMOsc-->
<img src="images/PseudoNodes.png" width="450">

### WebAssembly Nodes

A **WebAssembly Node** is configured with a
[WebAssembly module](https://webassembly.org/docs/modules/), that is interpreted
by a WebAssembly interpreter (currently
[WABT](https://github.com/WebAssembly/wabt)) built into the node itself.

We chose WebAssembly because it has a well-defined, unambiguous
[formal specification](https://webassembly.github.io/spec/core/valid/instructions.html),
and is targeted by most LLVM-based languages (including C++ and Rust), and
others, for example Go.

Each WebAssembly Node encapsulates an internal mutable state, corresponding the
[WebAssembly linear memory](https://webassembly.org/docs/semantics/#linear-memory)
on which the Oak Module operates. Concurrent invocations of the same WebAssembly
Node are serialized so that they do not concurrently access the same underlying
memory, but individual invocations may modify the internal state in such a way
that it is observable in subsequent invocations, potentially by different
clients (assuming this is allowed by the policies associated with the Oak Node
in the first place).

### gRPC Server Nodes

A **gRPC Server Node** provides a 'front door' for external interaction with an
Oak Application, by implementing a gRPC service. External requests to the gRPC
service are written to an outbound channel from the gRPC Node, which then
expects to receive response messages on a corresponding inbound channel.

### gRPC Client Nodes

TODO: <https://github.com/project-oak/oak/issues/308>

### Logging Nodes

A **Logging Node** provides a logging mechanism for Nodes under development by
including a single inbound channel; anything received on the channel will be
logged in plain text on the host machine. This node should only be enabled
during application development and debugging (due to the potential for
information leakage).

### Storage Nodes

A **Storage Node** provides a proxy mechanism for access to a persistent storage
mechanism. Nodes that require storage functionality write storage requests to a
channel that reaches the storage Node, then read the associated responses from a
corresponding outbound channel from the storage Node.

## Channels

Communication from an Oak Node to the Oak Runtime and to other Oak Nodes is
implemented via **channels**. A channel represents a uni-directional stream of
messages, with a receive half and a send half that an Oak Node can read from or
write to respectively. Each half of a channel is identified by a **handle**,
which is used as a parameter to the corresponding
[host function](abi.md#host-functions) calls.

### Pre-Defined Channels and Port Names

A collection of pre-configured channel halves are available to the Oak Node, as
specified in the `ApplicationConfiguration` used to create the Node. The handles
for these channels can be retrieved by using the
[`channel_find`](/docs/abi.md#host-functions) host function to map a _port name_
to the relevant channel handle.

## Oak Manager

The **Oak Manager** instantiates Oak Applications running within a platform
provider.

Note that the Oak Manager is not part of the TCB: the actual trusted attestation
only happens between client and the Oak Application running in the enclave at
execution time.

The particular case where the TEE is provided by Intel SGX is shown in the
following system diagram.

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1YJ8Rt-nunZ7NJ9diQswbwjEMAtGfzjGVY9ogwhA7hsI -->
<img src="images/SystemDiagram.png" width="850">

### Workflow

In response to an application creation request, the Oak Manager sends back to
the caller details about the gRPC endpoint of the newly created Oak Application,
initialized with the application configuration specified in the request.

Sample flow:

- ISV writes an Oak Module for the Oak Runtime using a high-level language and
  compiles it to WebAssembly.
- The client connects to the Oak Manager, and requests the creation of an Oak
  Application with the provided Application Configuration.
  - The WebAssembly Module code itself is passed as part of the Application
    Configuration.
- The Oak Manager creates a new enclave and initializes it with a fresh Oak
  Runtime, and then seals the enclave. The Oak Application exposes a gRPC server
  endpoint at a newly allocated endpoint (host:port). The endpoint gets
  forwarded to the client as part of the creation response.
  - Note that up to this point no sensitive data has been exchanged.
  - The client still has no guarantees that the endpoint is in fact running an
    Oak Runtime, as the Oak Manager is itself untrusted.
- The client connects to the Oak Application endpoint, and exchanges keys using
  the
  [Asylo assertion framework](https://asylo.dev/docs/reference/proto/identity/asylo.identity.v1.html).
  - This allows the client to verify the integrity of the Oak Runtime, and
    optionally also assert further properties about the remote system (e.g.
    possession of additional secret keys, etc.).
  - If the client is satisfied with the attestation, it continues with the rest
    of the exchange, otherwise it aborts immediately.
- The client sends its (potentially sensitive) data to the Oak Application (via
  the gRPC Server Node), alongside one or more secrecy labels that it requires
  the Oak Runtime to enforce on the data.
- The gRPC Server Node receives the data and performs the desired (and
  pre-determined) computation on top of them, and sends the results back to the
  client.

The following sequence diagram shows a basic flow of requests between a client,
the Oak Manager and an Oak Application.

<!-- From (Google-internal): http://go/sequencediagram/view/5170404486283264 -->
<img src="images/BasicFlow.png" width="850">

## Remote Attestation

Remote attestation is a core part of Project Oak. When a client connects to an
Oak Application (currently through a gRPC Server Node), the two first establish
a fresh ephemeral session key, and then they provide assertions to each other
over a channel encrypted with such key; the client relies on this assertion to
determine whether it is connecting to a valid version of the Oak Runtime (see
below for what constitutes a valid version). In particular, the attestation
includes a _measurement_ (i.e. a hash) of the Oak Module running in the remote
enclave, cryptographically bound to the session itself.

## Oak Runtime Updates

Under normal circumstances, a client connecting to an Oak Node validates the
attestation it receives from the Oak Node when establishing the connection
channel. The measurement in the attestation report corresponds to the hash of
the code loaded in enclave memory at the time the connection was established.
Because the Oak Runtime changes relatively infrequently, the list of known
measurements is small enough that the client is able to just check the inclusion
of the received measurement in the list.

Occasionally, a particular version of the Oak Runtime may be found to contain
security vulnerabilities or bugs, and we would like to prevent further clients
from connecting to servers using such versions.

TODO: Verifiable log of known versions, Binary Transparency, Key Transparency.

## Time

TODO: Roughtime
