# Oak Concepts

- [Oak Runtime](#oak-runtime)
- [Oak Node](#oak-node)
  - [WebAssembly](#webassembly)
- [Channels](#channels)
  - [Pre-Defined Channels and Port Names](#pre-defined-channels-and-port-names)
- [Pseudo-Nodes](#pseudo-nodes)
- [Oak Application](#oak-application)
- [Oak Manager](#oak-manager)
  - [Workflow](#workflow)
- [Remote Attestation](#remote-attestation)
- [Oak Runtime Updates](#oak-runtime-updates)
- [Time](#time)

## Oak Runtime

The **Oak Runtime** is the core software component of Project Oak; it is
responsible for executing Oak Modules and enforcing policies on top of data, as
well as producing remote attestations for clients.

Each Oak Runtime instance lives in its own dedicated enclave and is isolated
from both the host as well as other enclaves and Oak Runtime instances on the
same machine.

## Oak Node

The unit of execution in Oak is an **Oak Node**. The code for an Oak Node is a
self-contained [WebAssembly module](https://webassembly.org/docs/modules/) that
is interpreted by an Oak Runtime instance as part of an Oak Application.

Each running Oak Node has a single thread of execution, and also encapsulates an
internal mutable state, corresponding the
[WebAssembly linear memory](https://webassembly.org/docs/semantics/#linear-memory)
on which the Oak Module operates.

This single-threaded execution means that external invocations of the same Oak
Node are inherently serialized; however, the effect of one invocation may modify
internal state and so affect the result of a subsequent external request (by the
same client or a different client).

Clients may therefore wish to only make use of an Oak Node that allows multiple
invocations if it can be shown that the submitted data can only be retrieved in
sufficiently anonymized form in subsequent invocations by other clients.

### WebAssembly

The current version of the Oak Runtime supports
[WebAssembly](https://webassembly.org) as the first-class target language for
Oak Module development. Developers wishing to run their code as part of Project
Oak need to be able to compile their code to WebAssembly.

WebAssembly has a well-defined, unambiguous
[formal specification](https://webassembly.github.io/spec/core/valid/instructions.html),
and is targeted by most LLVM-based languages (including C++ and Rust), and
others, for example Go.

## Channels

Communication from the Oak Node to the Oak Runtime and to other Nodes is
implemented via **channels**. A channel represents a uni-directional stream of
messages, with a receive half and a send half that an Oak Node can read from or
write to respectively. Each half of a channel is identified by a **handle**,
which is used as a parameter to the corresponding
[host function](abi.md#host-functions) calls. Channel handles are integer values
that are specific to a particular Node (like per-process UNIX file descriptors),
so handle value 3 for Node A identify a different channel than handle value 3
for Node B (unless there happens to be a coincidence of numbering).

## Pseudo-Nodes

An Oak node is limited to exchanging messages with other Nodes via channels; to
allow interactions with the outside world, the Oak system also provides a number
of **pseudo-Nodes**.

These pseudo-Nodes present as normal Nodes to the 'normal' Nodes in an Oak
Application:

- Pseudo-Node instances are created with `node_create()` as for Wasm Nodes (with
  the exception of the gRPC pseudo-Node, which is automatically created at
  Application start-of-day).
- Nodes exchange messages with the pseudo-Nodes over channels.

However, the pseudo-Nodes are implemented as part of the Oak Runtime (executing
as native C++ code, rather than Wasm code) so that they can interact with the
outside world.

The available pseudo-Nodes are:

- **gRPC pseudo-node**: Provides a 'front door' for external interaction with an
  Oak Application, by implementing a gRPC service. The Oak Runtime automatically
  creates a gRPC pseudo-Node at Application start-of-day (and so gRPC
  pseudo-Nodes cannot be created with `node_create()`). External method
  invocations of the Application's gRPC service are delivered to a channel that
  connects from the pseudo-Node to the initial Node of the Application, as a
  message no data bytes but with two attached handles (in the following order):
  - A handle for the read half of a channel holding the inbound request, ready
    for the Node to read.
  - A handle for the write half of a channel that the Node should write the
    corresponding response message(s) to.
- **Logging pseudo-node**: Provides a logging mechanism for Nodes under
  development by including a single inbound channel; anything received on the
  channel will be logged. This node should only be enabled during application
  development and debugging (due to the potential for information leakage).
- **Storage pseudo-node**: Provides a proxy mechanism for access to a persistent
  storage mechanism. Nodes that require storage functionality write storage
  requests to a channel that reaches the storage pseudo-Node, then read the
  associated responses from a corresponding outbound channel from the storage
  pseudo-Node.

An Oak Application uses any of these pseudo-Nodes (except the first) by
including an entry for them in its `ApplicationConfiguration`, and creating them
at runtime (with `node_create()`).

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1gRCOzXWCEhp1-GF6Rnd9N6be8hs1sENfleCzXdQMOsc-->
<img src="images/PseudoNodes.png" width="450">

## Oak Application

An **Oak Application** is a set of Oak Nodes running within the same enclave,
and connected by unidirectional channels. The initial connectivity graph
consists of:

- A gRPC pseudo-Node.
- An initial Application Node.
- A single channel from the gRPC pseudo-Node to the initial Application Node.

Once the Application is running, new Nodes can be created (with
`node_create()`), new channels can be created (with `channel_create()`) and the
handles to either half of the channel may be passed between Nodes (over
channels).

The allowed contents of the Nodes, and the initial Node to run, are specified by
an [Application Configuration](/oak/proto/manager.proto).

Once a new Oak Application is initialized and its endpoint available, clients
may connect to it using individually end-to-end encrypted, authenticated and
attested channels. The remote attestation process proves to the client that the
remote enclave is indeed running a genuine Oak Runtime and will therefore obey
the policies set on the Oak Node; the Oak Runtime itself may then optionally
prove additional details about the Oak Module and its properties, which may
require reasoning about its internal structure.

## Oak Manager

The **Oak Manager** creates Oak Applications running within a platform provider.

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
  Node running the compiled Oak Module.
  - The module code itself is passed as part of the creation request.
- The Oak Manager creates a new enclave and initializes it with a fresh Oak
  Node, and then seals the enclave. The Oak Node exposes a gRPC endpoint at a
  newly allocated endpoint (host:port). The endpoint gets forwarded to the
  client as part of the creation response.
  - Note up to this point no sensitive data has been exchanged.
  - The client still has no guarantees that the endpoint is in fact running an
    Oak Runtime, as the Oak Manager is itself untrusted.
- The client connects to the Oak Node endpoint, and exchanges keys using the
  [Asylo assertion framework](https://asylo.dev/docs/reference/proto/identity/asylo.identity.v1.html).
  - This allows the client to verify the integrity of the Oak Node and the fact
    that it is indeed running an actual Oak Runtime, and optionally also
    asserting further properties about the remote system (e.g. possession of
    additional secret keys, etc.).
  - If the client is satisfied with the attestation, it continues with the rest
    of the exchange, otherwise it aborts immediately.
- The client sends its (potentially sensitive) data to the Oak Node, alongside
  one or more policies that it requires the Oak Node to enforce on the data.
- The Oak Node receives the data and performs the desired (and pre-determined)
  computation on top of them, and sends the results back to the client.

The following sequence diagram shows a basic flow of requests between a client,
the Oak Manager and an Oak Application.

<!-- From (Google-internal): http://go/sequencediagram/view/5170404486283264 -->
<img src="images/BasicFlow.png" width="850">

## Remote Attestation

Remote attestation is a core part of Project Oak. When a client connects to an
Oak Node, the two first establish a fresh ephemeral session key, and then they
provide assertions to each other over a channel encrypted with such key; the
client relies on this assertion to determine whether it is connecting to a valid
version of the Oak Runtime (see below for what constitutes a valid version). In
particular, the attestation includes a _measurement_ (i.e. a hash) of the Oak
Module running in the remote enclave, cryptographically bound to the session
itself.

The client may then infer additional properties about the Oak Module running on
the remote enclave, e.g. by means of "static attestation" certificates that are
produced as a byproduct of compiling the Oak Module source code itself on an
enclave and having the enclave sign a statement that binds the (hash of the)
compiled Oak Module to some high-level properties of the source code.

TODO: Expand on this.

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
