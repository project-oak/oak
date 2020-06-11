# Oak Concepts

- [Oak Runtime](#oak-runtime)
- [Nodes](#nodes)
  - [WebAssembly](#webassembly)
- [Channels](#channels)
  - [Orphaned Channels](#orphaned-channels)
  - [Invocations](#invocations)
- [Information Flow Control](#information-flow-control)
- [Pseudo-Nodes](#pseudo-nodes)
- [Oak Application](#oak-application)
- [Remote Attestation](#remote-attestation)
- [Time](#time)

## Oak Runtime

The **Oak Runtime** is the core software component of Project Oak; it is
responsible for executing Oak Modules and enforcing policies on top of data, as
well as producing remote attestations for clients.

Each Oak Runtime instance lives in its own dedicated enclave and is isolated
from both the host as well as other enclaves and Oak Runtime instances on the
same machine.

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1YJ8Rt-nunZ7NJ9diQswbwjEMAtGfzjGVY9ogwhA7hsI -->
<img src="images/SystemDiagram.png" width="850">

## Nodes

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
Oak Module development. Independent Software Vendor (ISVs) wishing to run their
code as part of Project Oak need to be able to compile their code to
WebAssembly.

WebAssembly has a well-defined, unambiguous
[formal specification](https://webassembly.github.io/spec/core/valid/instructions.html),
and is targeted by most LLVM-based languages (including C++ and Rust), and
others, for example Go.

## Channels

Communication from an Oak Node to the Oak Runtime and to other Nodes is
implemented via **Channels**. A Channel represents a uni-directional stream of
messages, with a receive half and a send half that an Oak Node can read from or
write to respectively. Each half of a Channel is identified by a **handle**,
which is used as a parameter to the corresponding
[host function](abi.md#host-functions) calls. Channel handles are integer values
that are specific to a particular Node (like per-process UNIX file descriptors),
so handle value 3 for Node A identifies a different Channel than handle value 3
for Node B (unless there happens to be a coincidence of numbering).

The messages that are sent over Channels hold two types of content, data and
handles. The data component is just a collection of bytes, but the handles
component allows references to underlying Channels to be copied between Nodes.

The Node that sends a message includes handle values from its own per-Node
numbering space; the Runtime translates these handles into internal references
to the relevant Channel object.

When a Node receives the message, these Runtime-internal references are
converted to _different_ handle values, newly assigned (by the Runtime) in the
numbering space of the receiving Node. (This is analogous to the
[transfer of file descriptors between different UNIX processes](https://en.wikipedia.org/wiki/File_descriptor#File_descriptors_as_capabilities).)

### Orphaned Channels

A Channel is considered _orphaned_ in particular direction if operations on the
Channel in that direction will never accomplish anything.

- The read half of a Channel is orphaned if there are no live references to the
  write half of the Channel, and the Channel is empty. A read operation on an
  orphaned Channel will return `ErrChannelClosed`, indicating that no read
  operations on the Channel will ever succeed in future.
- The write half of a Channel is orphaned if there are no live references to the
  read half of the Channel, regardless of whether the Channel currently contains
  messages or not. A write operation on an orphaned Channel will return
  `ErrChannelClosed`, indicating that any attempt to write messages to the
  Channel would just result in loss of the message.

A Channel that is orphaned in both read and write directions is a Channel that
has no live references to it, and is dropped.

### Invocations

The _invocation pattern_ is used for several kinds of interaction between Nodes
in Oak, and helps to illustrate the use of Channels. In this pattern, Node A has
an invocation channel to Node B, and it gets Node B to do things for it by
sending an invocation message down this Channel. The invocation message contains
no data, but instead contains references to two other ephemeral Channels:

- A reference to the read half of a _request Channel_ that is used to send
  request messages from A to B.
- A reference to the write half of a _response Channel_ that is used to send
  response messages from B to A.

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1-wHDIo1JcXAJg3jrJa54H0x-dLwjjD3U2YZIc_amctQ -->
<img src="images/InvocationPattern.png" width="550">

Node A keeps hold of a handle for the write half of the request channel, and
sends requests to it. It then reads responses from the read half of the response
channel until the operation is complete, then closes both ephemeral Channel
handles.

Node B acts on the invocation message by reading one or more request messages
from the first handle; once it has performed the requested functionality, it
sends one or more response messages via the second handle, and closes both of
its ephemeral Channel handles.

<img src="images/InvocationPattern.gif" width="550">

## Information Flow Control

The Oak Runtime implements an **information flow control** (IFC) system that has
rules about when information (in the form of messages) can flow. The core idea
is that Oak Nodes and Channels have **labels**, fixed at creation time. Each
Label has two **components**: **confidentiality** and **integrity**, where:

- Confidentiality is roughly equivalent to "secrecy" or "privacy"; confidential
  data becomes "more" confidential as it is mixed with other data.
- Integrity is roughly equivalent to "trusted", "validated", or "authenticated":
  trusted data becomes "less" trusted as it is mixed with other data sources.

Each label component is an unordered set of **tags**, and each **tag** is either
opaque (representing a **bearer token**), or represents a security principal.
For a confidentiality tag, the available principals are:

- A **user**: this tag indicates that data is confidential to this user.
- A particular piece of **code**: this tag indicates that a known Oak
  Application (or part thereof) has access to the data.
- A remote **domain**: this tag indicates that a service at this domain has
  access to the data.

The Runtime keeps track of labels, and enforces **flows-to** checks on data
moving between Nodes and Channels based on these labels.

- Data can only flow from a smaller to a larger confidentiality label: every tag
  in the source label must be present in the destination label.
- Data can only flow from a larger to a smaller integrity label: every tag in
  the destination label must be present in the source label.

There are exceptions to these rules; some Nodes have the **privilege** to bypass
particular data flow label checks. For confidentiality labels, the
**declassification** privileges are:

- The gRPC server pseudo-Node can bypass **user** tag checks, provided that it
  has an authenticated connection (e.g. with OpenID Connect) to the specific
  user.
- The gRPC client pseudo-Node can bypass **domain** tag checks, provided that it
  has an authenticated connection to a gRPC service on the specific domain.
- An individual WebAssembly Node can bypass a **code** tag check, provided that
  the code tag identifies that WebAssembly Node.

At an ABI level, this IFC functionality is visible to Oak Applications as
follows:

- The primitives for creating Nodes and channels include a `label` parameter to
  apply to the new Node or channel. The label of the creating Node must flow-to
  the label of the new Node or channel.
- Channel read and write operations can fail with a `PERMISSION_DENIED` error if
  data flow label checks have failed.
- There are `.._with_privilege` variants of all operations that involve flows-to
  checks, to indicate that a declassification privilege should be taken
  allowance of in the flows-to check.
  - `{node,channel}_create_with_privilege` for creation of new objects.
  - `channel_{read,write}_with_privilege` for message passing.

More details are described in a [separate IFC document](/docs/ifc.md).

## Pseudo-Nodes

An Oak Node is limited to exchanging messages with other Nodes via Channels; to
allow interactions with the outside world, the Oak system also provides a number
of **pseudo-Nodes**.

These pseudo-Nodes present as normal Nodes to the 'normal' Nodes in an Oak
Application:

- Pseudo-Node instances are created with `node_create()` as for Wasm Nodes.
- Nodes exchange messages with the pseudo-Nodes over Channels.

However, the pseudo-Nodes are implemented as part of the Oak Runtime (executing
as native C++ code, rather than Wasm code) so that they can interact with the
outside world.

The available pseudo-Nodes are:

- **gRPC server pseudo-Node**: Provides a 'front door' for external interaction
  with an Oak Application, by implementing a gRPC service. External method
  invocations of the Application's gRPC service are delivered to a channel that
  connects from the pseudo-Node to a Node of the Application, as a message with
  no data bytes but with two attached handles (in the following order):
  - A handle for the read half of a channel holding the inbound request, ready
    for the Node to read.
  - A handle for the write half of a channel that the Node should write the
    corresponding response message(s) to.
- **Logging pseudo-Node**: Provides a logging mechanism for Nodes under
  development by including a single inbound channel; anything received on the
  channel will be logged. This Node should only be enabled during application
  development and debugging (due to the potential for information leakage).
- **gRPC client pseudo-Node**: Provides a mechanism for Oak Nodes to make use of
  an external (non-Oak) gRPC service. Method invocations for the gRPC service
  are sent on the channel to the gRPC client pseudo-Node, as a message with no
  data bytes but with two attached handles (in the following order):
  - A handle for the read half of a channel holding the outbound request.
  - A handle for the write half of a channel that the corresponding response
    message(s) should be written to.
- **Storage pseudo-Node**: Provides a proxy mechanism for access to a persistent
  storage mechanism. Nodes that require storage functionality write storage
  requests to a channel that reaches the storage pseudo-Node, then read the
  associated responses from a corresponding outbound channel from the storage
  pseudo-Node.
- **Roughtime client pseudo-Node**: Provides a mechanism for Oak Nodes to
  retrieve a wall clock time using the
  [Roughtime protocol](https://roughtime.googlesource.com/roughtime).

An Oak Application uses any of these pseudo-Nodes (except the first) by
including an entry for them in its `ApplicationConfiguration`, and creating them
at runtime (with `node_create()`).

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1gRCOzXWCEhp1-GF6Rnd9N6be8hs1sENfleCzXdQMOsc -->
<img src="images/PseudoNodes.png" width="450">

## Oak Application

An **Oak Application** is a set of Oak Nodes running within the same enclave,
and connected by unidirectional channels. The initial connectivity graph
consists of a single Application Node with no associated channel.

Once the Application is running, new Nodes can be created (with
[`node_create`](/docs/abi.md#node_create)), new channels can be created (with
[`channel_create`](/docs/abi.md#channel_create)) and the handles to either half
of the channel may be passed between Nodes (over channels).

Typically, the first Application Node creates a
[gRPC server pseudo-Node](#pseudo-nodes) and sets up a channel from the
pseudo-Node to the Application, on which [gRPC method invocations](#invocations)
are delivered.

The list of allowed WebAssembly modules that can be used to instantiate
WebAssembly Nodes, and the initial Node to run, are specified by an
[Application Configuration](/oak/proto/application.proto).

Once a new Oak Application is initialized and its gRPC endpoint available,
clients may connect to it using individually end-to-end encrypted, authenticated
and attested channels. The [remote attestation](#remote-attestation) process
proves to the client that the remote enclave is indeed running a genuine Oak
Runtime and will therefore obey the policies set on the Oak Node; the Oak
Runtime itself may then optionally prove additional details about the Oak Module
and its properties, which may require reasoning about its internal structure.

## Remote Attestation

Remote attestation is a core part of Project Oak.

When a client connects to an Oak Application (currently via a gRPC connection),
the two first establish a fresh ephemeral session key, and then they provide
assertions to each other over a channel encrypted with that key; the client
relies on this assertion to determine whether it is connecting to a valid
version of the Oak Runtime. In particular, the attestation includes a
_measurement_ (i.e. a hash) of the exact version of the Oak Runtime itself in
the remote enclave, cryptographically bound to the gRPC session and signed by
the hardware root of trust for the remote attestation (e.g. Intel in the case of
SGX).

This functionality is currently provided by the
[Enclave Key Exchange Protocol (EKEP)](https://asylo.dev/docs/concepts/ekep.html)
as part of the [Asylo](https://github.com/google/asylo) framework.

The client first validates the cryptographic integrity of the attestation
received from the server, by checking whether the signature corresponds to a
platform with the desired root of trust (e.g. Intel). At this point the client
may also check for revocation of the key used to sign the attestation.

The client then uses the details of the attestation to determine whether the
specific instance of the Oak Runtime running on the server is trustworthy;
currently this is done by the client providing a list of "known good"
measurements to accept, but in the future this may involve more sophisticated
logic including something along the lines of a Binary Transparency log based on
[Google Trillian](https://github.com/google/trillian).

Once the client is satisfied with the remote attestation provided by the remote
Oak Runtime instance, it may then send data over this channel, encrypting them
with the key established as part of the initial key exchange protocol. This
guarantees that the the data are end-to-end encrypted between the client and
that particular enclave instance (i.e. the encryption is terminated _within_ the
remotely attested enclave on the server side).

Note that the measurement of the Oak Runtime does not include any details about
the specific Oak Application that is running; the client only needs to be
convinced of the fact that it is talking to a legitimate version of the Oak
Runtime, and that this version of the Oak Runtime will correctly propagate
labels (possibly related to declassification) that the client specifies,
regardless of the Oak Application that it happens to be running (including
future versions of the same or other Oak Applications).

## Time

The Oak Runtime includes a Roughtime client pseudo-Node, which allows Oak
Applications to retrieve an approximate wall clock time using the
[Roughtime protocol](https://roughtime.googlesource.com/roughtime). Note that
retrieving the current time is relatively slow, and so is best done
infrequently. (Also, retrieving the time involves interaction with external
servers and so has the potential to leak information via the timing of the
requests.)
