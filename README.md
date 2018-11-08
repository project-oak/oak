# Project Oak

The goal of Project Oak is to create a specification for secure transfer,
storage and processing of data.

Optionally it may also include a reference implementation and / or an official
SDK.

In traditional systems, data may be encrypted at rest and in transit, but it
must be available in plaintext to any system that needs to process them; this
means there are opportunities for system administrators, hardware vendors,
privileged software running on the same machine to compromise the
confidentiality and integrity of the data.

Even if the application is securely designed and data are encrypted, the
operating system kernel (and any user or piece of software with root or
privileged access on the machine that handles the data) has unrestricted access
to the machine hardware resources, and can leverage that to bypass any security
mechanism on the machine and extract secret keys and data.

As part of Project Oak, data is end-to-end encrypted between _enclaves_, which
are isolated compartments that can be created on-demand, and provide strong
confidentiality, integrity, and attestation capabilities, usually backed by
hardware features. Enclaves protect data and code even from the operating system
kernel and privileged software, and from most hardware attacks.

# Oak VM

The _Oak VM_ is the core software component of Project Oak; it is responsible
for executing business logic and enforcing policies on top of data, as well as
producing hardware-backed attestations for clients.

The current version of the Oak VM supports
[WebAssembly](https://webassembly.org) as the target language for business logic
applications. Developers wishing to run their code as part of Project Oak need
to be able to compile their code to WebAssembly. WebAssembly has a well-defined,
unambiguous
[formal specification](https://webassembly.github.io/spec/core/valid/instructions.html),
and is targeted by most LLVM-based languages (including C++ and Rust).

Project Oak also offers a Rust SDK with helper functions to facilitate
interactions with the Oak VM from Rust code compiled to WebAssembly. This
provides idiomatic Rust abstractions over the lower level WebAssembly interface.

# Oak Server

The Oak Server is a [gRPC](https://grpc.io/) server that allows clients to
request and interact with Oak VM instances. It exposes a gRPC API allowing
clients to interact with the untrusted runtime and request the creation of
ad-hoc trusted Oak VM instances within enclaves. Each Oak VM instance lives in
its own enclave and is isolated from both the host as well as other enclaves and
Oak VM instances.

# Remote Attestation

Remote attestation is a core part of Project Oak. When an Oak Client connects to
an Oak Server, the two first establish a fresh ephemeral session key, and then
they provide assertions to each other over a channel encrypted with such key;
the Oak Client relies on this assertion to determine whether it is connecting to
a valid version of the Oak VM (see below for what constitutes a valid version).
In particular, the attestation includes a _measurement_ (i.e. a hash) of the
code running in the remote enclave, cryptographically bound to the session
itself.

## Platform Upgrades

Under regular circumstances, an Oak Client connecting to an Oak Server validates
the attestation it receives from the Oak Server when establishing the connection
channel. The measurement in the attestation report corresponds to the hash of
the code loaded in enclave memory at the time the connection was established.
Because the Oak VM changes relatively slowly, the list of known measurements is
small enough that the client is able to just check the inclusion of the received
measurement in the list.

Occasionally, a particular version of the Oak VM may be found to contain
security vulnerabilities or bugs, and we would like to prevent further clients
from connecting to servers using such versions. TODO

# Workflow

Sample flow:

-   Developer writes business logic for the Oak VM using a high-level language
    and compiles it to WebAssembly for the Oak platform.
-   The Oak Client connects to the Oak Server scheduler, and requests the
    creation of an Oak VM instance running the compiled WebAssembly business
    logic.
    +   The code itself is passed as part of the scheduling request.
-   The Oak Server scheduler creates a new enclave and initialises it with a
    fresh Oak VM instance, and then seals the enclave. The Oak VM exposes a gRPC
    endpoint at a newly allocated endpoint (host:port). The endpoint gets
    forwarded to the client as part of the scheduling response.
    +   Note up to this point no sensitive data has been exchanged.
    +   The Oak Client still has not guarantees that the endpoint is in fact
        running an Oak VM, as the scheduler is itself untrusted.
-   The Oak Client connects to the Oak VM endpoint, and exchanges keys using the
    [Asylo assertion framework](https://asylo.dev/docs/reference/proto/identity/asylo.identity.v1.html).
    +   This allows the client to verify the integrity of the server and the
        fact that it is indeed running an actual Oak VM, and optionally also
        asserting further properties about the remote system (e.g. possession of
        additional secret keys, etc.).
    +   If the Oak Client is satisfied with the attestation, it continues with
        the rest of the exchange, otherwise it aborts immediately.
-   The Oak Client sends its (potentially sensitive) data to the Oak Server,
    alongside one or more policies that it requires the Oak Server to enforce on
    the data.
-   The Oak Server receives the data and performs the desired (and
    pre-determined) computation on top of them, and sends the results back to
    the Oak Client.

# Oak Policies

TODO

# Time

TODO: Roughtime

# Compile and run

`./run_server_docker`

(in another terminal)

`./run_client`
