# Project Oak

Project Oak is about creating protocols and infrastructure for secure transfer,
storage and processing of data.

In traditional systems, data are usually encrypted at rest and in transit, but
the decoding key must be available to any system that needs to process them at
all, which means there are opportunities for system administrators, hardware
vendors, privileged software running on the same machine to obtain access to
such keys and compromise the confidentiality and integrity of the data. Even if
the application is securely designed and data are encrypted, the operating
system kernel (and any person or piece of software with root or privileged
access) has unrestricted access to the machine hardware resources, and can
leverage that to bypass any security mechanism on the machine and extract secret
keys and data.

With Project Oak, data is end-to-end encrypted between _enclaves_, which are
isolated compartment that can be created on-demand, and provide strong
confidentiality, integrity, and attestation capabilities, usually backed by
hardware features. Enclaves protect data and code even from the operating system
kernel and privileged software.

# Oak VM

The Oak VM is the core component of Project Oak; it is responsible for executing
business logic and enforcing policies on top of data, as well as producing
hardware-backed attestations for clients.

The current version of the Oak VM supports
[WebAssembly](https://webassembly.org) as the target language for business logic
applications. Developers wishing to run their code as part of Project Oak need
to be able to compile their code to WebAssembly. WebAssembly has a well-defined,
unambiguous
[formal specification](https://webassembly.github.io/spec/core/valid/instructions.html),
and is targeted by most LLVM-based languages (including C++ and Rust).

# Oak Server

The Oak Server is a gRPC server that allows clients to request and interact with
Oak VM instances. It exposes a gRPC API allowing clients to interact with the
untrusted runtime and create trusted Oak VM instances within enclaves. Each Oak
VM instance lives in its own enclave and is isolated from both the host as well
as other enclaves and Oak VM instances.

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

# Compile and run

`./run_server_docker`

(in another terminal)

`./run_client`
