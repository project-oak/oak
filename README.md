# Project Oak

The goal of Project Oak is to create a specification and a reference
implementation for the secure transfer, storage and processing of data.

In traditional systems, data may be encrypted at rest and in transit, but they
are exposed to any part of the system that needs to process them. Even if the
application is securely designed and data are encrypted, the operating system
kernel (and any component with privileged access to the machine that handles the
data) has unrestricted access to the machine hardware resources, and can
leverage that to bypass any security mechanism on the machine itself and extract
secret keys and data.

As part of Project Oak, data are end-to-end encrypted between _enclaves_, which
are isolated computation compartments that can be created on-demand, and provide
strong confidentiality, integrity, and attestation capabilities at the hardware
level. Enclaves protect data and code even from the operating system kernel and
privileged software, and from most hardware attacks.

Additionally, data are associated with policies when they enter the system, and
policies are enforced and propagated even as data move from enclave to enclave.

## Terminology

- **Trusted Execution Environment (TEE)**: A secure CPU compartment containing
  code and data; it enforces isolation from the host and other TEE instances
  running on the same system. It guarantees _confidentiality_ and _integrity_
  of both data and code running within it, and it is capable of creating
  hardware-backed _remote attestations_ to prove to other parties a measurement
  of the TEE itself.
- **TEE Manufacturer**: The entity in charge of manufacturing the CPU or SoC
  supporting the TEE.
- **Platform Provider**: The entity in charge of maintaining and running the
  combined hardware and software stack surrounding the TEE, for instance in a
  cloud context.
- **Trusted Computing Base (TCB)**: The set of hardware, firmware, software
  components critical to the security of the system; bugs or vulnerabilities
  inside the TCB may jeopardise the security properties of the entire system.
- **Business Logic Developer**: The entity or person providing the code for the
  service running on top of the Project Oak; in the most common case this may
  be a third party developer.

## Threat Model

- **untrusted**:
  * hardware (memory, disk, motherboard, network card, external devices)
  * Operating System (kernel, drivers, libraries, applications)
  * platform provider (hardware, software, employees)
  * third-party developers
- **trusted-but-verifiable**:
  * Project Oak codebase (and its transitive dependencies)
- **trusted**:
  * TEE manufacturer
- **partly or conditionally trusted**:
  * end users

Side channels are out of scope for Project Oak software implementation. While we
acknowledge that most existing TEE have compromises and may be vulnerable to
various kinds of attacks, we leave their resolution to the respective TEE
manufacturers.

## Oak VM

The _Oak VM_ is the core software component of Project Oak; it is responsible
for executing business logic and enforcing policies on top of data, as well as
producing remote attestations.

### Business Logic - Oak Modules

The unit of compilation and execution in Oak is the Oak Module. Each Oak Module
is a self-contained [WebAssembly module](https://webassembly.org/docs/modules/)
that is interpreted by the Oak VM.

#### WebAssembly

The current version of the Oak VM supports
[WebAssembly](https://webassembly.org) as the first-class target language for
business logic applications. Developers wishing to run their code as part of
Project Oak need to be able to compile their code to WebAssembly.

WebAssembly has a well-defined, unambiguous
[formal specification](https://webassembly.github.io/spec/core/valid/instructions.html),
and is targeted by most LLVM-based languages (including C++ and Rust).

Each Oak VM instance lives in its own dedicated enclave and is isolated from
both the host as well as other enclaves and Oak VM instances on the same
machine.

#### WebAssembly Interface

The entry point of an Oak Module is a WebAssembly exported function named
`oak_main` with signature `() -> nil` (i.e. taking no arguments and returning no
value). This is somewhat similar to a regular `main` function in other
programming languages, except that it does not expect any explicit parameters;
any I/O is instead performed via separate, dedicated methods.

TODO: Use https://webassembly.org/docs/modules/#module-start-function when Rust
supports it.

An Oak Module may optionally rely on one or more **host calls**: these are invoked
as regular WebAssembly functions, but their implementation is fulfilled by the
Oak VM itself in order to perform side-effects or interact with the host system
or other Oak Servers.

All Oak host calls are defined in the `oak` import module.

The currently supported host calls are the following:

-   `print: (i32, 132) -> nil`: Prints a string to standard output on the
    host system. To be used for debugging only, as it leaks data. Will be
    removed before release.

    *   arg 0: Offset of block to print
    *   arg 1: Length of block to print

-   `get_time: (i32) -> nil`: Retrieves the current time from the host
    system. TODO: Implement this via
    [Roughtime](https://blog.cloudflare.com/roughtime/).

    *   arg 0: Offset of block to receive number of milliseconds.

-   `read: (i32, i32, i32) -> i32`: Reads from the specified input channel.

    *   arg 0: Input channel ID
    *   arg 1: Buffer address
    *   arg 2: Buffer size in bytes
    *   return 0: Number of bytes read

-   `write: (i32, i32) -> i32`

    *   arg 0: Buffer address
    *   arg 1: Buffer size in bytes
    *   return 0: Number of bytes written

#### Rust SDK

Project Oak also offers a Rust SDK with helper functions to facilitate
interactions with the Oak VM from Rust code compiled to WebAssembly. This
provides idiomatic Rust abstractions over the lower level WebAssembly interface.

## Oak Server

The Oak Server is a [gRPC](https://grpc.io/) server that allows developers to
deploy code to Oak VM instances, and clients to interact with them.

It consists of various gRPC services with which various categories of users
interact.

### Deployment Service

Business Logic Developers use the Deployment Service to deploy code to an Oak
instance run by a platform provider. Note that this is not part of the TCB,
since the actual trusted attestation only happens between client and server
running in the TEE at execution time.

Oak Modules follow the _serverless_ approach, in which functions are scheduled
on-demand and without developers having to provision or manage servers or
virtual machines.

Business Logic Developers first compile their code for the Oak Platform using
the Oak SDK for their language, resulting in a self-contained Oak Module. They
also manually create a manifest file in
[TOML](https://github.com/toml-lang/toml) format, specifying any extra
capabilities that the module is allowed to have access to. They finally upload
both of them to the Oak Server using the `oak_deploy` command-line tool.

TODO: Implement `oak_deploy`.

### Scheduling Service

When a client needs to perform a computation, it connects to the Scheduling
Service over gRPC and sends a request containing details about the Oak Module to
load, and any associated policies. The Scheduling Service itself is not part of
the TCB, and therefore must be considered untrusted by the client, i.e. the
scheduling service is assumed to be able to modify any (part of) scheduling
requests.

In response to a scheduling request, the Scheduling Service sends back to the
caller details about the gRPC endpoint of the newly created enclave, initialised
with the module and policies specified.

All of this is handled by the `oak_schedule` command-line tool.

TODO: Implement `oak_schedule`.

### Execution Service

Once a new enclave is initialised and its endpoint available, a client connects
to it using an authenticated and attested channel. The attestation proves to the
client that the remote enclave is indeed running a genuine Oak VM, and the Oak
VM itself may prove additional details about the business logic and its
properties.

## Capabilities

A baseline module without any extra capabilities specified in the manifest file
can be considered as a pure function, executing some computation and returning
its result to the caller, with no side effects allowed.

In order to allow the module to perform side effects, capabilities need to be
granted to it that allow the Oak VM to expose the appropriate logic to the
module itself.

### Input / Output Channels

The `input_channel` and `output_channel` capabilities allow the module to have
access to an input or output channel, respectively, managed by the Oak VM. The
channel is securely encrypted by construction (the encryption is performed by
the Oak VM itself).

The public key with which to perform the encryption must be provided as part of
the capability instantiation in the manifest file, so that it becomes part of
the Oak attestation offered by the Oak VM to clients before they exchange any
data with it.

Channels are identified by a sequential number, which is used to interact with
them.

By default, an input channel and an output channel are implicitly created by the
Oak VM and connected to the input and output of the client performing the gRPC
request that initiated the computation. These are available at index 0.

### Storage

TODO

### Logging

TODO

## Remote Attestation

Remote attestation is a core part of Project Oak. When an Oak Client connects to
an Oak Server, the two first establish a fresh ephemeral session key, and then
they provide assertions to each other over a channel encrypted with such key;
the Oak Client relies on this assertion to determine whether it is connecting to
a valid version of the Oak VM (see below for what constitutes a valid version).
In particular, the attestation includes a _measurement_ (i.e. a hash) of the
code running in the remote enclave, cryptographically bound to the session
itself.

## Oak VM Updates

Under regular circumstances, an Oak Client connecting to an Oak VM validates the
attestation it receives from the Oak VM when establishing the connection
channel. The measurement in the attestation report corresponds to the hash of
the code loaded in enclave memory at the time the connection was established.
Because the Oak VM changes relatively infrequently, the list of known
measurements is small enough that the client is able to just check the inclusion
of the received measurement in the list.

Occasionally, a particular version of the Oak VM may be found to contain
security vulnerabilities or bugs, and we would like to prevent further clients
from connecting to servers using such versions.

TODO: Verifiable log of known versions.

## Workflow

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

## Oak Policies

TODO

## Time

TODO: Roughtime

## Development

### Prerequisites

- Docker: https://docs.docker.com/install
- Bazel: https://docs.bazel.build/versions/master/install.html
- Rust: https://rustup.rs/

### Compile and Run

#### Server

The following command builds and runs an Oak Server instance.

`./run_server_docker`

#### Client

The following command (run in a separate terminal) compiles a sample business
logic from Rust to WebAssembly, and sends it to the Oak Server running on the
same machine.

`./run_client`
