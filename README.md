<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="docs/oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="docs/oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="docs/oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

[![Build Status](https://img.shields.io/github/actions/workflow/status/project-oak/oak/ci.yaml?branch=main&style=for-the-badge)](https://github.com/project-oak/oak/actions/workflows/ci.yaml?query=branch%3Amain)
[![Docs](https://img.shields.io/badge/docs-rust-brightgreen?style=for-the-badge)](https://project-oak.github.io/oak)

Oak is a software platform for building distributed systems providing externally
verifiable (or falsifiable) claims about system behaviors in a transparent way.

Oak provides building blocks that are used to build Enclave Applications, i.e.
applications that are isolated from the host on which they run, and are remotely
attestable.

In this doc we focus on distributed systems composed of heterogeneous "nodes"; a
node may be an Enclave Application running on a server (e.g. private data
center, public cloud provider, etc.), a regular application running on a client
device (e.g. phone, laptop), a regular HTTP or gRPC service, a storage system,
etc. When two nodes talk to each other, either or both of them may be Enclave
Applications. For each interaction between two nodes, we refer to them as
"initiator" and "responder". We avoid the terms "client" and "server" for those
roles, because in some cases the "initiator" node may actually be running on a
"server" - all combinations are possible.

An Enclave Application in an Oak distributed system can remotely attest itself
to other nodes: this consists in providing evidence of its own software and
hardware identity, bound to local cryptographic keys (stored in tamper-proof
hardware, guaranteeing that keys cannot be exfiltrated or copied), ultimately
signed by one or more software or hardware roots of trust available on the host
of that node. The software identity of an Enclave Application consists of
measurements (i.e. digests / hashes) of the executable binaries that contribute
to it, as well as additional data (e.g. configuration).

## Root of Trust

Oak focuses on VM-based
[Trusted Execution Environments (TEEs)](https://en.wikipedia.org/wiki/Trusted_execution_environment)
(e.g. AMD SEV-SNP, Intel TDX) as hardware root of trust for Enclave
Applications. This allows an Enclave Application to provide a remote attestation
report signed by hardware-bound keys in the TEE, which are not accessible by the
service provider. These keys are ultimately rooted in the TEE manufacturer (e.g.
AMD, Intel); this reduces (ideally, removes) the need to trust the service
provider of that node in order to validate its evidence, by distributing trust
across multiple non colluding actors.

## Encrypted Communication

At startup, each Enclave Application generates a local key pair, and binds the
public key to its own evidence. When a node intends to communicate with an
Enclave Application (as either initiator or responder), an end-to-end encrypted
channel is established between the two nodes. As part of the channel
establishment, each node also provides its own evidence (if any) to the other
node, and may use the evidence provided by the other node to establish its
trustworthiness, before deciding whether to exchange data with it.

This encrypted and attested channel provides:

- Confidentiality: each node knows that data sent over it may only be read by
  the other node
- Integrity: each node knows that data received over it must have been written
  by the other node
- Authenticity: each node knows the identity of the binary in any attested node
  processing the data it sends over the channel.

## Split Architecture

In order to minimize the attack surface and the Trusted Computing Base (TCB) of
an Enclave Application, Oak encourages a split architecture:

- Enclave Application: a binary built (reproducibly) from open source code,
  running inside the TEE. The Enclave Application has access to the decryption
  keys bound to the attestation evidence; it decrypts incoming requests from
  other nodes, processes them, encrypts responses and sends them back over the
  communication channel. This is the binary that is associated with externally
  verifiable claims. No other binary has access to incoming requests in
  plaintext.

- Host Application: a binary that runs on the host (untrusted) server
  environment that acts as the front-end for the Enclave Application; it exposes
  a gRPC endpoint which is externally reachable by other nodes. This binary only
  ever handles encrypted data; its main job is to create and maintain an
  instance of the Enclave Application in the TEE, and forward encrypted data to
  and from the Enclave Application. It may also contain proprietary logic that
  is needed to interact with the control plane or other internal systems
  necessary to run on the service provider infrastructure.

This architecture means the service provider would not be able to swap the
Enclave Application binary with a different (potentially malicious) one without
being detected. If the service provider were to introduce a backdoor in the
Enclave Application, it would have to sign the binary and publish it in a
verifiable log via the Transparent Release process, which would make the
backdoor irreversibly visible to external observers.

## Sealed Computing

A canonical use of Oak is to build privacy-preserving sealed computing
applications.

In a sealed computing application, a node (usually a client device) sends data
to an enclave application (usually a server), which processes data without the
service provider hosting the enclave application being able to see the inputs,
outputs, or side effects of the computation.

The following is a simplified architectural diagram.

![architectural_overview](docs/images/OakDiagramOverview.svg)

## Operating System

Oak supports two flavors of Operating Systems within the TEE, on which Enclave
Applications may be deployed:

- Oak Restricted Kernel: a very minimal custom written microkernel that only
  supports a single CPU and a single application. It places very severe
  restrictions on what the application can do by only exposing a very limited
  set of syscalls to the application. Oak Restricted Kernel applications are
  suitable for cases where review of the entire trusted code base inside the TEE
  is critical, and the limited features and reduced performance is an acceptable
  trade-off. Ideally it should be possible for a single expert human reviewer to
  review the code of the Oak Restricted Kernel in its entirety in a couple of
  weeks.

- Oak Containers: The Enclave Application is provided as part of an OCI runtime
  bundle. This includes a full Linux kernel and a Linux distribution with a
  container runtime engine inside the TEE. Using the OCI runtime bundle as a
  compatibility layer provides a more familiar development experience and more
  flexibility. Oak Containers also supports multiple CPUs in the TEE and is
  therefore suitable for cases with high performance requirements. The drawback
  of this approach is that the size of the entire trusted code base running in
  the TEE is significantly larger, as it is not feasible for a single human
  reviewer to review the code for the entire Linux kernel and Linux
  distribution. The trust model for his approach relies on the security of the
  broader Linux ecosystem. The additional features and flexibility that the
  Linux kernel provides to the application also makes it more difficult to
  reason about the behavior of an application, which in turn makes the review
  process more complicated.

## Remote Attestation

Remote Attestation is a process by which a TEE provides evidence to a remote
party about its own state and the identity of the workload running inside the
TEE (the Enclave Application).

Oak uses a multi-stage protocol in order to measure the identity of each layer
in the boot process (beyond just the bootloader) and cryptographically bind it
together with the TEE evidence. The [Oak Stage 0 virtual firmware](stage0) is
pre-loaded into the VM memory, and it is covered by the TEE attestation report.
To cover the later boot stages, Oak relies on the
[Device Identifier Composition Engine (DICE)](https://trustedcomputinggroup.org/work-groups/dice-architectures/)
approach, where each boot stage is responsible for measuring the next stage. Oak
augments the attestation report with this additional evidence so that the
identity of all the components of the workload is covered (e.g. kernel and
application) by the evidence.

When a node connects to an Enclave Application, it first requests the
attestation evidence and associated endorsements. The endorsements include a
certificate chain from AMD to prove that the attestation report was signed by a
legitimate AMD CPU and optionally signed statements from the developers of the
various components running inside the enclave. The other node then verifies the
evidence using these endorsements to make sure it matches its expectations. The
client node should ensure that the enclave application is running in an
up-to-date and correctly configured TEE (e.g. the CPU is running up to date
versions of the microcode and SNP firmware and that debugging is disabled) and
that the identity of the various components running inside the enclave matches
expectations.

Once the node is satisfied that the enclave application meets all its
expectations, it uses a public key that is bound to the evidence to set up an
encrypted channel with the enclave application.

To be sure that the enclave application will handle data in accordance with
expectations, external reviewers must review the code running in the TEE. Oak
enables this by publishing provenance information of most Oak components. These
act as a reverse index that allows a reviewer to look up the exact source code
commit that was used to build each component given the measurement digest of the
binary from the attestation evidence. All Oak components are reproducibly
buildable (see Transparent Release below), which means that a reviewer can fetch
the specific source code commit and rebuild the component to confirm that it
produces the same exact measurement digest. This gives the reviewer confidence
that the code version they are reviewing is the exact same code version that was
loaded into the enclave during startup.

## Transparent Release

Transparent Release is a set of formats and tools that allow developers to
publish and consume claims about binary artifacts in a transparent and
non-repudiable way.

As part of the remote attestation process, a node obtains the identity of the
Enclave Application in the form of one or more binary digests (e.g. usually at
least one per each layer of the boot chain); it then needs to establish whether
these measurements are trustworthy.

As a first approximation, we could assume that the client knows exactly which
digests to expect by hard-coding them, and can verify the actual values against
the expected ones locally. This works, but it is very limiting with respect to
the evolution of the server application: as soon as any of the Enclave
Application binaries changes as part of a new release, the node will stop
trusting the Enclave Application, and the two will not be able to interact any
more.

We could solve this by hard-coding in the node a public key used to sign the
binary digests, instead of the digests themselves. This way, when the Enclave
Application binaries change, the developer can sign them with the corresponding
private key in their possession, and distribute these signatures alongside the
remote attestation report to the node, which can then verify the validity of
these signatures. This works, but it has the problem of allowing the Enclave
Application to present different signatures to different nodes, which would be
very hard for users to detect.

The solution implemented is to sign not only the digests when a new release is
created, but also to log this signature to an external append-only verifiable
log. Oak relies on [Rekor](https://docs.sigstore.dev/logging/overview/) (by
Sigstore) as the external verifiable log for this purpose. As part of the
Transparent Release process the signature is logged to Rekor, and an inclusion
proof (or inclusion promise) is obtained from it, signed by Rekor's root key.
This is then stored alongside the binary artifact in question, and provided to
nodes that may want to verify the identity of the Enclave Application. This
makes it impossible for the developer to insert a backdoor in the Enclave
Application without also logging it to the verifiable log.

## Trust Model

We acknowledge that perfect security is impossible. In general, having a smaller
Trusted Computing Base (TCB) is better, and Oak tries to minimize the TCB to the
minimum components that need to be trusted.

### Untrusted

Oak is designed to be verifiably trustworthy without needing to trust the
following:

- most hardware (memory, disk, motherboard, network card, external devices)
- Host Operating System (kernel, drivers, libraries, applications)
- Hypervisor / VMM

The service provider may intend to access and exfiltrate users’ private data.
They own the host machines in the data center, therefore have server root access
and are capable of modifying the host machine OS, drivers, hypervisor, etc. They
can also inspect network traffic that contains users’ data. In the Oak
architecture, we treat the host hardware and the host OS operated by the service
provider as untrusted. The data that need to be protected need to be encrypted
when stored in the host OS’s memory system, with the decryption keys managed by
the TEE, not accessible by the service provider hosting the hardware machines.
The Oak architecture allows applications to make stronger claims by reducing the
need to trust the service provider.

### Trusted-but-verifiable

- Oak trusted platform
- Enclave application

Both the Oak platform libraries and components, and the Enclave Application that
runs on that platform, run inside the TEE. They have access to unencrypted data.
Oak establishes trust for these components by open sourcing them, and enables
external inspection and verification via Transparent Release.

### Trusted

- Hardware TEE manufacturer (e.g. AMD, Intel)

The hardware TEE is responsible for memory encryption and decryption, and
generating the remote attestation report, etc.

No particular TEE manufacturer is absolutely trusted by Oak; rather, each client
decides what TEE manufacturer(s) to trust when connecting to Enclave
Applications running on other hosts. Oak makes it possible for Enclave
Applications running on TEEs to present evidence rooted in the manufacturer of
the TEE itself. Additional TEE models and manufacturers may be supported by Oak
over time.

### Side channel attacks

[Side-channel attacks](https://en.wikipedia.org/wiki/Side-channel_attack)
present significant challenges for confidential computing environments. We
acknowledge that most existing TEEs have compromises and may be vulnerable to
various kinds of side-channel attacks. This is an active research area, both
hardware and software innovations are needed to defend against such attacks.
Service providers hosting the TEE based servers need to implement strong host
security. Strong security requires
[defense in depth](<https://en.wikipedia.org/wiki/Defense_in_depth_(computing)>).

Attacks that require physical access to the server hardware is another class of
attacks that Oak and TEE hardware manufacturers cannot defend against alone.
Physical attacks are expensive and therefore not scalable. To defend against
them, service providers need to implement strong physical security in their data
centers.

## Getting involved

We welcome [contributors](docs/CONTRIBUTING.md)! To join our community, we
recommend joining the
[mailing list](https://groups.google.com/g/project-oak-discuss).
