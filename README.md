# ![Project Oak](docs/oak-logo/svgs/oak-logo.svg?sanitize=true)

[![Build Status](https://img.shields.io/github/workflow/status/project-oak/oak/Continuous%20Integration/main?style=for-the-badge)](https://github.com/project-oak/oak/actions?query=workflow%3A%22Continuous+Integration%22+branch%3Amain)
[![codecov](https://img.shields.io/codecov/c/github/project-oak/oak?style=for-the-badge)](https://codecov.io/gh/project-oak/oak)
[![Docs](https://img.shields.io/badge/docs-rust-brightgreen?style=for-the-badge)](https://project-oak.github.io/oak)
[![Slack](https://img.shields.io/badge/slack-project--oak-purple?logo=slack&style=for-the-badge)](https://join.slack.com/t/project-oak/shared_invite/zt-5hiliinq-f0fYZGwlzfH3kMrJuu3qlw)
[![Mailing list](https://img.shields.io/badge/mailing_list-project--oak--discuss-red?logo=gmail&style=for-the-badge)](https://groups.google.com/g/project-oak-discuss)

The goal of Project Oak is to create a specification and a reference
implementation for the secure transfer, storage and processing of data.

In present computing platforms (including virtualized, and cloud platforms),
data may be encrypted at rest and in transit, but they are exposed to any part
of the system that needs to process them. Even if the application is securely
designed and data are encrypted, the operating system kernel (and any component
with privileged access to the machine that handles the data) has unrestricted
access to the machine hardware resources, and can leverage that to bypass any
security mechanism on the machine itself and extract secret keys and data.

[Oak Functions](/oak_functions) is a server binary that exposes an API (over
gRPC / HTTP) that allows clients to send data, and the server to execute
untrusted business logic code over client-provided data in a controlled way,
enforcing strong privacy guarantess about its execution.

In order for these guarantees to be transferred to remote clients, Oak Functions
is expected to be run in a
[Trusted Execution Environment (TEE)](https://en.wikipedia.org/wiki/Trusted_execution_environment),
so that clients can perform
[Remote Attestation](https://en.wikipedia.org/wiki/Trusted_Computing#REMOTE-ATTESTATION)
in order to establish that a legitimate version of the Oak trusted runtime is
indeed running server side, before actually sending any data to it.

Further information is included in the following documents:

- [Oak Development](docs/development.md) covers practical steps for getting a
  development Oak system up and running.
- [Oak Functions](oak_functions/README.md) presents our computing platform for
  developing stateless applications in a privacy preserving way.

## Parties involved

- **Oak Trusted Runtime Authors**: The authors of the code in this repository;
  mostly this corresponds to the Project Oak team, but also any contributors,
  and, by extension, the authors of third party dependencies used in Oak.
- **TEE Manufacturer**: The entity in charge of manufacturing the CPU or System
  on a Chip (SoC) supporting the TEE, including hardware, software, and
  cryptographic keys.
- **Platform Provider**: The entity in charge of maintaining and running the
  combined hardware and software stack surrounding the TEE, for instance a cloud
  provider; this includes their software, hardware, and employees.
- **Untrusted Business Logic Authors**: The authors of the untrusted business
  logic, compiled to Wasm, that is executed by the Oak Functions Runtime.

## Threat Model

- **untrusted**:
  - most hardware (memory, disk, motherboard, network card, external devices)
  - Operating System (kernel, drivers, libraries, applications)
  - Platform Provider
  - Untrusted Business Logic Authors
- **trusted-but-verifiable**:
  - Oak Trusted Runtime Authors (their actions are verifiable via
    https://github.com/project-oak/transparent-release)
- **trusted**:
  - TEE Manufacturer
- **partly or conditionally trusted**:
  - end users

Side channels are out of scope for Project Oak software implementation. While we
acknowledge that most existing TEEs have compromises and may be vulnerable to
various kinds of attacks (and therefore we do need resistance to side channels)
we leave their resolution to the respective TEE Manufacturers and other
researchers.

End users are considered "partly trusted" in that we assume that when two users
exchange data, there is a pre-existing basic trust relationship between them; in
particular we assume that the recipient of the data is not going to
intentionally circumvent robust protection mechanisms on their device in order
to extract the received data.

## Getting involved

We welcome [contributors](docs/CONTRIBUTING.md)! To join our community, we
recommend joining the
[mailing list](https://groups.google.com/g/project-oak-discuss) and the
[slack](https://join.slack.com/t/project-oak/shared_invite/zt-5hiliinq-f0fYZGwlzfH3kMrJuu3qlw).
