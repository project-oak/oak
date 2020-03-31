# Project Oak

[![Build Status](https://img.shields.io/badge/build-status-blue)](https://pantheon.corp.google.com/cloud-build/dashboard?project=oak-ci)
[![Fuzzing Status](https://oss-fuzz-build-logs.storage.googleapis.com/badges/oak.svg)](https://bugs.chromium.org/p/oss-fuzz/issues/list?sort=-opened&can=1&q=proj:oak)
[![Docs](https://img.shields.io/badge/docs-rust-brightgreen)](https://project-oak.github.io/oak)
[![Slack](https://img.shields.io/badge/slack-chat-purple?logo=slack)](https://project-oak.slack.com)

The goal of Project Oak is to create a specification and a reference
implementation for the secure transfer, storage and processing of data.

In present computing platforms (including virtualized, and cloud platforms),
data may be encrypted at rest and in transit, but they are exposed to any part
of the system that needs to process them. Even if the application is securely
designed and data are encrypted, the operating system kernel (and any component
with privileged access to the machine that handles the data) has unrestricted
access to the machine hardware resources, and can leverage that to bypass any
security mechanism on the machine itself and extract secret keys and data.

As part of Project Oak, data are end-to-end encrypted between _enclaves_, which
are isolated computation compartments that can be created on-demand, and provide
strong confidentiality, integrity, and attestation capabilities via a
combination of hardware and software functionality. Enclaves protect data and
code even from the operating system kernel and privileged software, and are
intended to protect from most hardware attacks.

Additionally, data are associated with policies when they enter the system, and
policies are enforced and propagated as data move from enclave to enclave.

Further information is included in the following documents:

- [Oak Concepts](docs/concepts.md) describes the key concepts involved in Oak
  applications.
- [Oak ABI](docs/abi.md) documents the core Oak ABI.
- [Oak SDK](docs/sdk.md) describes the SDK that is provided on top of the Oak
  ABI, to allow more convenient development of Oak applications.
- [Oak Development](docs/development.md) covers practical steps for getting a
  development Oak system up and running.
- [Programming Oak](docs/programming-oak.md) discusses programming for the Oak
  system.

## Terminology

- **Enclave**: A secure CPU compartment that can be created on-demand,
  containing code and data; it enforces isolation from the host and other
  enclave instances running on the same system. It guarantees _confidentiality_
  and _integrity_ of both data and code running within it, and it is capable of
  creating hardware-backed _remote attestations_ to prove to other parties a
  measurement (i.e. hash) of the code and data within the enclave itself. Also
  known as Trusted Execution Environment (TEE).
- **Enclave Manufacturer**: The entity in charge of manufacturing the CPU or
  System on a Chip (SoC) supporting enclaves.
- **Platform Provider**: The entity in charge of maintaining and running the
  combined hardware and software stack surrounding the TEE, for instance in a
  cloud context.
- **Trusted Computing Base (TCB)**: The set of hardware, firmware, software
  components critical to the security of the system; bugs or vulnerabilities
  inside the TCB may jeopardise the security properties of the entire system.
- **Independent Software Vendor (ISV)**: The entity or person providing the code
  for the service running on top of the Project Oak; in the most common case
  this may be a third party developer.

## Threat Model

- **untrusted**:
  - most hardware (memory, disk, motherboard, network card, external devices)
  - Operating System (kernel, drivers, libraries, applications)
  - platform provider (hardware, software, employees)
  - third-party developers
- **trusted-but-verifiable**:
  - Project Oak codebase (and its transitive dependencies)
- **trusted**:
  - enclave manufacturer (and therefore at least some hardware / software)
- **partly or conditionally trusted**:
  - end users

Side channels are out of scope for Project Oak software implementation. While we
acknowledge that most existing enclaves have compromises and may be vulnerable
to various kinds of attacks (and therefore we do need resistance to side
channels) we leave their resolution to the respective enclave manufacturers and
other researchers.

End users are considered "partly trusted" in that we assume that when two users
exchange data, there is a pre-existing basic trust relationship between them; in
particular we assume that the recipient of the data is not going to
intentionally circumvent robust protection mechanisms on their device in order
to extract the received data.
