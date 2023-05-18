<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="docs/oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="docs/oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="docs/oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

[![Build Status](https://img.shields.io/github/actions/workflow/status/project-oak/oak/ci.yaml?branch=main&style=for-the-badge)](https://github.com/project-oak/oak/actions/workflows/ci.yaml?query=branch%3Amain)
[![Docs](https://img.shields.io/badge/docs-rust-brightgreen?style=for-the-badge)](https://project-oak.github.io/oak)

The goal of Project Oak is to provide infrastructure to transfer, store and
process sensitive user data in a secure and transparent way.

To do so, Oak relies on running a _Trusted Application_ in a
[Trusted Execution Environment (TEE)](https://en.wikipedia.org/wiki/Trusted_execution_environment).
An example of a Trusted Application is
[Oak Functions](/oak_functions/README.md). The Trusted Application can provide
the client cryptographically attested evidence of the executable state of the
TEE through [Remote Attestation](./docs/remote-attestation.md). Together with
[Transparent Release](https://github.com/project-oak/transparent-release) this
binds the open-source source code to the remotely attested binary running inside
the TEE. In order to feasibly review all the source code running inside the TEE,
and minimize our trusted computing base, Oak provides the following
infrastructure: [stage 0](/stage0_bin/),
[Oak Restricted Kernel](/oak_restricted_kernel/) and controlled communications
interfaces, i.e., the [Oak Comms Channel](/oak_channel/) and
[microRPC](/micro_rpc/).

## Parties involved

- **Trusted Application Authors**: The authors writing the Trusted Application
  running on Oak Infrastructure.
- **Oak Infrastructure Authors**: The authors of the code in this repository;
  mostly this corresponds to the Project Oak team, but also any contributors,
  and, by extension, the authors of third party dependencies used in Oak.
- **Platform Provider**: The entity in charge of maintaining and running the
  combined hardware and software stack surrounding the TEE, for instance a cloud
  provider; this includes their software, hardware, and employees.
- **TEE Manufacturer**: The entity in charge of manufacturing the TEE, including
  hardware, software, and cryptographic keys.

## Threat Model

- **untrusted**:
  - most hardware (memory, disk, motherboard, network card, external devices)
  - Platform Provider
  - Host Operating System (kernel, drivers, libraries, applications)
  - Hypervisor / VMM
- **trusted-but-[transparent](https://github.com/project-oak/transparent-release)**
  - Oak Infrastructure Authors
  - Trusted Application Authors
- **trusted**:
  - TEE Manufacturer

Side channels are out of scope for Project Oak at present. While we acknowledge
that TEEs cannot defend against all possible attacks (and therefore we do need
resistance to side channels) we leave their resolution to the respective TEE
Manufacturers and other researchers.

## Getting involved

We welcome [contributors](docs/CONTRIBUTING.md)! To join our community, we
recommend joining the
[mailing list](https://groups.google.com/g/project-oak-discuss) and the
[slack](https://join.slack.com/t/project-oak/shared_invite/zt-5hiliinq-f0fYZGwlzfH3kMrJuu3qlw).

[Oak development](docs/development.md) covers practical steps for getting a
development Oak system up and running.
