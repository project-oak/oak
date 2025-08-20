<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Functions Standalone on Google Cloud Platform (GCP)

TODO: b/441440062 - Migrate all generic Oak Functions architecture parts to the
Oak Functions README.md

## Introduction

Welcome, developer. This README provides a comprehensive overview of the Oak
Functions standalone application. Specifically it describes its implementation
and operation on the [Google Cloud Platform](https://cloud.google.com). Unlike
the
[Oak Functions](https://github.com/project-oak/oak/blob/main/oak_functions/README.md)
flavors that run on the
[Restricted Kernel](https://github.com/project-oak/oak/blob/main/oak_restricted_kernel/README.md)
or
[Oak Containers](https://github.com/project-oak/oak/blob/main/oak_containers/README.md),
this service does not require an
[Oak Functions Launcher](https://github.com/project-oak/oak/blob/main/oak_functions_launcher/README.md)
to configure the binary's environment.

Oak Functions is designed to provide a secure, remotely attestable sandbox
environment for running stateless services. This setup leverages Trusted
Execution Environments (TEEs) to ensure that even the operator of the service
cannot access user data, offering a high degree of privacy and trust. It is
fully open-sourced, built with Rust for proper memory management and security,
and designed to be easily auditable. It provides a robust framework for
implementing use-cases that require private information retrieval by utilizing
an encrypted, in-memory, read-only database.

## Core Concepts

The Oak Functions operates on a few core concepts which we describe below.

### Trusted vs. Untrusted Code

Trusted and untrusted components are separated to maintain the integrity and
confidentiality of user data. We define _Trusted Code_ and _Untrusted Code_ as:

- _Trusted Code_: This is the core Oak Functions application logic, which is
  open-source and auditable. It handles all cryptographic operations and ensures
  that untrusted code cannot compromise user privacy. It also provides a Wasm
  sandbox for running untrusted Wasm modules.

- _Untrusted Code_: This is the custom logic in the form of a WebAssembly (Wasm)
  module. This code is executed within a secure sandbox on each client request,
  and each sandbox instance is destroyed immediately after execution.

### Architecture

Oak Functions leverages Wasm sandboxing and an in-memory database in its
architecture. The sandbox provides a limited ABI for the untrusted code in the
sandbox to interact with the surrounding, trusted environment. The untrusted
code has access to an in-memory database, referred to as "lookup data", which it
can query in a read-only manner. More information on the architecture can be
found in
[the Oak Functions README.md](https://github.com/project-oak/oak/blob/main/oak_functions/README.md).

## System Architecture and Roles

TODO: b/441440062 - Introduce 'Components' section and migrate some terminology
to it.

The architecture of the Oak Functions standalone application on GCP involves
several key roles:

- _The Author_: The development team responsible for creating and maintaining
  the open-source Oak Functions codebase (the Oak team).

- _The Operator_: The entity that deploys and runs the Oak Functions standalone
  application with their own custom Wasm logic.

- _The Client_: The application or process that interacts with the Oak Functions
  instance on behalf of a user, such as a mobile application.

- _The User_: The end-user whose data is being processed.

- _The Infrastructure Provider_: The provider of the server-side environment,
  such as Google Cloud.

- _Confidential Space_: An isolated, encrypted server-side environment offered
  by Google Cloud for operating on sensitive data. Read more on
  [Google Cloud's Confidential Space homepage](https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview).

A foundational principle of this architecture is that the client and, by
extension, the user do not need to trust the operator. Trust in the Oak
Functions standalone application is established through open-source code,
verifiable builds, and transparency logs.

## Startup and Initialization

Before the application can serve requests, it performs several initialization
tasks.

### Wasm Module Initialization

The application is designed to load the operator's untrusted Wasm logic from an
external source, which provides two key benefits:

1. It keeps the auditable, open-source logic separate from the operator's custom
   logic.

2. It ensures that the Wasm logic does not alter the container image's
   measurement, which is crucial for attestation verification.

The operator specifies the location of the Wasm module via a URL, and the
application fetches it. To ensure the integrity of the Wasm module, the operator
can provide a SHA-256 hash that the application will verify after downloading
the module. The application can be configured to use an OAuth 2.0 token for
authorized access to the Wasm module from storage systems like Google Cloud
Storage.

### Lookup Data Loading

The process for loading lookup data is similar to that of the Wasm module in
that it queried from an external source. This is to ensure that the core trusted
logic and the container image are not affected by the lookup data. This data
must be a serialized `LookupDataChunk` and is loaded into the Confidential Space
process's memory. While not a mandatory component for the application to run, it
is a key feature for many use-cases.

## Attestation and Verification

A cornerstone of the Oak Functions trust model is remote attestation. This
process allows clients to verify that they are communicating with a genuine Oak
Functions instance running in a secure environment.

### Attestation Generation

At startup, the application requests attestation evidence from the Google Cloud
environment. This evidence is provided as a
[JSON Web Token (JWT)](https://datatracker.ietf.org/doc/html/rfc7519) that
conforms to the
[OpenID Connect (OIDC) specification](https://auth0.com/docs/authenticate/protocols/openid-connect-protocol)
and is issued by Google Cloud's attestation verification service. This JWT
certifies that the application is running on Confidential Space and includes
detailed information about the workload's environment. The JWT token is also
referred to as an
[ID token](https://cloud.google.com/docs/authentication/token-types#id).

To bind this attestation to the current session (see
[Oak Session](https://github.com/project-oak/oak/blob/main/oak_session/README.md)),
the application generates an asymmetric key pair and provides a hash of the
public key as a nonce in the attestation request. This ensures that the
resulting JWT is tied to the specific cryptographic keys being used for the
client communication.

### Endorsements

The attestation evidence is bundled with endorsements that provide a chain of
trust:

- _Author Signature_: The Oak team digitally signs the application's container
  image using Cosign and stores this endorsement in the OCI registry. This
  signature certifies that the application was produced by the Oak team.

- _Transparency Log_: The endorsement is also posted to a public transparency
  log (Rekor) to protect against split-view attacks.

The application retrieves these endorsements from the OCI registry using the
container image hash found within its own attestation evidence.

### Client Verification

To establish a secure connection, a client must perform a series of verification
steps:

1. _Pre-installed Keys_: The client must have the public keys for the Oak team,
   Rekor, and
   [Google Cloud attestation verification service's X.509 certificate](https://confidentialcomputing.googleapis.com/.well-known/confidential_space_root.crt)
   pre-installed.

2. _JWT Validation_: The client validates the JWT's signature chain, ensuring it
   was issued by Google's trusted service and that the token is still valid. It
   also checks that the application is running on a production image of
   Confidential Space.

3. _Endorsement Verification_: The client verifies the signatures from the Oak
   team and Rekor within the endorsement and ensures that the container image
   digest in the JWT matches the one in the endorsement.

4. _Claim Comparison_: Finally, the client compares the claims made in the
   endorsement against a set of expected values to ensure it is communicating
   with the intended and trusted version of the application. The claims are
   expressed as URLs and are viewable in the
   [claims folder](https://github.com/project-oak/oak/tree/main/docs/tr/claim).

If any of these verification steps fail, the client must close the communication
channel to protect user privacy.

## Client Interaction

All communication with the Oak Functions standalone application must be
conducted through the
[_Oak Session API_](https://github.com/project-oak/oak/blob/main/oak_session/README.md).
This is an end-to-end encrypted protocol built on top of a bidirectional
streaming gRPC channel, allowing for secure, encrypted communication after the
initial attestation and verification are successfully completed.

## Logging

The Oak Functions standalone application generates logs that provide operational
information without compromising user privacy. Logging from the untrusted Wasm
module, however, is handled differently. Logs from the Wasm module are currently
discarded.

- TODO: b/441282383 - Allow Wasm logging on debug confidential space images.
