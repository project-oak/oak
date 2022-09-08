# Remote Attestation

A crucial advantage of a Trusted Execution Environment (TEE) is the ability to
perform **Remote Attestation**. It allows software to remotely check the TEE
platform authenticity and also provides the remote software with the information
about the code running inside the TEE. And if the code of the application is
**reproducibly buildable**, the software can check that the TEE platform is
running the application that is expected to run.

One of the main components used in the remote attestation process is an
**Attestation Report**, which is a data structure signed by the TEE platform and
containing information identifying the code that is running inside the TEE. This
report can be checked to confirm that it is signed by the **TEE Provider** (e.g.
AMD or Intel), which results in evidence that the code is running on a genuine
TEE platform.

## Overview

The Remote Attestation protocol is implemented as a simplification of the
[Enclave Key Exchange Protocol (EKEP)](https://asylo.dev/docs/concepts/ekep.html)
handshake protocol.

The Remote Attestation protocol works on top of the [gRPC](https://grpc.io/)
protocol and consists of 2 stages:

1. Handshake
   - Server proves its identity by sending a cryptographically signed
     Attestation Report
   - Both Client and Server establish an encrypted connection with keys that are
     bound to the TEE platform's firmware
1. Data Exchange
   - The keys generated during the Handshake are used to encrypt data sent
     between Client and Server

Prior to the _Handshake_ both Client and Server each generate an individual
[ECDSA-P256](https://datatracker.ietf.org/doc/html/rfc6979) key pair called
**Signing Key Pair**. These keys are persistent between connections (but
regenerated at startup) and are used to sign **Transcripts**: hashes of previous
handshake messages that are sent in each new handshake message to prevent
[Replay Attacks](https://en.wikipedia.org/wiki/Replay_attack). Each handshake
message also includes a random string so that transcripts always contain new
random values.

Also for each individual connection both Client and Server each generate an
[X25519](https://datatracker.ietf.org/doc/html/rfc7748) Diffie-Hellman key pair
called **Ephemeral Key Pair**. These keys are used to establish a shared secret
between Client and Server.

The shared secret is used to generate 2 shared
[AES-256-GCM](https://datatracker.ietf.org/doc/html/rfc5288) **Session Keys**
that are used during the _Data Exchange_ stage:

- Server Session Key
  - Which is used to encrypt messages sent by the Server
- Client Session Key
  - Which is used to encrypt messages sent by the Client

It's important to node that for each new request **Client** performs the Remote
Attestation from the start in order to create a new pair of Session keys.

## Workflow

The workflow of the Remote Attestation protocol involves 4 interacting entities:

1. Client
   - Client application that connects to the Server
   - Client is provided with a TEE Provider's Root key
2. Untrusted Launcher
   - Companion of the Trusted Runtime
   - Runs directly on the server host
3. Trusted Runtime
   - Runs inside a secure VM on the server
   - Communicates with the outside world via the Untrusted Launcher
4. TEE Platform
   - Firmware that provides a TEE support (i.e. Intel SGX or AMD-SEV-SNP capable
     CPU)
   - Possesses a firmware key
5. TEE Provider
   - TEE platform provider that can confirm authenticity of the TEE Platform
     firmware keys using its root key
   - Client must have the TEE Provider's root public key
   - It’s important to note that the TEE Provider is an external server (i.e.
     belongs to Intel or AMD)

The complete workflow of the Remote Attestation protocol looks as follows:

### Pre-handshake

1. **TEE Provider** creates a signature of the **TEE Platform**'s firmware
   public key
2. **Untrusted Launcher** instructs the **TEE Platform** to start the **Trusted
   Runtime** in a secure VM
3. **TEE Platform** stores a cryptographic measurement of the **Trusted
   Runtime** at launch
4. Both **Client** and **Trusted Runtime** generate an individual
   [ECDSA-P256](https://datatracker.ietf.org/doc/html/rfc6979) _Signing_ key
   pair
5. **Trusted Runtime** requests a `AttestationReport` from the **TEE Platform**
   and includes the hash of its Signing public key in the request
   - **TEE Platform** includes the cryptographic measurement of the **Trusted
     Runtime** at launch in the `AttestationReport`
   - **TEE Platform** includes the supplied hash of the **Trusted Runtime**’s
     _Signing_ public key in the `AttestationReport`
   - **TEE Platform** signs the `AttestationReport` with its firmware private
     key
6. **Trusted Runtime** receives the `AttestationReport` and stores it
7. **Untrusted Launcher** sends an initial configuration message to the
   **Trusted Runtime**, which then initializes

### Handshake

1. **Client** generates an
   [X25519](https://datatracker.ietf.org/doc/html/rfc7748) _Ephemeral_ key pair
2. **Client** sends a `ClientHello` message to the **Trusted Runtime**
   - Which includes a random string
3. **Trusted Runtime** generates an
   [X25519](https://datatracker.ietf.org/doc/html/rfc7748) _Ephemeral_ key pair
4. **Trusted Runtime** sends `ServerIdentity` to the **Client** which contains:
   - **Trusted Runtime**’s _Ephemeral_ public key
   - New random string
   - _Transcript_: [SHA-256](https://datatracker.ietf.org/doc/html/rfc6234) hash
     of the concatenated `ClientHello` and current `ServerIdentity` (excluding
     the _Transcript_) signed with the **Trusted Runtime**'s _Signing_ private
     key
   - **Trusted Runtime**’s _Signing_ public key
   - `AttestationReport` signed by the **TEE Platform**'s hardware key, which
     includes a hash of the **Trusted Runtime**’s _Signing_ public key
   - Corresponding **TEE Provider**’s certificate that is signed by the **TEE
     Provider**’s _Root_ key
5. **Client** validates `ServerIdentity`
   - If the corresponding `AttestationReport` is not valid, then the **Client**
     closes the connection and aborts the protocol
6. **Client** sends `ClientIdentity` to the **Trusted Runtime** which contains:
   - **Client**’s _Ephemeral_ public key
   - _Transcript_: [SHA-256](https://datatracker.ietf.org/doc/html/rfc6234) hash
     of the concatenated `ClientHello`, `ServerIdentity` and current
     `ClientIdentity` (excluding the _Transcript_) signed with the **Client**'s
     _Signing_ private key
   - **Client**’s _Signing_ public key
7. **Client** and **Trusted Runtime** use both _Ephemeral_ public keys to create
   an [X25519](https://datatracker.ietf.org/doc/html/rfc7748) _Shared Secret_
8. **Client** and **Trusted Runtime** derive _Session_ keys from the _Shared
   Secret_ and both _Ephemeral_ public keys using a _Key Derivation Function_
   ([HKDF](https://datatracker.ietf.org/doc/html/rfc5869))
   - Each side generates 2
     [AES-256-GCM](https://datatracker.ietf.org/doc/html/rfc5288) _Session_
     keys:
     - Server Session Key
     - Client Session Key
   - **Client** and **Trusted Runtime** use Authenticated Encryption/Decryption
     ([AEAD](https://en.wikipedia.org/wiki/Authenticated_encryption)) for
     communication

### Post-handshake

**Client** and **Trusted Runtime** use generated _Session_ keys to exchange
data.

## Workflow Diagram

```mermaid
sequenceDiagram
  participant Client
  participant Untrusted Launcher
  participant Trusted Runtime
  participant TEE Platform

  Note over Untrusted Launcher,TEE Platform: Load the Trusted Runtime

  Untrusted Launcher->>TEE Platform: Trusted Runtime Memory Contents
  TEE Platform -->> TEE Platform: Store a measurement of the Trusted Runtime
  TEE Platform ->> Trusted Runtime: Start the Trusted Runtime in a secure VM

  Trusted Runtime-->>Trusted Runtime: Generate a Signing key pair
  Trusted Runtime-->>Trusted Runtime: Put Signing public key hash in the AttestationReport request
  Trusted Runtime->>TEE Platform: AttestationReport request
  TEE Platform-->>TEE Platform: Generate AttestationReport
  TEE Platform->>Trusted Runtime: Signed AttestationReport

  Note over Untrusted Launcher,Trusted Runtime: Initialization

  Untrusted Launcher->>Trusted Runtime: Configuration and business logic

  Client-->>Client: Generate a Signing key pair

  Note over Client,Trusted Runtime: Handshake Start

  Client-->>Client: Generate an Ephemeral key pair
  Client->>Untrusted Launcher: ClientHello
  Untrusted Launcher->>Trusted Runtime: ClientHello
  Trusted Runtime-->>Trusted Runtime: Generate an Ephemeral key pair

  Trusted Runtime->>Untrusted Launcher: ServerIdentity
  Untrusted Launcher->>Client: ServerIdentity
  Client-->>Client: Validate ServerIdentity

  Client->>Untrusted Launcher: ClientIdentity
  Untrusted Launcher->>Trusted Runtime: ClientIdentity

  Client-->>Client: Derive Session Keys
  Trusted Runtime-->>Trusted Runtime: Derive Session Keys
  Note over Client,Trusted Runtime: Handshake Completed


loop Data Exchange
  Client->>Untrusted Launcher: Encrypted request
  Untrusted Launcher->>Trusted Runtime: Encrypted request
  Trusted Runtime-->>Trusted Runtime: Invoke business logic
  Trusted Runtime->>Untrusted Launcher: Encrypted response
  Untrusted Launcher->>Client: Encrypted response
end
```
