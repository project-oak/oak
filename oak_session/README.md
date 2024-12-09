<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Encrypted Session SDK

This library provides an implementation of Oak end-to-end encrypted attested
session between the communicating parties, e.g., between Oak enclaves and user
devices or other Oak enclaves. This session is implemented using the
[Noise Protocol Framework](https://noiseprotocol.org/noise.html) in combination
with remote attestation. It offers features such as bidirectional attestation,
streaming sessions, and endorsement/evidence client-side caching.

## Design

The SDK comprises two interacting parties: the Client (initiator) and the Server
(responder). The core component is a `Session` object that manages the handshake
process and facilitates message encryption/decryption upon successful handshake
completion. The `Session` object functions as a state machine, offering `read`
and `write` functions for data messages and
`put_incoming_message`/`get_outgoing_message` functions for protocol messages
that can be passed to the transport layer.

The underlying implementation involves the `AttestationProvider` and
`Handshaker` objects, which manage attestation and produce the session
encryption key, respectively. The newly created session is bound to the supplied
attested evidence using the handshake transcript hash and the public key that is
included in the evidence by `SessionBinder` and then verified by the
`SessionBindingVerifier`. Only after the bindings are verified the session
becomes open and ready for communication. Once that happens, the `Encryptor`
object handles the encryption and decryption of application messages.

To sum it up, the steps to establish the communication channel are:

- Exchange of the attested evidence and its verification
- Noise Protocol handshake
- Binding the session handshake transcript to the attested evidence
- Session is open for secure communication

## Key Features

- **Attestation Verification:** The library retains attestation verification for
  authentication, establishing the responder's identity and optionally the
  initiator's identity through attestation. Attestation can be hardware rooted
  or be based on some trusted certification authority.
- **Noise Handshake:** We rely on the Noise protocol framework to perform the
  handshake and establish a secure communication channel between parties. A
  number of [Noise Patterns](https://noiseexplorer.com/patterns/) are supported.
- **Attestation-to-Handshake Binding:** Each party signs the handshake
  transcript hash with the application keyset to bind the attestation to the
  session.
- **Support for unreliable transport:** The implementation can be adapted to
  handle unstable connections (e.g., UDP) by incorporating sequence numbers,
  nonce customization, and message duplication prevention mechanisms.

## Getting Started

To use this library, follow these steps:

- Create a `Config` object specifying the desired features of the session
  - Pick the attestation type (Unidirectional or Bidirectional)
  - Add attesters and attestation verifiers
  - Pick the desired Noise handshake pattern
- Use the configuration to create a `Session` object (`ClientSession` for the
  initiator of the connection, `ServerSession` for the responder)
- Use `get_outgoing_message` and `put_incoming_message` to exchange the attested
  evidence and handshake messages until the session becomes open
- Once `is_open` becomes true, the session is ready for use. You can use `read`
  and `write` for plaintext messages and exchange the encrypted messages
  returned by `get_outgoing_message` over the transport layer.

## Customizations

### Support for static pre-exchanged keys

If one or both parties posess a static key where the public component is known
by its peer (perhaps through the use of PKI), it is possible to use it in the
handshake by picking a Noise NK or KK scheme.

### Support for custome encryptors

The default `OrderedChannelEncryptor` includes consecutive nonces in the
encrypted messages and so protects from replay, reorder and packet drop attacks.
This presumes that the order of the messages is preserved by the communication
channel. To support use cases where this is infeasible we allow picking a
different encryptor or implementing your own. It is important in this case that
the user of the SDK implements alternative measures to protect from network
attacks.

### Support for attestation caching

While the primitives that we provide assume that attestation will be exchanged
and verified separately for each established session, it is possible to optimize
this step by implementing your own `AttestationVerifier` and, optionally,
`Attester` to cache the accepted attestation.
