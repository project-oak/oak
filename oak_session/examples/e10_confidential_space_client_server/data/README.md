# Test Data for Confidential Space Example

This directory contains keys and tokens used for the Confidential Space
client/server example.

## ⚠️ Security Warning

**DO NOT USE THESE ARTIFACTS OUTSIDE OF THIS EXAMPLE.**

The private keys and tokens in this directory are for testing and demonstration
purposes only. They are checked into a public repository and provide no
security. They **MUST NOT** be used in any production environment.

## File Descriptions

### `endorsement.jwt`

This is a sample endorsement JWT (JSON Web Token) that would be issued by Google
Cloud for a workload running in Confidential Space. In a real-world scenario,
this token is fetched from the instance metadata server and serves as
attestation evidence for the client.

This sample JWT is signed by the private key corresponding to
`c_space_root.pem`.

### `binding_key.pem`

This file contains a sample private key used by the server to sign data during
the secure session handshake (a process called session binding). In a real
deployment, this key would be generated within the Trusted Execution Environment
(TEE) and never leave it.

In a real-world attestation flow, the corresponding public key would be embedded
within the `endorsement.jwt` to cryptographically bind the server's identity to
the attestation evidence.

### `c_space_root.pem`

This is a sample X.509 root certificate. In this example, it represents the root
of trust for Confidential Space. The client uses this certificate to verify the
signature on the `endorsement.jwt`.

In a real-world scenario, the client would be configured with Google's official
production root certificate for Confidential Space.
