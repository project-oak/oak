# Oak Crypto

Foundational cryptographic primitives used throughout Project Oak for secure
communication and attestation.

## Overview

This crate provides a collection of cryptographic tools designed for use in both
`std` and `no_std` environments. It primarily focuses on:

- **Bidirectional Hybrid Public Key Encryption (HPKE)**: Implementation of RFC
  9180 for secure, authenticated communication between clients and enclaves.
- **Signing and Verification**: Generic traits (`Signer`, `Verifier`) and
  implementations for standard digital signature schemes like ECDSA.
- **Identity and Encryption Keys**: Management of asymmetric key pairs used for
  enclave identity and data encryption.
- **Noise Handshake**: Components for building secure communication channels
  based on the Noise Protocol Framework.

## Key Components

- `ClientEncryptor` and `ServerEncryptor`: Used to establish an encrypted
  session using HPKE.
- `Signer` trait: An interface for signing data, implemented by types like
  `IdentityKey`.
- `hpke`: Module containing the low-level HPKE implementation.

## Usage Example

```rust
// Establishing an HPKE session
// See src/encryptor.rs for the full ClientEncryptor and ServerEncryptor implementation.
let (client_encryptor, server_encryptor) = ...;
let encrypted_message = client_encryptor.encrypt(&payload, &associated_data)?;
let decrypted_payload = server_encryptor.decrypt(&encrypted_message)?;
```
