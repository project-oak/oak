//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// Crypto primitives used by the remote attestation protocol.
//
// Should be kept in sync with the Java implementation of the remote attestation
// protocol.

// Ideally we would also have a check that enforces that at most one feature is enabled, but that
// currently does not work because we run tests with the --all-features flag, which breaks this.
#[cfg(not(any(feature = "ring-crypto", feature = "rust-crypto")))]
compile_error!("Exactly one cryptographic implementation must be specified.");

// When both implementations are selected (e.g. when testing with all features) we use the `ring`
// implementation.
#[cfg(all(feature = "rust-crypto", not(feature = "ring-crypto")))]
mod rust_crypto;

#[cfg(all(feature = "rust-crypto", not(feature = "ring-crypto")))]
pub use rust_crypto::{
    get_random, get_sha256, AeadEncryptor, KeyNegotiator, SignatureVerifier, Signer,
};

#[cfg(feature = "ring-crypto")]
mod ring_crypto;

#[cfg(feature = "ring-crypto")]
pub use ring_crypto::{
    get_random, get_sha256, AeadEncryptor, KeyNegotiator, SignatureVerifier, Signer,
};

/// Length of the encryption nonce.
/// `ring::aead` uses 96-bit (12-byte) nonces.
/// <https://briansmith.org/rustdoc/ring/aead/constant.NONCE_LEN.html>
pub const NONCE_LENGTH: usize = 12;
pub const SHA256_HASH_LENGTH: usize = 32;
pub const AEAD_ALGORITHM_KEY_LENGTH: usize = 32;
pub const KEY_AGREEMENT_ALGORITHM_KEY_LENGTH: usize = 32;
/// Salt used for key derivation with HKDF.
/// <https://datatracker.ietf.org/doc/html/rfc5869>
pub const KEY_DERIVATION_SALT: &str = "Remote Attestation Protocol v1";
/// Purpose string used for deriving server session keys with HKDF.
pub const SERVER_KEY_PURPOSE: &str = "Remote Attestation Protocol Server Session Key";
/// Purpose string used for deriving client session keys with HKDF.
pub const CLIENT_KEY_PURPOSE: &str = "Remote Attestation Protocol Client Session Key";
/// OpenSSL ECDSA-P256 key public key length, which is represented as
/// `0x04 | X: 32-byte | Y: 32-byte`.
/// Where X and Y are big-endian coordinates of an Elliptic Curve point.
/// <https://datatracker.ietf.org/doc/html/rfc6979>
pub const SIGNING_ALGORITHM_KEY_LENGTH: usize = 65;
// TODO(#2277): Use OpenSSL signature format (which is 72 bytes).
/// IEEE-P1363 encoded ECDSA-P256 signature length.
/// <https://datatracker.ietf.org/doc/html/rfc6979>
/// <https://standards.ieee.org/standard/1363-2000.html>
pub const SIGNATURE_LENGTH: usize = 64;

/// Defines the type of key negotiator and the set of session keys created by it.
#[derive(Clone)]
pub enum KeyNegotiatorType {
    /// Defines a key negotiator which provides server session key for encryption and client
    /// session key for decryption.
    Server,
    /// Defines a key negotiator which provides client session key for encryption and server
    /// session key for decryption.
    Client,
}

/// Convenience struct for passing an encryption key as an argument.
#[derive(PartialEq)]
pub(crate) struct EncryptionKey(pub(crate) [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH]);

/// Convenience struct for passing a decryption key as an argument.
#[derive(PartialEq)]
pub(crate) struct DecryptionKey(pub(crate) [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH]);
