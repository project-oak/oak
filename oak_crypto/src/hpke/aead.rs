//
// Copyright 2023 The Project Oak Authors
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

//! Implementation of Authenticated Encryption with Associated Data (AEAD).
//! <https://datatracker.ietf.org/doc/html/rfc5116>

use alloc::vec::Vec;

use aes_gcm::{
    Aes256Gcm, Key, KeyInit,
    aead::{Aead, Payload},
};
use anyhow::anyhow;

/// Represents `N_k` from RFC9180.
/// <https://www.rfc-editor.org/rfc/rfc9180.html#name-cryptographic-dependencies>
pub(crate) const AEAD_ALGORITHM_KEY_SIZE_BYTES: usize = 32;
/// Represents `N_n` from RFC9180.
/// <https://www.rfc-editor.org/rfc/rfc9180.html#name-cryptographic-dependencies>
pub(crate) const AEAD_NONCE_SIZE_BYTES: usize = 12;
/// Convenience type for representing an AEAD key.
pub(crate) type AeadKey = [u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
/// Convenience type for representing an AEAD nonce.
pub(crate) type AeadNonce = [u8; AEAD_NONCE_SIZE_BYTES];

/// Encrypts `plaintext` with associated data using AES-GCM encryption scheme.
/// Note: the corresponding associated data is NOT encrypted.
pub(crate) fn encrypt(
    secret_key: &AeadKey,
    nonce: &AeadNonce,
    plaintext: &[u8],
    associated_data: &[u8],
) -> anyhow::Result<Vec<u8>> {
    let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(secret_key));

    // Encrypt message.
    cipher
        .encrypt(nonce.into(), Payload { msg: plaintext, aad: associated_data })
        .map_err(|error| anyhow!("couldn't encrypt data: {}", error))
}

/// Decrypts `ciphertext` and authenticates `associated_data` using AES-GCM
/// encryption scheme.
pub(crate) fn decrypt(
    secret_key: &AeadKey,
    nonce: &AeadNonce,
    ciphertext: &[u8],
    associated_data: &[u8],
) -> anyhow::Result<Vec<u8>> {
    let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(secret_key));

    // Decrypt message.
    cipher
        .decrypt(nonce.into(), Payload { msg: ciphertext, aad: associated_data })
        .map_err(|error| anyhow!("couldn't decrypt data: {}", error))
}
