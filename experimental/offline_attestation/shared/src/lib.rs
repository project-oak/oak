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

//! Shared components used by both the client and server for offline attestation.

use anyhow::anyhow;
use serde::{Deserialize, Serialize};
pub use tink_core::keyset::Handle;
pub use tink_hybrid::init;

const ENCRYPTION_CONTEXT: &[u8] = b"Offline Attestation v0.1";

/// An encrypted request sent from the client to the server.
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EncryptedRequest {
    /// The encrypted payload.
    ///
    /// Contains the raw output from Tink hybrid encryption.
    pub ciphertext: Vec<u8>,

    /// The public key that should be used for encrypting the response.
    ///
    /// Contains the binary-serialised form of the Tink keyset representing the public key.
    pub response_public_key: Vec<u8>,
}

impl EncryptedRequest {
    /// Deserialises the `response_public_key` as a keyset handle.
    pub fn get_public_key_handle(&self) -> anyhow::Result<Handle> {
        deserialize_public_key(&self.response_public_key)
    }
}

/// An encrypted response sent from the server to the client.
#[derive(Deserialize, Serialize)]
pub struct EncryptedResponse {
    /// The encrypted payload.
    ///
    /// Contains the raw output from Tink hybrid encryption.
    pub ciphertext: Vec<u8>,
}

/// Placeholder for an attestation report.
pub struct AttestationReport {}

/// Information about the public key that should be used for encrypting requests.
#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PublicKeyInfo {
    /// The public key that should be used for encrypting requests.
    ///
    /// Contains the binary-serialised form of the Tink keyset representing the public key.
    pub request_public_key: Vec<u8>,

    /// The binary-serialised attestation report providing evidence that the public key was
    /// generated in the enclave and that the private key will not be leaked from the enclave.
    ///
    /// In a real implementation this will include a hash of the public key to bind the key to the
    /// attestation.
    pub attestation: Vec<u8>,
}

impl PublicKeyInfo {
    /// Constructs a new `PublicKeyInfo` instance from the public key handle.
    pub fn new(
        public_key_handle: &Handle,
        attestation_report: &AttestationReport,
    ) -> anyhow::Result<Self> {
        let attestation = serialize_attestation_report(attestation_report)?;
        let request_public_key = serialize_public_key(public_key_handle)?;
        Ok(Self {
            request_public_key,
            attestation,
        })
    }

    /// Validates the attestation associated with the public key to ensure that the public key is
    /// bound to the attestation and that the expected server code is running in an appropriate
    /// enclave.
    pub fn validate(&self) -> anyhow::Result<()> {
        // In a real implementation this would check the attestation report. For now we just pretend
        // that everything is OK.
        Ok(())
    }

    /// Deserialises the `request_publlic_key` as a keyset handle.
    pub fn get_public_key_handle(&self) -> anyhow::Result<Handle> {
        deserialize_public_key(&self.request_public_key)
    }
}

/// Encrypts the clear text `data` using Tink hybrid encryption.
///
/// The `public_key_handle` must represent a public key suitable for hybrid encryption. The
/// encrypted data can only be decrypted using the correcposing private key associated with this
/// public key.
pub fn encrypt(public_key_handle: &Handle, data: &[u8]) -> anyhow::Result<Vec<u8>> {
    let encryptor = tink_hybrid::new_encrypt(public_key_handle)
        .map_err(|error| anyhow!("Couldn't create hybrid encryptor: {}", error))?;
    encryptor
        .encrypt(data, ENCRYPTION_CONTEXT)
        .map_err(|error| anyhow!("Couldn't encrypt data: {}", error))
}

/// Decrypts the provides `cyphertext` using the private key.
///
/// The `private_key_handle` must represent a private key suitable for hybrid encryption. The
/// decryption will only succeed if the ciphertext was created using the corresponding public key.
pub fn decrypt(private_key_handle: &Handle, ciphertext: &[u8]) -> anyhow::Result<Vec<u8>> {
    let decryptor = tink_hybrid::new_decrypt(private_key_handle)
        .map_err(|error| anyhow!("Couldn't create hybrid decryptor: {}", error))?;
    decryptor
        .decrypt(ciphertext, ENCRYPTION_CONTEXT)
        .map_err(|error| anyhow!("Couldn't decrypt ciphertext: {}", error))
}

/// Generates a new private key suitable for hybrid encryption and returns a handle to the
/// containing keyset.
pub fn generate_private_key() -> anyhow::Result<Handle> {
    tink_core::keyset::Handle::new(&tink_hybrid::ecies_hkdf_aes128_gcm_key_template())
        .map_err(|error| anyhow!("Couldn't create private key: {}", error))
}

/// Serialises the handle's underlying keyset containing the public key to a binary representation.
///
/// Serialisation will fail if the handle's keyset contains any secret data.
pub fn serialize_public_key(public_key_handle: &Handle) -> anyhow::Result<Vec<u8>> {
    let mut result = Vec::new();
    let mut writer = tink_core::keyset::BinaryWriter::new(&mut result);
    public_key_handle
        .write_with_no_secrets(&mut writer)
        .map_err(|error| anyhow!("Couldn't deserialise public key: {}", error))?;
    Ok(result)
}

/// Deserialises the binary data into a keyset containing the public key and returns the associated
/// handle.
pub fn deserialize_public_key(data: &[u8]) -> anyhow::Result<Handle> {
    let mut reader = tink_core::keyset::BinaryReader::new(data);
    Handle::read_with_no_secrets(&mut reader)
        .map_err(|error| anyhow!("Couldn't deserialise public key: {}", error))
}

/// Serialises the attestation report to a binary representation.
///
/// For now we just use an empty vector as a placeholder.
pub fn serialize_attestation_report(
    _attestation_report: &AttestationReport,
) -> anyhow::Result<Vec<u8>> {
    Ok(Vec::new())
}

/// Deserialises the attestation report from a binary representation.
///
/// For now we just use return the empty placeholder.
pub fn deserialize_attestation_report(_attestation: &[u8]) -> anyhow::Result<AttestationReport> {
    Ok(AttestationReport {})
}
