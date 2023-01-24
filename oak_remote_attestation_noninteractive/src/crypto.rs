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

use crate::proto::{CryptoRequest, CryptoResponse};
use anyhow::{anyhow, Context};
use prost::Message;
use tink_core::keyset::Handle;
use tink_hybrid::init;

pub(crate) static HYBRID_ENCRYPTION_SCHEME: fn() -> tink_proto::KeyTemplate =
    tink_hybrid::ecies_hkdf_aes128_gcm_key_template;
pub(crate) static SYMMETRIC_ENCRYPTION_SCHEME: fn() -> tink_proto::KeyTemplate =
    tink_aead::aes128_gcm_key_template;

/// Context info value for encryption and decryption.
/// 
/// The value should be the same for both encryption and decryption to ensure
/// the correct decryption of a ciphertext:
/// https://docs.rs/tink-core/0.2.4/tink_core/trait.HybridDecrypt.html#security-guarantees
pub(crate) const HYBRID_ENCRYPTION_CONTEXT_INFO: &[u8] = b"Oak Non-Interactive Attestation v0.1";

pub struct ClientCryptoProvider {
    enclave_public_key: Handle,
}

impl ClientCryptoProvider {
    pub fn create(serialized_enclave_public_key: &[u8]) -> anyhow::Result<Self> {
        let enclave_public_key = deserialize_public_key(serialized_enclave_public_key)
            .map_err(|error| anyhow!("couldn't deserialize enclave public key: {}", error))?;
        Ok(Self { enclave_public_key })
    }

    pub fn get_encryptor(&self) -> anyhow::Result<ClientEncryptor> {
        ClientEncryptor::create(&self.enclave_public_key)
            .map_err(|error| anyhow!("couldn't create client encryptor: {}", error))
    }
}

pub struct ClientEncryptor<'a> {
    enclave_public_key: &'a Handle,
    response_key: Handle,
}

impl<'a> ClientEncryptor<'a> {
    pub fn create(enclave_public_key: &'a Handle) -> anyhow::Result<Self> {
        let response_key = tink_core::keyset::Handle::new(
            &SYMMETRIC_ENCRYPTION_SCHEME()
        ).map_err(|error| anyhow!("couldn't create response key: {}", error))?;
        Ok(Self { enclave_public_key, response_key })
    }

    pub fn encrypt(self, message: &[u8]) -> anyhow::Result<(Vec<u8>, ClientDecryptor)> {
        let encryptor = tink_hybrid::new_encrypt(&self.enclave_public_key)
            .map_err(|error| anyhow!("couldn't create hybrid encryptor: {}", error))?;

        let serialized_response_key = serialize_public_key(&self.response_key)
            .map_err(|error| anyhow!("couldn't serialize response key: {}", error))?;
        let request = CryptoRequest {
            body: message.to_vec(),
            response_key: serialized_response_key,
        };
        let mut serialized_request = vec![];
        request
            .encode(&mut serialized_request)
            .map_err(|error| anyhow!("couldn't serialize request: {}", error))?;

        let encrypted_request = encryptor
            .encrypt(&serialized_request, HYBRID_ENCRYPTION_CONTEXT_INFO)
            .map_err(|error| anyhow!("couldn't encrypt request: {}", error))?;
        let decryptor = ClientDecryptor::new(self.response_key);

        Ok((encrypted_request, decryptor))
    }
}

pub struct ClientDecryptor {
    /// Symmetric key ... used to decrypt the response.
    response_key: Handle,
}

impl ClientDecryptor {
    fn new(response_key: Handle) -> Self {
        Self { response_key }
    }

    fn decrypt(self, encrypted_message: &[u8]) -> anyhow::Result<Vec<u8>> {
        let decryptor = tink_aead::new(&self.response_key)
            .map_err(|error| anyhow!("couldn't create AEAD decryptor: {}", error))?;

        // We don't specify any additional authenticated data.
        let additional_data = vec![];
        let serialized_response = decryptor
            .decrypt(&encrypted_message, &additional_data)
            .map_err(|error| anyhow!("couldn't decrypt response: {}", error))?;
    
        let response = CryptoResponse::decode(serialized_response.as_ref())
            .context("couldn't deserialize response")?;
    
        Ok(response.body)
    }
}

pub struct EnclaveCryptoProvider {
    private_key: Handle,
}

impl EnclaveCryptoProvider {
    pub fn create() -> anyhow::Result<Self> {
        let private_key = tink_core::keyset::Handle::new(
            &HYBRID_ENCRYPTION_SCHEME()
        ).map_err(|error| anyhow!("couldn't create enclave private key: {}", error))?;
        Ok(Self { private_key })
    }

    pub fn get_public_key(&self) -> anyhow::Result<Vec<u8>> {
        let public_key = self
            .private_key
            .public()
            .map_err(|error| anyhow!("couldn't get enclave public key: {}", error))?;
        serialize_public_key(&public_key)
    }

    pub fn get_decryptor(&self) -> EnclaveDecryptor {
        EnclaveDecryptor::new(&self.private_key)
    }
}

pub struct EnclaveDecryptor<'a> {
    private_key: &'a Handle,
}

impl<'a> EnclaveDecryptor<'a> {
    pub fn new(private_key: &'a Handle) -> Self {
        Self { private_key }
    }

    pub fn decrypt(self, encrypted_message: &[u8]) -> anyhow::Result<(Vec<u8>, EnclaveEncryptor)> {
        let decryptor = tink_hybrid::new_decrypt(&self.private_key)
            .map_err(|error| anyhow!("couldn't create hybrid decryptor: {}", error))?;

        let serialized_request = decryptor
            .decrypt(&encrypted_message, HYBRID_ENCRYPTION_CONTEXT_INFO)
            .map_err(|error| anyhow!("couldn't decrypt request: {}", error))?;

        let request = CryptoRequest::decode(serialized_request.as_ref())
            .context("couldn't deserialize request")?;
        let response_key = deserialize_public_key(&request.response_key)
            .map_err(|error| anyhow!("couldn't deserialize response key: {}", error))?;
        let encryptor = EnclaveEncryptor::new(response_key);
        
        Ok((request.body, encryptor))
    }
}

pub struct EnclaveEncryptor {
    response_key: Handle,
}

impl EnclaveEncryptor {
    pub fn new(response_key: Handle) -> Self {
        Self { response_key }
    }

    pub fn encrypt(self, message: &[u8]) -> anyhow::Result<Vec<u8>> {
        let encryptor = tink_aead::new(&self.response_key)
            .map_err(|error| anyhow!("couldn't create AEAD encryptor: {}", error))?;

        let response = CryptoResponse {
            body: message.to_vec(),
        };
        let mut serialized_response = vec![];
        response
            .encode(&mut serialized_response)
            .map_err(|error| anyhow!("couldn't serialize response: {}", error))?;

        // We don't specify any additional authenticated data.
        let additional_data = vec![];
        let encrypted_response = encryptor
            .encrypt(&serialized_response, &additional_data)
            .map_err(|error| anyhow!("couldn't encrypt response: {}", error))?;
    
        Ok(encrypted_response)
    }
}

/// Serialises the handle's underlying keyset containing the public key to a binary representation.
///
/// Serialisation will fail if the handle's keyset contains any secret data.
pub(crate) fn serialize_public_key(public_key_handle: &Handle) -> anyhow::Result<Vec<u8>> {
    let mut result = Vec::new();
    let mut writer = tink_core::keyset::BinaryWriter::new(&mut result);
    public_key_handle
        .write_with_no_secrets(&mut writer)
        .map_err(|error| anyhow!("couldn't deserialise public key: {}", error))?;
    Ok(result)
}

/// Deserialises the binary data into a keyset containing the public key and returns the associated
/// handle.
pub(crate) fn deserialize_public_key(serialized_public_key: &[u8]) -> anyhow::Result<Handle> {
    let mut reader = tink_core::keyset::BinaryReader::new(serialized_public_key);
    Handle::read_with_no_secrets(&mut reader)
        .map_err(|error| anyhow!("couldn't deserialise public key: {}", error))
}

// pub(crate) fn serialize_symmetric_key(symmetric_key_handle: &Handle) -> anyhow::Result<Vec<u8>> {
//     let mut result = Vec::new();
//     let mut writer = tink_core::keyset::BinaryWriter::new(&mut result);
//     symmetric_key_handle
//         .write(&mut writer)
//         .map_err(|error| anyhow!("couldn't deserialise symmetric key: {}", error))?;
//     Ok(result)
// }

// pub(crate) fn deserialize_symmetric_key(serialized_symmetric_key: &[u8]) -> anyhow::Result<Handle> {
//     let mut reader = tink_core::keyset::BinaryReader::new(serialized_symmetric_key);
//     Handle::read(&mut reader)
//         .map_err(|error| anyhow!("couldn't deserialise symmetric key: {}", error))
// }
