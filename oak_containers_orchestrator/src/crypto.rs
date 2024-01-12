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

use std::sync::Arc;

use anyhow::{anyhow, Context};
use hpke::{kem::X25519HkdfSha256, Deserializable, Kem};
use oak_crypto::encryptor::{EncryptionKeyProvider, RecipientContextGenerator, ServerEncryptor};
use tonic::{Request, Response};

use crate::proto::oak::{
    containers::v1::{
        orchestrator_crypto_server::OrchestratorCrypto, DeriveSessionKeysRequest,
        DeriveSessionKeysResponse, KeyOrigin,
    },
    key_provisioning::v1::GroupKeys,
};

/// An implementation of the Key Store without group keys.
pub struct InstanceKeyStore {
    // TODO(#4507): Remove `Arc` once the key is no longer required by the `Attester`.
    instance_encryption_key: Arc<EncryptionKeyProvider>,
}

impl Default for InstanceKeyStore {
    fn default() -> Self {
        Self::new()
    }
}

impl InstanceKeyStore {
    pub fn new() -> Self {
        Self {
            instance_encryption_key: Arc::new(EncryptionKeyProvider::generate()),
        }
    }

    pub fn instance_encryption_key(&self) -> Arc<EncryptionKeyProvider> {
        // TODO(#4442): Currently we have to give the encryption key provider to the `ipc_server`.
        // Once we move all enclave apps to the new crypto service and update the `Attester` to not
        // have the private key - this function should be removed.
        self.instance_encryption_key.clone()
    }

    pub fn instance_encryption_public_key(&self) -> Vec<u8> {
        self.instance_encryption_key.get_serialized_public_key()
    }

    pub fn generate_group_keys(self) -> KeyStore {
        KeyStore {
            instance_encryption_key: self.instance_encryption_key,
            group_encryption_key: EncryptionKeyProvider::generate(),
        }
    }

    pub fn provide_group_keys(self, group_keys: GroupKeys) -> anyhow::Result<KeyStore> {
        // Create server encryptor for decrypting the group keys received from the leader enclave.
        let encrypted_encryption_private_key = group_keys
            .encrypted_encryption_private_key
            .context("encrypted encryption key wasn't provided")?;
        let encapsulated_public_key = encrypted_encryption_private_key
            .serialized_encapsulated_public_key
            .as_ref()
            .context("encapsulated public key wasn't provided")?;
        let mut server_encryptor = ServerEncryptor::create(
            encapsulated_public_key,
            self.instance_encryption_key.clone(),
        )
        .context("couldn't create server encryptor")?;

        // Decrypt group keys.
        let (decrypted_encryption_private_key, _) = server_encryptor
            .decrypt(&encrypted_encryption_private_key)
            .context("couldn't decrypt the encryption private key")?;

        // Parse private key and derive public key.
        // TODO(#4513): We shouldn't store the public key, only the private key.
        let encryption_private_key =
            <X25519HkdfSha256 as Kem>::PrivateKey::from_bytes(&decrypted_encryption_private_key)
                .map_err(|err| anyhow!("couldn't deserialize private key: {:?}", err))?;
        let encryption_public_key = X25519HkdfSha256::sk_to_pk(&encryption_private_key);
        let group_encryption_key =
            EncryptionKeyProvider::new(encryption_private_key, encryption_public_key);

        // Add group keys to the Orchestrator key store.
        Ok(KeyStore {
            instance_encryption_key: self.instance_encryption_key,
            group_encryption_key,
        })
    }
}

/// An implementation of the Key Store with initialized group keys.
pub struct KeyStore {
    // TODO(#4507): Remove `Arc` once the key is no longer required by the `Attester`.
    instance_encryption_key: Arc<EncryptionKeyProvider>,
    group_encryption_key: EncryptionKeyProvider,
}

impl KeyStore {
    pub fn instance_encryption_key(&self) -> Arc<EncryptionKeyProvider> {
        // TODO(#4442): Currently we have to give the encryption key provider to the `ipc_server`.
        // Once we move all enclave apps to the new crypto service and update the `Attester` to not
        // have the private key - this function should be removed.
        self.instance_encryption_key.clone()
    }
}

pub(crate) struct CryptoService {
    key_store: Arc<KeyStore>,
}

impl CryptoService {
    pub(crate) fn new(key_store: Arc<KeyStore>) -> Self {
        Self { key_store }
    }
}

#[tonic::async_trait]
impl OrchestratorCrypto for CryptoService {
    async fn derive_session_keys(
        &self,
        request: Request<DeriveSessionKeysRequest>,
    ) -> Result<Response<DeriveSessionKeysResponse>, tonic::Status> {
        let request = request.into_inner();

        let encryption_key = match request.key_origin() {
            KeyOrigin::Unspecified => {
                Err(tonic::Status::invalid_argument("unspecified key origin"))?
            }
            KeyOrigin::Instance => &self.key_store.instance_encryption_key,
            KeyOrigin::Group => &self.key_store.group_encryption_key,
        };

        let context = encryption_key
            .generate_recipient_context(&request.serialized_encapsulated_public_key)
            .map_err(|err| tonic::Status::internal(format!("couldn't derive session keys: {err}")))?
            .serialize()
            .map_err(|err| {
                tonic::Status::internal(format!("couldn't serialize session keys: {err}"))
            })?;
        Ok(tonic::Response::new(DeriveSessionKeysResponse {
            context: Some(context),
        }))
    }
}
