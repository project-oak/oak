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

use anyhow::Context;
use oak_crypto::{
    encryption_key::{generate_encryption_key_pair, EncryptionKey, EncryptionKeyHandle},
    encryptor::ServerEncryptor,
};
use oak_dice::cert::generate_ecdsa_key_pair;
use oak_proto_rust::oak::crypto::v1::EncryptedRequest;
use tonic::{Request, Response};

use crate::proto::oak::{
    containers::v1::{
        orchestrator_crypto_server::OrchestratorCrypto, DeriveSessionKeysRequest,
        DeriveSessionKeysResponse, KeyOrigin, SignRequest, SignResponse,
    },
    key_provisioning::v1::GroupKeys as GroupKeysProto,
};

pub fn generate_instance_keys() -> (InstanceKeys, InstancePublicKeys) {
    let (encryption_key, encryption_public_key) = generate_encryption_key_pair();
    let (signing_key, signing_public_key) = generate_ecdsa_key_pair();
    (
        InstanceKeys { encryption_key, signing_key },
        InstancePublicKeys { encryption_public_key, signing_public_key },
    )
}

pub struct InstanceKeys {
    encryption_key: EncryptionKey,
    signing_key: p256::ecdsa::SigningKey,
}

pub struct InstancePublicKeys {
    pub encryption_public_key: Vec<u8>,
    pub signing_public_key: p256::ecdsa::VerifyingKey,
}

impl InstanceKeys {
    pub fn generate_group_keys(&self) -> (GroupKeys, GroupPublicKeys) {
        let (group_encryption_key, group_encryption_public_key) = generate_encryption_key_pair();
        (
            GroupKeys { encryption_key: group_encryption_key },
            GroupPublicKeys { encryption_public_key: group_encryption_public_key },
        )
    }

    pub fn provide_group_keys(&self, group_keys: GroupKeysProto) -> anyhow::Result<GroupKeys> {
        // Create server encryptor for decrypting the group keys received from the
        // leader enclave.
        let encrypted_encryption_private_key = group_keys
            .encrypted_encryption_private_key
            .context("encrypted encryption key wasn't provided")?;

        // Decrypt group keys.
        let (_, mut decrypted_encryption_private_key, _) =
            ServerEncryptor::decrypt(&encrypted_encryption_private_key, &self.encryption_key)
                .context("couldn't decrypt the encryption private key")?;

        let group_encryption_key =
            EncryptionKey::deserialize(&mut decrypted_encryption_private_key)
                .context("couldn't deserialize private key")?;

        Ok(GroupKeys { encryption_key: group_encryption_key })
    }
}

pub struct GroupKeys {
    encryption_key: EncryptionKey,
}

pub struct GroupPublicKeys {
    pub encryption_public_key: Vec<u8>,
}

impl GroupKeys {
    /// Returns group encryption private key which was encrypted with the
    /// `peer_public_key`.
    pub fn encrypted_group_encryption_key(
        &self,
        peer_public_key: &[u8],
    ) -> anyhow::Result<EncryptedRequest> {
        self.encryption_key.encrypted_private_key(peer_public_key)
    }
}

pub(crate) struct CryptoService {
    instance_keys: InstanceKeys,
    group_keys: Arc<GroupKeys>,
}

impl CryptoService {
    pub(crate) fn new(instance_keys: InstanceKeys, group_keys: Arc<GroupKeys>) -> Self {
        Self { instance_keys, group_keys }
    }

    fn signing_key(
        &self,
        key_origin: KeyOrigin,
    ) -> Result<&p256::ecdsa::SigningKey, tonic::Status> {
        match key_origin {
            KeyOrigin::Unspecified => {
                Err(tonic::Status::invalid_argument("unspecified key origin"))?
            }
            KeyOrigin::Instance => Ok(&self.instance_keys.signing_key),
            KeyOrigin::Group =>
            // TODO(#4442): Implement with key provisioning.
            {
                Err(tonic::Status::unimplemented(
                    "signing using the group key is not yet implemented",
                ))
            }
        }
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
            KeyOrigin::Instance => &self.instance_keys.encryption_key,
            KeyOrigin::Group => &self.group_keys.encryption_key,
        };

        let session_keys = encryption_key
            .generate_recipient_context(&request.serialized_encapsulated_public_key)
            .map_err(|err| tonic::Status::internal(format!("couldn't derive session keys: {err}")))?
            .serialize()
            .map_err(|err| {
                tonic::Status::internal(format!("couldn't serialize session keys: {err}"))
            })?;
        Ok(tonic::Response::new(DeriveSessionKeysResponse { session_keys: Some(session_keys) }))
    }

    async fn sign(
        &self,
        request: Request<SignRequest>,
    ) -> Result<Response<SignResponse>, tonic::Status> {
        let request = request.into_inner();
        let signing_key = self.signing_key(request.key_origin())?;
        let signature = <p256::ecdsa::SigningKey as oak_crypto::signer::Signer>::sign(
            signing_key,
            &request.message,
        );
        Ok(tonic::Response::new(SignResponse { signature: Some(signature) }))
    }
}
