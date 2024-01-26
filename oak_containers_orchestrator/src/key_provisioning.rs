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


use crate::{
    crypto::KeyStore,
    proto::oak::key_provisioning::v1::{
        key_provisioning_server::KeyProvisioning, GetGroupKeysRequest, GetGroupKeysResponse,
    },
};
use oak_attestation_verification::verifier::verify;
use oak_crypto::encryptor::{EncryptionKeyProvider, ServerEncryptor};
use oak_proto_rust::oak::attestation::v1::ReferenceValues;
use std::sync::Arc;
use tonic::{Request, Response};

struct KeyProvisioningService {
    key_store: Arc<KeyStore>,
    reference_values: ReferenceValues,
}

impl KeyProvisioningService {
    pub fn new(key_store: Arc<KeyStore>) -> Self {
        Self {
            key_store,
            // TODO(#4442): Provide reference values by the hostlib.
            reference_values: ReferenceValues{},
        }
    }
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningService {
    async fn get_group_keys(
        &self,
        request: Request<GetGroupKeysRequest>,
    ) -> Result<Response<GetGroupKeysResponse>, tonic::Status> {
        let request = request.into_inner();

        // Verify attestation evidence and get encryption public key, which will be used to encrypt
        // group keys.
        let evidence = request
            .evidence
            .context("request message doesn't contain evidence")?;
        let endorsements = request
            .endorsements
            .context("request message doesn't contain endorsements")?;
        let attestation_results = verify(&evidence, &endorsements, &self.reference_values)
            .context("couldn't verify endorsed evidence")?;

        // Create server encryptor for decrypting the group keys received from the leader enclave.
        let encrypted_encryption_private_key =
            request
                .encrypted_encryption_private_key
                .ok_or(tonic::Status::invalid_argument(
                    "encrypted encryption key wasn't provided",
                ))?;
        let encapsulated_public_key = encrypted_encryption_private_key
            .serialized_encapsulated_public_key
            .as_ref()
            .ok_or(tonic::Status::invalid_argument(
                "encapsulated public key wasn't provided",
            ))?;
        let mut server_encryptor = ServerEncryptor::create(
            encapsulated_public_key,
            self.key_store.instance_encryption_key(),
        )
        .map_err(|err| {
            tonic::Status::internal(format!("couldn't create server encryptor: {err}"))
        })?;

        // Decrypt group keys.
        let (decrypted_encryption_private_key, _) = server_encryptor
            .decrypt(&encrypted_encryption_private_key)
            .map_err(|err| {
                tonic::Status::internal(format!(
                    "couldn't decrypt the encryption private key: {err}"
                ))
            })?;
        let group_encryption_key =
            EncryptionKeyProvider::from_private_key(decrypted_encryption_private_key).map_err(
                |err| tonic::Status::internal(format!("couldn't deserialize private key: {err}")),
            )?;

        // Add group keys to the Orchestrator key store.
        self.key_store
            .mutable_group_encryption_key()
            .set(group_encryption_key)
            .map_err(|_| {
                tonic::Status::internal("group encryption key was already initialized".to_string())
            })?;

        self.cancellation_token.cancel();
        Ok(tonic::Response::new(()))
    }
}
