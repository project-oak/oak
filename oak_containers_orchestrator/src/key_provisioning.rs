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
    proto::oak::{
        containers::v1::{
            orchestrator_key_provisioning_server::{
                OrchestratorKeyProvisioning, OrchestratorKeyProvisioningServer,
            },
            UpdateGroupPrivateKeysRequest,
        },
        key_provisioning::v1::{
            key_provisioning_server::{KeyProvisioning, KeyProvisioningServer},
            GetGroupPrivateKeysRequest, GetGroupPrivateKeysResponse,
        },
    },
};
use oak_crypto::encryptor::{EncryptionKeyProvider, ServerEncryptor};
use std::{sync::Arc, net::SocketAddr};
use tokio_util::sync::CancellationToken;
use tonic::{transport::Server, Request, Response};

pub struct KeyProvisioningService {
    key_store: Arc<KeyStore>,
    // Cancellation token to tell the Key Provisioning gRPC service to stop after receiving group
    // keys. This sender will be used inside the gRPC service handler.
    cancellation_token: CancellationToken,
}

impl KeyProvisioningService {
    pub async fn start(
        listen_address: SocketAddr,
        key_store: Arc<KeyStore>,
    ) -> Result<(), anyhow::Error> {
        let cancellation_token = CancellationToken::new();
        let key_provisioning_service_instance = KeyProvisioningService {
            key_store,
            cancellation_token: cancellation_token.clone(),
        };

        Server::builder()
            .add_service(OrchestratorKeyProvisioningServer::new(
                key_provisioning_service_instance,
            ))
            .serve_with_shutdown(listen_address, cancellation_token.cancelled())
            .await?;

        Ok(())
    }
}

#[tonic::async_trait]
impl OrchestratorKeyProvisioning for KeyProvisioningService {
    async fn update_group_private_keys(
        &self,
        request: Request<UpdateGroupPrivateKeysRequest>,
    ) -> Result<Response<()>, tonic::Status> {
        let request = request.into_inner();

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

pub struct KeyProvisioningLeaderService {
    key_store: Arc<KeyStore>,
}

impl KeyProvisioningLeaderService {
    pub async fn start(
        listen_address: SocketAddr,
        key_store: Arc<KeyStore>,
        cancellation_token: CancellationToken,
    ) -> Result<(), anyhow::Error> {
        let key_provisioning_leader_service_instance = KeyProvisioningLeaderService {
            key_store,
        };

        Server::builder()
            .add_service(KeyProvisioningServer::new(
                key_provisioning_leader_service_instance,
            ))
            .serve_with_shutdown(listen_address, cancellation_token.cancelled())
            .await?;

        Ok(())
    }
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningLeaderService {
    async fn get_group_private_keys(
        &self,
        _request: Request<GetGroupPrivateKeysRequest>,
    ) -> Result<Response<GetGroupPrivateKeysResponse>, tonic::Status> {
        // TODO(#4442): Provide actual Reference Values for Key Provisioning and verify attestation.
        Err(tonic::Status::unimplemented(
            "Key Provisioning is not implemented",
        ))
    }
}
