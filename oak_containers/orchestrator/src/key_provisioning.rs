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

use oak_attestation_verification::verifier::verify_dice_chain_and_extract_evidence;
use oak_containers_attestation::GroupKeys;
use oak_grpc::oak::key_provisioning::v1::key_provisioning_server::{
    KeyProvisioning, KeyProvisioningServer,
};
use oak_proto_rust::oak::key_provisioning::v1::{
    GetGroupKeysRequest, GetGroupKeysResponse, GroupKeys as GroupKeysProto,
};
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;
use tokio_util::sync::CancellationToken;
use tonic::{Request, Response, transport::Server};

struct KeyProvisioningService {
    group_keys: Arc<GroupKeys>,
}

impl KeyProvisioningService {
    pub fn new(group_keys: Arc<GroupKeys>) -> Self {
        Self { group_keys }
    }
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningService {
    async fn get_group_keys(
        &self,
        request: Request<GetGroupKeysRequest>,
    ) -> Result<Response<GetGroupKeysResponse>, tonic::Status> {
        let request = request.into_inner();

        // Verify attestation evidence and get encryption public key, which will be used
        // to encrypt group keys.
        let evidence = request
            .evidence
            .ok_or(tonic::Status::invalid_argument("request message doesn't contain evidence"))?;
        let _endorsements = request.endorsements.ok_or(tonic::Status::invalid_argument(
            "request message doesn't contain endorsements",
        ))?;
        // TODO(#4442): Provide reference values by the hostlib and use `verify`
        // function.
        let attestation_results =
            verify_dice_chain_and_extract_evidence(&evidence).map_err(|err| {
                tonic::Status::invalid_argument(format!("couldn't verify endorsed evidence: {err}"))
            })?;

        // Encrypt group keys.
        let encrypted_encryption_private_key = self
            .group_keys
            .encrypted_group_encryption_key(&attestation_results.encryption_public_key)
            .map_err(|err| {
                tonic::Status::internal(format!("couldn't encrypt encryption private key: {err}"))
            })?;
        Ok(tonic::Response::new(GetGroupKeysResponse {
            group_keys: Some(GroupKeysProto {
                encrypted_encryption_private_key: Some(encrypted_encryption_private_key),
            }),
        }))
    }
}

pub async fn create(
    address: &str,
    group_keys: Arc<GroupKeys>,
    cancellation_token: CancellationToken,
) -> Result<(), anyhow::Error> {
    let key_provisioning_service_instance = KeyProvisioningService::new(group_keys);

    let listener = TcpListener::bind(address).await?;

    Server::builder()
        .add_service(KeyProvisioningServer::new(key_provisioning_service_instance))
        .serve_with_incoming_shutdown(
            TcpListenerStream::new(listener),
            cancellation_token.cancelled(),
        )
        .await?;

    Ok(())
}
