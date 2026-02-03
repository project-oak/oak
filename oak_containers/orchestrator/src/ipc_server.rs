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

use std::{fs::Permissions, os::unix::prelude::PermissionsExt, sync::Arc};

use anyhow::Context;
use oak_containers_attestation::{GroupKeys, InstanceKeys};
use oak_crypto::encryption_key::EncryptionKeyHandle;
use oak_grpc::oak::containers::{
    orchestrator_server::{Orchestrator, OrchestratorServer},
    v1::orchestrator_crypto_server::{OrchestratorCrypto, OrchestratorCryptoServer},
};
use oak_proto_rust::oak::{
    attestation::v1::{Endorsements, Evidence},
    containers::{
        GetApplicationConfigResponse,
        v1::{
            BindSessionRequest, BindSessionResponse, DeriveSessionKeysRequest,
            DeriveSessionKeysResponse, KeyOrigin, SignRequest, SignResponse,
        },
    },
    crypto::v1::Signature,
    session::v1::EndorsedEvidence,
};
use tokio::{fs::set_permissions, net::UnixListener};
use tokio_stream::wrappers::UnixListenerStream;
use tokio_util::sync::CancellationToken;
use tonic::{Request, Response, transport::Server};

use crate::launcher_client::LauncherClient;

pub struct CryptoService {
    instance_keys: InstanceKeys,
    group_keys: Arc<GroupKeys>,
}

impl CryptoService {
    pub fn new(instance_keys: InstanceKeys, group_keys: Arc<GroupKeys>) -> Self {
        Self { instance_keys, group_keys }
    }

    #[allow(clippy::result_large_err)]
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
        let signature = Signature {
            signature: <p256::ecdsa::SigningKey as oak_crypto::signer::Signer>::sign(
                signing_key,
                &request.message,
            ),
        };
        Ok(tonic::Response::new(SignResponse { signature: Some(signature) }))
    }

    async fn bind_session(
        &self,
        request: Request<BindSessionRequest>,
    ) -> Result<Response<BindSessionResponse>, tonic::Status> {
        let request = request.into_inner();
        let signature = Signature {
            signature: <p256::ecdsa::SigningKey as oak_crypto::signer::Signer>::sign(
                &self.instance_keys.session_binding_key,
                [request.transcript, request.additional_data].concat().as_slice(),
            ),
        };
        Ok(tonic::Response::new(BindSessionResponse { signature: Some(signature) }))
    }
}

pub struct ServiceImplementation {
    application_config: Vec<u8>,
    launcher_client: Arc<LauncherClient>,
    evidence: Evidence,
    endorsements: Endorsements,
}

#[tonic::async_trait]
impl Orchestrator for ServiceImplementation {
    async fn get_application_config(
        &self,
        _request: Request<()>,
    ) -> Result<Response<GetApplicationConfigResponse>, tonic::Status> {
        Ok(tonic::Response::new(GetApplicationConfigResponse {
            config: self.application_config.clone(),
        }))
    }

    async fn notify_app_ready(&self, _request: Request<()>) -> Result<Response<()>, tonic::Status> {
        self.launcher_client
            .notify_app_ready()
            .await
            .map_err(|err| tonic::Status::internal(format!("couldn't send notification: {err}")))?;
        Ok(tonic::Response::new(()))
    }

    async fn get_endorsed_evidence(
        &self,
        _request: Request<()>,
    ) -> Result<Response<EndorsedEvidence>, tonic::Status> {
        Ok(tonic::Response::new(EndorsedEvidence {
            evidence: Some(self.evidence.clone()),
            endorsements: Some(self.endorsements.clone()),
        }))
    }
}

pub async fn server<P>(
    socket_address: P,
    orchestrator_server: OrchestratorServer<ServiceImplementation>,
    crypto_server: OrchestratorCryptoServer<CryptoService>,
    cancellation_token: CancellationToken,
) -> Result<(), anyhow::Error>
where
    P: AsRef<std::path::Path> + Clone,
{
    let uds = UnixListener::bind(socket_address.clone())
        .context("could not bind to the supplied address")?;
    let uds_stream = UnixListenerStream::new(uds);
    // Change permissions on the socket to be world-RW, as otherwise processes
    // running as `oakc` can't access it. (Either that, or we should change the
    // owner of the socket to oakc.)
    set_permissions(socket_address, Permissions::from_mode(0o666)).await?;

    Server::builder()
        .add_service(orchestrator_server)
        .add_service(crypto_server)
        .serve_with_incoming_shutdown(uds_stream, cancellation_token.cancelled())
        .await?;

    Ok(())
}

pub fn create_services(
    evidence: Evidence,
    endorsements: Endorsements,
    instance_keys: InstanceKeys,
    group_keys: Arc<GroupKeys>,
    application_config: Vec<u8>,
    launcher_client: Arc<LauncherClient>,
) -> (OrchestratorServer<ServiceImplementation>, OrchestratorCryptoServer<CryptoService>) {
    let service_instance = ServiceImplementation {
        // TODO(#4442): Remove once apps use the new crypto service.
        application_config,
        launcher_client,
        evidence,
        endorsements,
    };
    let crypto_service_instance = CryptoService::new(instance_keys, group_keys);
    (
        OrchestratorServer::new(service_instance),
        OrchestratorCryptoServer::new(crypto_service_instance),
    )
}
