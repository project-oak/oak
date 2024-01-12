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
    crypto::{CryptoService, KeyStore},
    launcher_client::LauncherClient,
    proto::oak::containers::{
        orchestrator_server::{Orchestrator, OrchestratorServer},
        v1::orchestrator_crypto_server::OrchestratorCryptoServer,
        GetApplicationConfigResponse,
    },
};
use anyhow::Context;
use std::{fs::Permissions, os::unix::prelude::PermissionsExt, sync::Arc};
use tokio::{fs::set_permissions, net::UnixListener};
use tokio_stream::wrappers::UnixListenerStream;
use tokio_util::sync::CancellationToken;
use tonic::{transport::Server, Request, Response};

pub struct ServiceImplementation {
    application_config: Vec<u8>,
    launcher_client: Arc<LauncherClient>,
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
}

pub async fn create<P>(
    socket_address: P,
    key_store: Arc<KeyStore>,
    application_config: Vec<u8>,
    launcher_client: Arc<LauncherClient>,
    cancellation_token: CancellationToken,
) -> Result<(), anyhow::Error>
where
    P: AsRef<std::path::Path> + Clone,
{
    let service_instance = ServiceImplementation {
        // TODO(#4442): Remove once apps use the new crypto service.
        application_config,
        launcher_client,
    };
    let crypto_service_instance = CryptoService::new(key_store);

    let uds = UnixListener::bind(socket_address.clone())
        .context("could not bind to the supplied address")?;
    let uds_stream = UnixListenerStream::new(uds);
    // Change permissions on the socket to be world-RW, as otherwise processes running as `oakc`
    // can't access it. (Either that, or we should change the owner of the socket to oakc.)
    set_permissions(socket_address, Permissions::from_mode(0o666)).await?;

    Server::builder()
        .add_service(OrchestratorServer::new(service_instance))
        .add_service(OrchestratorCryptoServer::new(crypto_service_instance))
        .serve_with_incoming_shutdown(uds_stream, cancellation_token.cancelled())
        .await?;

    Ok(())
}
