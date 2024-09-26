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

use anyhow::{Context, Result};
use oak_grpc::oak::containers::orchestrator_client::OrchestratorClient as GrpcOrchestratorClient;
use oak_proto_rust::oak::session::v1::EndorsedEvidence;
use tonic::transport::{Endpoint, Uri};
use tower::service_fn;

// Unix Domain Sockets do not use URIs, hence this URI will never be used.
// It is defined purely since in order to create a channel, since a URI has to
// be supplied to create an `Endpoint`. Even though in this case the endpoint
// is technically a file, tonic expects us to provide our own connector, and
// this ignored endpoint. :(
static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

// Path used to facilitate inter-process communication between the orchestrator
// and the trusted application.
const IPC_SOCKET: &str = "/oak_utils/orchestrator_ipc";

/// Trait defining the interface for interacting with the Orchestrator.
/// This trait can be implemented by the real Orchestrator or mocked for testing
/// purposes.
#[async_trait::async_trait]
pub trait OrchestratorInterface {
    /// Retrieves the application configuration from the Orchestrator.
    /// This configuration contains settings and parameters specific to the
    /// application.
    async fn get_application_config(&mut self) -> Result<Vec<u8>>;

    /// Notifies the Orchestrator that the application is ready to receive
    /// requests. This should be called after the application has completed
    /// its initialization.
    async fn notify_app_ready(&mut self) -> Result<()>;

    /// Retrieves the endorsed evidence from the Orchestrator.
    /// This evidence is used to prove the authenticity and integrity of the
    /// application.
    async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence>;
}

/// Utility struct used to interface with the Orchestrator.
#[derive(Clone)]
pub struct OrchestratorClient {
    inner: GrpcOrchestratorClient<tonic::transport::channel::Channel>,
}

#[async_trait::async_trait]
impl OrchestratorInterface for OrchestratorClient {
    async fn get_application_config(&mut self) -> Result<Vec<u8>> {
        let config = self.inner.get_application_config(()).await?.into_inner().config;
        Ok(config)
    }

    async fn notify_app_ready(&mut self) -> Result<()> {
        self.inner.notify_app_ready(tonic::Request::new(())).await?;
        Ok(())
    }

    async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence> {
        Ok(self.inner.get_endorsed_evidence(()).await?.into_inner())
    }
}

// New functionality should be added to the OrchestratorInterface trait, not
// here.
impl OrchestratorClient {
    pub async fn create() -> Result<Self> {
        let inner: GrpcOrchestratorClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::try_from(IGNORED_ENDPOINT_URI)
                .context("couldn't form endpoint")?
                .connect_with_connector(service_fn(move |_: Uri| {
                    tokio::net::UnixStream::connect(IPC_SOCKET)
                }))
                .await
                .context("couldn't connect to UDS socket")?;

            GrpcOrchestratorClient::new(channel)
        };
        Ok(Self { inner })
    }

    #[deprecated(
        note = "This method has been moved to the [`OrchestratorInterface`] trait, which [`OrchestratorClient`] implements. Temporarily it will continue to be exposed as plain methods for backwards compatibility. This will change in future updates."
    )]
    pub async fn get_application_config(&mut self) -> Result<Vec<u8>> {
        <Self as OrchestratorInterface>::get_application_config(self).await
    }

    #[deprecated(
        note = "This method has been moved to the [`OrchestratorInterface`] trait, which [`OrchestratorClient`] implements. Temporarily it will continue to be exposed as plain methods for backwards compatibility. This will change in future updates."
    )]
    pub async fn notify_app_ready(&mut self) -> Result<()> {
        <Self as OrchestratorInterface>::notify_app_ready(self).await
    }

    #[deprecated(
        note = "This method has been moved to the [`OrchestratorInterface`] trait, which [`OrchestratorClient`] implements. Temporarily it will continue to be exposed as plain methods for backwards compatibility. This will change in future updates."
    )]
    pub async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence> {
        <Self as OrchestratorInterface>::get_endorsed_evidence(self).await
    }
}
