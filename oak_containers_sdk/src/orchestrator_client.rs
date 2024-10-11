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

use crate::{IGNORED_ENDPOINT_URI, IPC_SOCKET};

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
    // TODO: b/356381841 - Remove this function once all clients start using
    // the `EndorsedEvidenceProvider`.
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
        self.get_application_config().await
    }

    async fn notify_app_ready(&mut self) -> Result<()> {
        self.notify_app_ready().await
    }

    async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence> {
        self.get_endorsed_evidence().await
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

    pub async fn get_application_config(&mut self) -> Result<Vec<u8>> {
        Ok(self.inner.get_application_config(()).await?.into_inner().config)
    }

    pub async fn notify_app_ready(&mut self) -> Result<()> {
        self.inner.notify_app_ready(tonic::Request::new(())).await?;
        Ok(())
    }

    pub async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence> {
        Ok(self.inner.get_endorsed_evidence(()).await?.into_inner())
    }
}

#[tokio::test]
async fn test_trait_usage() {
    struct Fake {}

    const APP_CONFIG: &[u8] = b"app config";

    #[async_trait::async_trait]
    impl OrchestratorInterface for Fake {
        async fn get_application_config(&mut self) -> Result<Vec<u8>> {
            Ok(APP_CONFIG.to_vec())
        }

        async fn notify_app_ready(&mut self) -> Result<()> {
            Ok(())
        }

        async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence> {
            Err(anyhow::anyhow!("nah"))
        }
    }

    async fn orchestrator_stuff(mut iorch: Box<dyn OrchestratorInterface>) -> Vec<u8> {
        iorch.get_application_config().await.unwrap()
    }

    assert_eq!(orchestrator_stuff(Box::new(Fake {})).await, APP_CONFIG)
}
