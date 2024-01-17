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
use tonic::transport::{Endpoint, Uri};
use tower::service_fn;

use crate::proto::oak::containers::v1::orchestrator_client::OrchestratorClient as GrpcOrchestratorClient;

// Unix Domain Sockets do not use URIs, hence this URI will never be used.
// It is defined purely since in order to create a channel, since a URI has to
// be supplied to create an `Endpoint`. Even though in this case the endpoint
// is technically a file, tonic expects us to provide our own connector, and
// this ignored endpoint. :(
static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

// Path used to facilitate inter-process communication between the orchestrator
// and the trusted application.
const IPC_SOCKET: &str = "/oak_utils/orchestrator_ipc";

/// Utility struct used to interface with the launcher
#[derive(Clone)]
pub struct OrchestratorClient {
    inner: GrpcOrchestratorClient<tonic::transport::channel::Channel>,
}

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
        let config = self
            .inner
            .get_application_config(())
            .await?
            .into_inner()
            .config;
        Ok(config)
    }

    pub async fn notify_app_ready(&mut self) -> Result<()> {
        self.inner.notify_app_ready(tonic::Request::new(())).await?;
        Ok(())
    }
}
