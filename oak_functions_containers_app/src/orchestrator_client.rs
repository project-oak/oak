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

use crate::proto::oak::containers::{
    orchestrator_client::OrchestratorClient as GrpcOrchestratorClient, GetCryptoContextRequest,
};
use anyhow::Context;
use async_trait::async_trait;
use oak_crypto::{
    encryptor::AsyncRecipientContextGenerator, hpke::RecipientContext,
    proto::oak::crypto::v1::CryptoContext,
};
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

/// Utility struct used to interface with the launcher
#[derive(Clone)]
pub struct OrchestratorClient {
    inner: GrpcOrchestratorClient<tonic::transport::channel::Channel>,
}

// TODO(#4478): Reuse Orchestrator client in all Oak Containers examples.
impl OrchestratorClient {
    pub async fn create() -> Result<Self, Box<dyn std::error::Error>> {
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

    pub async fn get_application_config(&mut self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let config = self
            .inner
            .get_application_config(())
            .await?
            .into_inner()
            .config;
        Ok(config)
    }

    pub async fn get_crypto_context(
        &self,
        serialized_encapsulated_public_key: &[u8],
    ) -> Result<CryptoContext, Box<dyn std::error::Error>> {
        let context = self
            .inner
            // TODO(#4477): Remove unnecessary copies of the Orchestrator client.
            .clone()
            .get_crypto_context(GetCryptoContextRequest {
                serialized_encapsulated_public_key: serialized_encapsulated_public_key.to_vec(),
            })
            .await?
            .into_inner()
            // Crypto context.
            .context
            .context("crypto context wasn't provided")?;
        Ok(context)
    }

    pub async fn notify_app_ready(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.inner.notify_app_ready(tonic::Request::new(())).await?;
        Ok(())
    }
}

#[async_trait]
impl AsyncRecipientContextGenerator for OrchestratorClient {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        let serialized_crypto_context = self
            .get_crypto_context(encapsulated_public_key)
            .await
            .map_err(|error| {
                tonic::Status::internal(format!(
                    "couldn't get crypto context from the Orchestrator: {:?}",
                    error
                ))
            })?;
        let crypto_context =
            RecipientContext::deserialize(serialized_crypto_context).map_err(|error| {
                tonic::Status::internal(format!("couldn't deserialize crypto context: {:?}", error))
            })?;
        Ok(crypto_context)
    }
}
