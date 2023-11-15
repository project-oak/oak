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
    orchestrator_client::OrchestratorClient,
    proto::oak::containers::example::{
        trusted_application_server::{TrustedApplication, TrustedApplicationServer},
        HelloRequest, HelloResponse,
    },
};
use anyhow::anyhow;
use oak_crypto::{encryptor::ServerEncryptor, hpke::RecipientContext};
use oak_remote_attestation::handler::AsyncEncryptionHandler;
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

struct TrustedApplicationImplementation {
    orchestrator_client: OrchestratorClient,
    application_config: Vec<u8>,
}

impl TrustedApplicationImplementation {
    pub fn new(orchestrator_client: OrchestratorClient, application_config: Vec<u8>) -> Self {
        Self {
            orchestrator_client,
            application_config,
        }
    }
}

#[tonic::async_trait]
impl TrustedApplication for TrustedApplicationImplementation {
    async fn hello(
        &self,
        request: tonic::Request<HelloRequest>,
    ) -> Result<tonic::Response<HelloResponse>, tonic::Status> {
        let encrypted_request = request
            .into_inner()
            .encrypted_request
            .ok_or(tonic::Status::internal("encrypted request wasn't provided"))?;

        // Initialize server encryptor.
        let serialized_encapsulated_public_key = encrypted_request
            .serialized_encapsulated_public_key
            .as_ref()
            .ok_or(tonic::Status::invalid_argument(
                "initial request message doesn't contain encapsulated public key",
            ))?;
        let serialized_crypto_context = self
            .orchestrator_client
            .get_crypto_context(serialized_encapsulated_public_key)
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
        let mut server_encryptor = ServerEncryptor::new(crypto_context);

        // Associated data is ignored.
        let (name_bytes, _) = server_encryptor
            .decrypt(&encrypted_request)
            .map_err(|error| {
                tonic::Status::internal(format!("couldn't decrypt request: {:?}", error))
            })?;

        let name = String::from_utf8(name_bytes)
            .map_err(|error| tonic::Status::internal(format!("name is not UTF-8: {:?}", error)))?;
        let greeting: String = format!("Hello from the trusted side, {}! Btw, the Trusted App has a config with a length of {} bytes.", name, self.application_config.len());
        let response = server_encryptor
            .encrypt(greeting.as_bytes(), EMPTY_ASSOCIATED_DATA)
            .map_err(|error| {
                tonic::Status::internal(format!("couldn't encrypt response: {:?}", error))
            })?;

        Ok(tonic::Response::new(HelloResponse {
            encrypted_response: Some(response),
        }))
    }
}

pub async fn create(
    listener: TcpListener,
    orchestrator_client: OrchestratorClient,
    application_config: Vec<u8>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(TrustedApplicationServer::new(
            TrustedApplicationImplementation::new(orchestrator_client, application_config),
        ))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
