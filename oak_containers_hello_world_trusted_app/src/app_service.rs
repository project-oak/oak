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

use crate::proto::oak::containers::example::{
    trusted_application_server::{TrustedApplication, TrustedApplicationServer},
    HelloRequest, HelloResponse,
};
use anyhow::anyhow;
use oak_containers_sdk::EncryptionKeyHandle;
use oak_crypto::encryptor::AsyncServerEncryptor;
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

struct TrustedApplicationImplementation {
    application_config: Vec<u8>,
    encryption_key_handle: EncryptionKeyHandle,
}

impl TrustedApplicationImplementation {
    pub fn new(application_config: Vec<u8>, encryption_key_handle: EncryptionKeyHandle) -> Self {
        Self {
            application_config,
            encryption_key_handle,
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

        let mut server_encryptor = AsyncServerEncryptor::new(&self.encryption_key_handle);

        // Associated data is ignored.
        let (name_bytes, _) =
            server_encryptor
                .decrypt(&encrypted_request)
                .await
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
    application_config: Vec<u8>,
    encryption_key_handle: EncryptionKeyHandle,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(TrustedApplicationServer::new(
            TrustedApplicationImplementation::new(application_config, encryption_key_handle),
        ))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
