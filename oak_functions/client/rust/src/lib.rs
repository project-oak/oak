//
// Copyright 2021 The Project Oak Authors
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

pub mod proto {
    #![allow(clippy::return_self_not_must_use)]
    tonic::include_proto!("oak.session.stream.v1");
}

pub mod attestation;
pub mod rekor;

use crate::attestation::{into_server_identity_verifier, ConfigurationVerifier};
use anyhow::{Context, Error, Result};
use async_trait::async_trait;
use grpc_streaming_attestation::client::AttestationClient as StreamingAttestationClient;
use grpc_unary_attestation::client::AttestationClient as UnaryAttestationClient;
use oak_functions_abi::proto::{Request, Response};
use prost::Message;

#[cfg(test)]
mod tests;

// TODO(#1867): Add remote attestation support.
const TEE_MEASUREMENT: &[u8] = br"Test TEE measurement";

#[async_trait]
pub trait Session {
    async fn invoke(&mut self, request: Request) -> anyhow::Result<Response>;
}

// Shared response handling logic for clients.
fn handle_response(response: Result<Option<Vec<u8>>, Error>) -> anyhow::Result<Response> {
    response
        .context("Error invoking Oak Functions instance")?
        .ok_or_else(|| anyhow::anyhow!("Empty response"))
        .and_then(|rsp| Response::decode(rsp.as_ref()).context("Could not decode the response"))
}

pub struct Client {
    inner: StreamingAttestationClient,
}

impl Client {
    pub async fn new(uri: &str, verifier: ConfigurationVerifier) -> anyhow::Result<Self> {
        let inner = StreamingAttestationClient::create(
            uri,
            TEE_MEASUREMENT,
            into_server_identity_verifier(verifier),
        )
        .await
        .context("Could not create Oak Functions client")?;
        Ok(Client { inner })
    }
}

#[async_trait]
impl Session for Client {
    async fn invoke(&mut self, request: Request) -> anyhow::Result<Response> {
        handle_response(self.inner.send(request).await)
    }
}

pub struct UnaryClient {
    inner: UnaryAttestationClient,
}

impl UnaryClient {
    pub async fn new(uri: &str, verifier: ConfigurationVerifier) -> anyhow::Result<Self> {
        let inner = UnaryAttestationClient::create(
            uri,
            TEE_MEASUREMENT,
            into_server_identity_verifier(verifier),
        )
        .await
        .context("Could not create Oak Functions client")?;
        Ok(UnaryClient { inner })
    }
}

#[async_trait]
impl Session for UnaryClient {
    async fn invoke(&mut self, request: Request) -> anyhow::Result<Response> {
        handle_response(self.inner.send(request).await)
    }
}
