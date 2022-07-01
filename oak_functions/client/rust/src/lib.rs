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
    tonic::include_proto!("oak.session.unary.v1");
}

pub mod rekor;

use anyhow::Context;
use grpc_unary_attestation::client::AttestationClient;
use oak_functions_abi::{Request, Response};

#[cfg(test)]
mod tests;

pub struct Client {
    inner: AttestationClient,
}

impl Client {
    pub async fn new(uri: &str) -> anyhow::Result<Self> {
        let inner = AttestationClient::create(uri)
            .await
            .context("Could not create Oak Functions client")?;
        Ok(Client { inner })
    }

    pub async fn invoke(&mut self, request: Request) -> anyhow::Result<Response> {
        let encoded_response = self
            .inner
            .send(&request.body)
            .await
            .context("Error invoking Oak Functions instance")?;

        Response::decode(encoded_response.as_ref()).context("Could not decode the response")
    }
}
