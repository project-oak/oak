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

mod proto {
    tonic::include_proto!("oak.functions.server");
}

use anyhow::Context;
use oak_functions_abi::proto::Response;
use oak_grpc_attestation_client::AttestationClient;
use prost::Message;

pub struct Client {
    inner: AttestationClient,
}

impl Client {
    pub async fn new(uri: &str) -> anyhow::Result<Self> {
        let inner = AttestationClient::create(uri, br"Test TEE measurement")
            .await
            .context("Could not create Oak Functions client")?;
        Ok(Client { inner })
    }
    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Response> {
        let response = self
            .inner
            .send(request_body)
            .await
            .context("Error invoking Oak Functions instance")?;
        response
            .ok_or_else(|| anyhow::anyhow!("Empty response"))
            .and_then(|rsp| Response::decode(rsp.as_ref()).context("Could not decode the response"))
    }
}
