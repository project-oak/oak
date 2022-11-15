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

pub mod rekor;

use anyhow::Context;

#[cfg(test)]
mod tests;

pub struct Client {
    inner: oak_remote_attestation_noninteractive::client::OakClient,
}

impl Client {
    pub async fn new(uri: &str) -> anyhow::Result<Self> {
        let inner = oak_remote_attestation_noninteractive::client::OakClient::create(uri)
            .await
            .context("couldn't create Oak Functions client")?;
        Ok(Client { inner })
    }

    pub async fn invoke(&mut self, request: &[u8]) -> anyhow::Result<Vec<u8>> {
        // TODO(#3442): Fetch enclave public key.
        // TODO(#3442): Encrypt request.
        let response = self
            .inner
            .message(request)
            .await
            .context("error invoking Oak Functions instance")?;
        // TODO(#3442): Decrypt response.
        Ok(response)
    }
}
