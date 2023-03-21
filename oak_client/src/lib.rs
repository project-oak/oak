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
//

pub mod proto {
    #![allow(clippy::return_self_not_must_use)]
    tonic::include_proto!("oak.session.noninteractive.v1");
}

pub mod transport;
pub mod verifier;

use anyhow::Context;
use std::vec::Vec;

/// Client for connecting to Oak.
/// Represents a Relying Party from the RATS Architecture:
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-relying-party>
pub struct OakClient<T>
where
    T: micro_rpc::AsyncTransport<Error = anyhow::Error>,
{
    transport: T,
}

impl<T> OakClient<T>
where
    T: micro_rpc::AsyncTransport<Error = anyhow::Error>,
{
    pub async fn create(transport: T) -> anyhow::Result<Self> {
        // TODO(#3442): Fetch enclave public key.
        // TODO(#3641): Implement client-side attestation verification.
        Ok(Self { transport })
    }

    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // TODO(#3767): Use hybrid encryption for messages.
        self.transport
            .invoke(request_body)
            .await
            .context("couldn't send request")
    }
}
