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

// TODO(#3843): Rename `proto` to `grpc`.
pub mod proto {
    #![allow(clippy::return_self_not_must_use)]
    tonic::include_proto!("oak.session.noninteractive.v1");
}

pub mod transport;
pub mod verifier;

use crate::transport::AsyncEvidenceProvider;
use anyhow::{anyhow, Context};
use oak_crypto::{encryptor::ClientEncryptor, schema::EncryptedResponse};
use prost::Message;
use std::vec::Vec;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// Client for connecting to Oak.
/// Represents a Relying Party from the RATS Architecture:
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-relying-party>
pub struct OakClient<T>
where
    T: micro_rpc::AsyncTransport<Error = anyhow::Error>,
{
    transport: T,
    server_encryption_public_key: Vec<u8>,
}

impl<T> OakClient<T>
where
    T: micro_rpc::AsyncTransport<Error = anyhow::Error> + AsyncEvidenceProvider,
{
    pub async fn create(mut transport: T) -> anyhow::Result<Self> {
        // TODO(#3641): Implement client-side attestation verification.
        let evidence = transport
            .get_evidence()
            .await
            .context("couldn't get attestation evidence")?;
        Ok(Self {
            transport,
            server_encryption_public_key: evidence.encryption_public_key.to_vec(),
        })
    }

    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // Encrypt request.
        let mut client_encryptor = ClientEncryptor::create(&self.server_encryption_public_key)
            .context("couldn't create encryptor")?;
        let encrypted_request = client_encryptor
            .encrypt(request_body, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt request")?;

        // Serialize request.
        let mut serialized_request = vec![];
        encrypted_request
            .encode(&mut serialized_request)
            .map_err(|error| anyhow!("couldn't serialize request: {:?}", error))?;

        // Send request.
        let serialized_response = self
            .transport
            .invoke(&serialized_request)
            .await
            .map_err(|error| anyhow!("couldn't send request: {:?}", error))?;

        // Deserialize response.
        let encrypted_response = EncryptedResponse::decode(serialized_response.as_ref())
            .map_err(|error| anyhow!("couldn't deserialize response: {:?}", error))?;

        // Decrypt response.
        // Currently we ignore the associated data.
        let (response, _) = client_encryptor
            .decrypt(&encrypted_response)
            .context("client couldn't decrypt response")?;

        Ok(response)
    }
}
