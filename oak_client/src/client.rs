//
// Copyright 2024 The Project Oak Authors
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

use anyhow::{Context, anyhow};
use oak_crypto::encryptor::ClientEncryptor;

use crate::{
    transport::{EvidenceProvider, Transport},
    verifier::AttestationVerifier,
};

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// Client for connecting to Oak.
/// Represents a Relying Party from the RATS Architecture:
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-relying-party>
pub struct OakClient<T: Transport> {
    transport: T,
    server_encryption_public_key: Vec<u8>,
}

impl<T: Transport + EvidenceProvider> OakClient<T> {
    pub async fn create(
        mut transport: T,
        verifier: &dyn AttestationVerifier,
    ) -> anyhow::Result<Self> {
        let endorsed_evidence =
            transport.get_endorsed_evidence().await.context("couldn't get endorsed evidence")?;

        let evidence = endorsed_evidence
            .evidence
            .context("endorsed evidence message doesn't contain evidence")?;
        let endorsements = endorsed_evidence
            .endorsements
            .context("endorsed evidence message doesn't contain endorsements")?;
        let attestation_results = verifier
            .verify(&evidence, &endorsements)
            .context("couldn't verify endorsed evidence")?;

        Ok(Self {
            transport,
            server_encryption_public_key: attestation_results.encryption_public_key.to_vec(),
        })
    }

    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // Encrypt request.
        let mut client_encryptor = ClientEncryptor::create(&self.server_encryption_public_key)
            .context("couldn't create encryptor")?;
        let encrypted_request = client_encryptor
            .encrypt(request_body, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt request")?;

        // Send request.
        let encrypted_response = self
            .transport
            .invoke(&encrypted_request)
            .await
            .map_err(|error| anyhow!("couldn't send request: {:?}", error))?;

        // Decrypt response.
        // Currently we ignore the associated data.
        let (response, _) = client_encryptor
            .decrypt(&encrypted_response)
            .context("client couldn't decrypt response")?;

        Ok(response)
    }
}
