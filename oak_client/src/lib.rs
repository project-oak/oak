//
// Copyright 2022 The Project Oak Authors
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

pub mod transport;
pub mod rekor;

use crate::transport::Transport;
use anyhow::Context;
use tonic::transport::Channel;

#[cfg(test)]
mod tests;

pub struct ReferenceValue {
    binary_hash: String;
}

pub struct OakClientBuilder {
    transport: Box<dyn Transport>,
    evidence_provider: Box<dyn EvidenceProvider>,
    reference_value: ReferenceValue,
}

/// ... RATS architecture:
/// https://datatracker.ietf.org/doc/html/draft-ietf-rats-architecture
impl OakClientBuilder {
    pub fn new(transport: Box<dyn Transport>,
               evidence_provider: Box<dyn EvidenceProvider>,
               reference_value: ReferenceValue,
               encryptor_provider: EncryptorProvider) -> Self {
        Self { transport, evidence_provider, reference_value }
    }

    pub fn build(self) -> anyhow::Result<OakClient> {
        let evidence = self.evidence_provider.get_evidence(self.transport)?;

        let attestation_result = self.verifier.verify(
            evidence, self.reference_value);

        if attestation_result.is_ok() {
            OakClient {
                transport: self.transport,
            }
        } else {
            Err(anyhow!(
                "Attestation verification failed: {:?}", attestation_result)
            )
        }
    }
}

pub struct OakClient {
    transport: Box<dyn Transport>, // RpcClient
    encryptor: ClientEncryptor,
}

impl OakClient {
    pub fn invoke(&self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        let (encrypted_request, decryptor) = encryptor
            .encrypt(request_body)
            .context("couldn't encrypt request")?;
        let encrypted_response = self
            .transport
            .invoke(encrypted_request)
            .context("couldn't send request")?;
        let decrypted_response = decryptor
            .decrypt(encrypted_response)
            .context("couldn't decrypt response")?;
        Ok(decrypted_response)
    }
}

pub trait EvidenceProvider {
    fn get_evidence(transport: &dyn Transport) -> anyhow::Result<Evidence>;
}

pub struct NonInteractiveEvidenceProvider {
    fn new(transport: &dyn Transport) {

    }

    fn get_evidence() -> anyhow::Result<Evidence> {

    }
}

pub trait AttestationVerifier {
    fn verify(evidence: Evidence, reference_value: ReferenceValue) -> anyhow::Result<()>;
}

pub struct NonInteractiveAttestationManager {}

impl EvidenceProvider for NonInteractiveAttestationManager {
    fn get_evidence(transport: &dyn Transport) -> anyhow::Result<Evidence> {

    }
}

fn main() {
    let channel = Channel::from_shared(uri.to_string())
        .context("couldn't create gRPC channel")?
        .connect()
        .await?;
    let transport = StreamingSessionClient::new(channel);

    let oak_client = OakClient::builder()
        .transport(transport)
        .verifier()
        .build();
}
