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

use anyhow::Context;
use async_trait::async_trait;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier, ClientHandshaker, Encryptor,
};
use oak_remote_attestation_sessions::SessionId;

/// Abstract version of networking stub.
// Async trait requires the definition and all implementations to be marked as
// optionally [`Send`] if one implementation is not.
#[async_trait(?Send)]
pub trait UnaryClient {
    /// Constructs a requests, sends it over the network, and returns the result.
    async fn message(&mut self, session_id: SessionId, body: Vec<u8>) -> anyhow::Result<Vec<u8>>;
}

/// gRPC Attestation Service client implementation.
pub struct GenericAttestationClient<T: UnaryClient> {
    session_id: SessionId,
    encryptor: Encryptor,
    client: T,
}

impl<T: UnaryClient> GenericAttestationClient<T> {
    pub async fn create<G: AttestationGenerator, V: AttestationVerifier>(
        mut client: T,
        attestation_behavior: AttestationBehavior<G, V>,
    ) -> anyhow::Result<Self> {
        let session_id: SessionId = rand::random();

        let mut handshaker = ClientHandshaker::new(attestation_behavior)?;
        let client_hello = handshaker
            .create_client_hello()
            .context("Couldn't create client hello message")?;

        let mut response = client
            .message(session_id, client_hello)
            .await
            .context("Couldn't message client hello message")?;

        while !handshaker.is_completed() {
            let request = handshaker
                .next_step(&response)
                .context("Couldn't process handshake message")?;

            if let Some(request) = request {
                response = client
                    .message(session_id, request)
                    .await
                    .context("Couldn't message client hello message")?;
            }
        }

        let encryptor = handshaker
            .get_encryptor()
            .context("Couldn't get encryptor")?;

        Ok(Self {
            session_id,
            encryptor,
            client,
        })
    }

    /// Sends data encrypted by the [`Encryptor`] to the server and decrypts the server responses.
    pub async fn message(&mut self, request_as_plaintext_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let encrypted_request = self
            .encryptor
            .encrypt(request_as_plaintext_bytes)
            .context("Couldn't encrypt request")?;

        let encrypted_response = self
            .client
            .message(self.session_id, encrypted_request)
            .await
            .context("Couldn't message encrypted data request")?;

        // The runtime responds with an encrypted response that contains an
        // encoded proto containing the plaintext response and status code.
        // After decrypting we're left with the encoded proto.
        let encoded_response = self
            .encryptor
            .decrypt(&encrypted_response)
            .context("Couldn't decrypt response")?;

        Ok(encoded_response)
    }
}
