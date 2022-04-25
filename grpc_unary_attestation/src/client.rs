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

use crate::proto::{unary_session_client::UnarySessionClient, UnaryRequest};
use anyhow::Context;
use oak_functions_abi;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, ClientHandshaker, Encryptor, ServerIdentityVerifier,
};
use oak_remote_attestation_sessions::SessionId;
use tonic::transport::Channel;

/// gRPC Attestation Service client implementation.
pub struct AttestationClient {
    session_id: SessionId,
    encryptor: Encryptor,
    client: UnarySessionClient<Channel>,
}

impl AttestationClient {
    pub async fn create(
        uri: &str,
        expected_tee_measurement: &[u8],
        server_verifier: ServerIdentityVerifier,
    ) -> anyhow::Result<Self> {
        let session_id: SessionId = rand::random();
        let channel = Channel::from_shared(uri.to_string())
            .context("Couldn't create gRPC channel")?
            .connect()
            .await?;
        let mut client = UnarySessionClient::new(channel);

        let mut handshaker = ClientHandshaker::new(
            AttestationBehavior::create_peer_attestation(expected_tee_measurement),
            server_verifier,
        );
        let client_hello = handshaker
            .create_client_hello()
            .context("Couldn't create client hello message")?;

        let mut response = client
            .message(UnaryRequest {
                body: client_hello,
                session_id: session_id.to_vec(),
            })
            .await
            .context("Couldn't send client hello message")?
            .into_inner();

        while !handshaker.is_completed() {
            let request = handshaker
                .next_step(&response.body)
                .context("Couldn't process handshake message")?;

            if let Some(request) = request {
                response = client
                    .message(UnaryRequest {
                        body: request,
                        session_id: session_id.to_vec(),
                    })
                    .await
                    .context("Couldn't send client hello message")?
                    .into_inner();
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
    pub async fn send(
        &mut self,
        request: oak_functions_abi::proto::Request,
    ) -> anyhow::Result<Option<Vec<u8>>> {
        let encrypted_request = self
            .encryptor
            .encrypt(&request.body)
            .context("Couldn't encrypt request")?;
        let encrypted_response = self
            .client
            .message(UnaryRequest {
                session_id: self.session_id.to_vec(),
                body: encrypted_request,
            })
            .await
            .context("Couldn't send encrypted data request")?
            .into_inner();

        let encoded_response = self
            .encryptor
            .decrypt(&encrypted_response.body)
            .context("Couldn't decrypt response")?;

        Ok(Some(encoded_response))
    }
}
