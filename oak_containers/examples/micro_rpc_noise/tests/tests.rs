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

use anyhow::Context;
use micro_rpc_noise_rust_proto::oak::containers::example::{
    TrustedApplicationClient, TrustedApplicationServer,
};
use micro_rpc_noise_service::TrustedApplicationService;
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    Session,
};

#[test]
fn basic_request_test() {
    let mut micro_rpc_client = TrustedApplicationClient::new(TrustedApplicationServer::new(
        TrustedApplicationService::new(),
    ));

    let mut client_session = oak_session::ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("failed to initialize client session");

    client_session.init_session(&mut micro_rpc_client).expect("Failed to init session");
    let encrypted_request =
        client_session.encrypt_request(b"Micro RPC Noise Test").expect("Failed to encrypt request");
    let encrypted_response = micro_rpc_client
        .oak_session(&encrypted_request)
        .expect("Failed to send request via microRPC")
        .expect("Empty response");
    let response =
        client_session.decrypt_response(&encrypted_response).expect("Failed to decrypt response");
    assert_eq!(response, b"Hello from application, Micro RPC Noise Test!");
}

/// These session helpers should eventually move into the SDK.
trait ClientSessionHelper {
    fn encrypt_request(&mut self, request: &[u8]) -> anyhow::Result<SessionRequest>;
    fn decrypt_response(&mut self, session_response: &SessionResponse) -> anyhow::Result<Vec<u8>>;
    fn init_session<T: micro_rpc::Transport>(
        &mut self,
        client: &mut TrustedApplicationClient<T>,
    ) -> anyhow::Result<()>
    where
        <T as micro_rpc::Transport>::Error: std::fmt::Debug;
}

impl ClientSessionHelper for oak_session::ClientSession {
    fn encrypt_request(&mut self, request: &[u8]) -> anyhow::Result<SessionRequest> {
        self.write(PlaintextMessage { plaintext: request.to_vec() })
            .context("couldn't write message to encrypt")?;

        self.get_outgoing_message()
            .context("error getting encrypted request")?
            .ok_or_else(|| anyhow::anyhow!("no encrypted request"))
    }

    fn decrypt_response(&mut self, session_response: &SessionResponse) -> anyhow::Result<Vec<u8>> {
        self.put_incoming_message(session_response)
            .context("failed to put response for decryption")?;

        self.read()
            .context("error reading decrypted response")?
            .ok_or_else(|| anyhow::anyhow!("no encrypted response"))
            .map(|p| p.plaintext)
    }

    fn init_session<T: micro_rpc::Transport>(
        &mut self,
        client: &mut TrustedApplicationClient<T>,
    ) -> anyhow::Result<()>
    where
        <T as micro_rpc::Transport>::Error: std::fmt::Debug,
    {
        let init_request =
            self.get_outgoing_message().context("error getting init_message")?.ok_or_else(
                || anyhow::anyhow!("no init message provided, but session not initialized"),
            )?;

        let init_response =
            client.oak_session(&init_request).expect("failed to send initialization request")?;

        self.put_incoming_message(&init_response)
            .context("error putting init_response response")?;

        anyhow::ensure!(self.is_open());
        Ok(())
    }
}
