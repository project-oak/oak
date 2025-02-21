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

use anyhow::{Context, Result};
use futures::channel::mpsc::{self, Sender};
use oak_gcp_echo_proto::oak::standalone::example::enclave_application_client::EnclaveApplicationClient;
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, Session,
};
use tonic::transport::{Channel, Uri};

// A client for streaming requests to the Echo server over an E2EE Noise
// Protocol session.
pub struct EchoClient {
    client_session: ClientSession,
    response_stream: tonic::codec::Streaming<SessionResponse>,
    tx: Sender<SessionRequest>,
}

impl EchoClient {
    pub async fn create<T: AsRef<str>>(url: T) -> Result<EchoClient> {
        let url = url.as_ref().to_owned();
        let uri = Uri::from_maybe_shared(url).context("invalid URI")?;
        let channel =
            Channel::builder(uri).connect().await.context("couldn't connect via gRPC channel")?;

        let mut client = EnclaveApplicationClient::new(channel);

        let (mut tx, rx) = mpsc::channel(10);

        let mut response_stream =
            client.oak_session(rx).await.context("couldn't send stream request")?.into_inner();

        // We don't have a noise client impl yet, so we need to manage the session
        // manually.
        // TODO: b/356389780 - Integrate Noise into the Oak Client.
        let mut client_session = ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .context("could not create client session")?;

        client_session
            .init_session(&mut tx, &mut response_stream)
            .await
            .context("failed to handshake")?;

        Ok(EchoClient { client_session, response_stream, tx })
    }

    pub async fn echo(&mut self, request: &[u8]) -> Result<Vec<u8>> {
        let request =
            self.client_session.encrypt_request(request).context("failed to encrypt message")?;

        self.tx.try_send(request).context("couldn't send request to server")?;

        let response = self
            .response_stream
            .message()
            .await
            .context("error getting response")?
            .context("didn't get any response")?;

        self.client_session.decrypt_response(&response).context("failed to decrypt response")
    }
}

// TODO: b/381533311 - Move ClientSessionHelper to client SDK.
#[async_trait::async_trait]
trait ClientSessionHelper {
    fn encrypt_request(&mut self, request: &[u8]) -> anyhow::Result<SessionRequest>;
    fn decrypt_response(&mut self, session_response: &SessionResponse) -> anyhow::Result<Vec<u8>>;
    async fn init_session(
        &mut self,
        send_request: &mut mpsc::Sender<SessionRequest>,
        receive_response: &mut tonic::Streaming<SessionResponse>,
    ) -> anyhow::Result<()>;
}

#[async_trait::async_trait]
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

    async fn init_session(
        &mut self,
        send_request: &mut mpsc::Sender<SessionRequest>,
        receive_response: &mut tonic::Streaming<SessionResponse>,
    ) -> Result<()> {
        while !self.is_open() {
            let init_request =
                self.get_outgoing_message().context("error getting init_message")?.ok_or_else(
                    || anyhow::anyhow!("no init message provided, but session not initialized"),
                )?;

            send_request.try_send(init_request).context("failed to send init request")?;

            if let Some(init_response) =
                receive_response.message().await.context("failed to receive response")?
            {
                self.put_incoming_message(&init_response)
                    .context("error putting init_response response")?;
            }
        }
        Ok(())
    }
}
