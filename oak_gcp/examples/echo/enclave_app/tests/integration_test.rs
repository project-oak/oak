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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use anyhow::{Context, Result};
use futures::channel::mpsc;
use oak_gcp_echo_proto::oak::standalone::example::enclave_application_client::EnclaveApplicationClient;
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    Session,
};
use tokio::net::TcpListener;
use tonic::transport::Channel;

async fn start_server() -> Result<(SocketAddr, tokio::task::JoinHandle<Result<()>>)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    Ok((
        addr,
        tokio::spawn(oak_gcp_examples_echo_enclave_app::app_service::create(
            listener,
            Box::new(oak_gcp_examples_echo_enclave_app::app::EchoHandler),
        )),
    ))
}

#[tokio::test]
async fn test_echo() {
    let (addr, _join_handle) = start_server().await.unwrap();

    let url = format!("http://{addr}");

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url)
        .context("couldn't create gRPC channel")
        .unwrap()
        .connect()
        .await
        .context("couldn't connect via gRPC channel")
        .unwrap();

    let mut client = EnclaveApplicationClient::new(channel);

    let (mut tx, rx) = mpsc::channel(10);

    let mut response_stream =
        client.oak_session(rx).await.expect("couldn't send stream request").into_inner();

    // We don't have a noise client impl yet, so we need to manage the session
    // manually.
    // TODO: b/356389780 - Integrate Noise into the Oak Client.
    let mut client_session = oak_session::ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("could not create client session");

    client_session.init_session(&mut tx, &mut response_stream).await.expect("failed to handshake");

    let request =
        client_session.encrypt_request(b"test message").expect("failed to encrypt message");

    tx.try_send(request).expect("Could not send request to server");

    let response = response_stream
        .message()
        .await
        .expect("error getting response")
        .expect("didn't get any response");

    let decrypted_response =
        client_session.decrypt_response(&response).expect("failed to decrypt response");

    assert_eq!(decrypted_response, b"test message");
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
        self.write(&PlaintextMessage { plaintext: request.to_vec() })
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
