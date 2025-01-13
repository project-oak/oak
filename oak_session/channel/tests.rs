//
// Copyright 2025 The Project Oak Authors
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

use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, ServerSession, Session,
};
use oak_session_channel::OakSessionChannel;
use oak_session_channel_testing::test_transport;

#[tokio::test]
async fn channel_session_nn_succeeds() {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut server_session = ServerSession::create(server_config).unwrap();

    // Handshake
    let handshake_request = client_session
        .get_outgoing_message()
        .expect("failed to get handshake message")
        .expect("no handshake request");
    server_session
        .put_incoming_message(&handshake_request)
        .expect("failed to put handshake request");
    let handshake_response = server_session
        .get_outgoing_message()
        .expect("failed handshake response")
        .expect("no handshake response");
    client_session
        .put_incoming_message(&handshake_response)
        .expect("failed to put handshake_response");
    assert!(client_session.is_open());
    assert!(server_session.is_open());

    let (transport, mut mock_server_verification) = test_transport(server_session);
    let mut channel = OakSessionChannel::create(Box::new(transport), Box::new(client_session));

    let client_message = b"hello server".to_vec();
    channel.send(&client_message).await.expect("failed to send");
    assert_eq!(vec![client_message], mock_server_verification.get_received_messages());

    let server_message = b"hello client";
    mock_server_verification.add_message_to_send(server_message.to_vec());
    assert_eq!(server_message, channel.receive().await.expect("failed to receive").as_slice());
}
