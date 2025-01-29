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
    ServerSession,
};
use oak_session_channel::{new_client_channel, new_server_channel};
use oak_session_channel_testing::test_transport;

#[tokio::test]
async fn client_session_channel_nn_succeeds() {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_session = ServerSession::create(server_config).unwrap();

    let (transport, mut mock_server_verification) = test_transport(server_session);
    let mut channel = new_client_channel(client_config, transport)
        .await
        .expect("Failed to create new client channel");

    let client_message = b"hello server".to_vec();
    channel.send(&client_message).await.expect("failed to send");
    assert_eq!(vec![client_message], mock_server_verification.get_received_messages());

    let server_message = b"hello client";
    mock_server_verification.add_message_to_send(server_message.to_vec());
    assert_eq!(server_message, channel.receive().await.expect("failed to receive").as_slice());
}

#[tokio::test]
async fn server_session_channel_nn_succeeds() {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let client_session = ClientSession::create(client_config).unwrap();

    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let (transport, mut mock_client_verification) = test_transport(client_session);
    let mut channel = new_server_channel(server_config, transport)
        .await
        .expect("Failed to create new client channel");

    let server_message = b"hello client".to_vec();
    channel.send(&server_message).await.expect("failed to send");
    assert_eq!(vec![server_message], mock_client_verification.get_received_messages());

    let client_message = b"hello server";
    mock_client_verification.add_message_to_send(client_message.to_vec());
    assert_eq!(client_message, channel.receive().await.expect("failed to receive").as_slice());
}
