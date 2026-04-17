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

use micro_rpc_noise_rust_proto::oak::containers::example::{
    TrustedApplicationClient, TrustedApplicationServer,
};
use micro_rpc_noise_service::TrustedApplicationService;
use oak_session::{
    Session,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
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

    while !client_session.is_open() {
        let request = client_session.next_init_message().expect("expected client init message");
        let response = micro_rpc_client
            .oak_session(&request)
            .expect("failed to get message")
            .expect("failure from service");
        client_session.handle_init_message(response).expect("failed to handle init response");
    }

    let encrypted_request =
        client_session.encrypt(b"Micro RPC Noise Test").expect("Failed to encrypt request");
    let encrypted_response = micro_rpc_client
        .oak_session(&encrypted_request)
        .expect("Failed to send request via microRPC")
        .expect("Empty response");
    let response = client_session.decrypt(encrypted_response).expect("Failed to decrypt response");
    assert_eq!(response, b"Hello from application, Micro RPC Noise Test!");
}
