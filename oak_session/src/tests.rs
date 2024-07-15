// Copyright 2024 Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use oak_crypto::identity_key::{IdentityKey, IdentityKeyHandle};

use crate::{
    config::HandshakerConfig,
    handshake::{ClientHandshaker, HandshakeType, Handshaker, ServerHandshaker},
    ProtocolEngine,
};

#[test]
fn process_nk_handshake() {
    let identity_key = IdentityKey::generate();
    let client_handshaker = ClientHandshaker::create(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNK,
        self_static_private_key: None,
        peer_static_public_key: Some(identity_key.get_public_key().unwrap()),
        peer_attestation_binding_public_key: None,
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNK,
        self_static_private_key: Some(&identity_key),
        peer_static_public_key: None,
        peer_attestation_binding_public_key: None,
    });
    do_handshake(client_handshaker, server_handshaker);
}

#[test]
fn process_nn_handshake() {
    let client_handshaker = ClientHandshaker::create(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNN,
        self_static_private_key: None,
        peer_static_public_key: None,
        peer_attestation_binding_public_key: None,
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNN,
        self_static_private_key: None,
        peer_static_public_key: None,
        peer_attestation_binding_public_key: None,
    });
    do_handshake(client_handshaker, server_handshaker);
}

fn do_handshake(mut client_handshaker: ClientHandshaker, mut server_handshaker: ServerHandshaker) {
    let request = client_handshaker.get_outgoing_message().unwrap().unwrap();
    server_handshaker
        .put_incoming_message(&request)
        .expect("Failed to process the server incoming message");
    let response = server_handshaker.get_outgoing_message().unwrap().unwrap();
    client_handshaker
        .put_incoming_message(&response)
        .expect("Failed to process the client incoming message");
    let session_keys_client = client_handshaker.derive_session_keys().unwrap();
    let session_keys_server = server_handshaker.derive_session_keys().unwrap();
    assert_eq!(session_keys_client.request_key, session_keys_server.response_key);
    assert_eq!(session_keys_server.request_key, session_keys_client.response_key);
}
