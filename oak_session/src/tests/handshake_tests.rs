// Copyright 2025 Oak Authors
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

use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};

use googletest::prelude::*;
use oak_crypto::{
    encryptor::Encryptor,
    identity_key::{IdentityKey, IdentityKeyHandle},
};
use oak_proto_rust::oak::session::v1::PlaintextMessage;

use crate::{
    config::HandshakeHandlerConfig,
    encryptors::OrderedChannelEncryptor,
    handshake::{ClientHandshakeHandler, HandshakeHandler, HandshakeType, ServerHandshakeHandler},
    ProtocolEngine,
};

#[test]
fn process_kk_handshake() {
    let initiator_identity_key: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let responder_identity_key: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let responder_public_key = responder_identity_key.get_public_key().unwrap();
    let client_handshaker = ClientHandshakeHandler::create(HandshakeHandlerConfig {
        handshake_type: HandshakeType::NoiseKK,
        self_static_private_key: Some(responder_identity_key),
        peer_static_public_key: Some(initiator_identity_key.get_public_key().unwrap()),
        session_binders: BTreeMap::new(),
    })
    .unwrap();
    let server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseKK,
            self_static_private_key: Some(initiator_identity_key),
            peer_static_public_key: Some(responder_public_key),
            session_binders: BTreeMap::new(),
        },
        false,
    );
    do_handshake(client_handshaker, server_handshaker);
}

#[test]
fn process_nk_handshake() {
    let identity_key = Box::new(IdentityKey::generate());
    let client_handshaker = ClientHandshakeHandler::create(HandshakeHandlerConfig {
        handshake_type: HandshakeType::NoiseNK,
        self_static_private_key: None,
        peer_static_public_key: Some(identity_key.get_public_key().unwrap()),
        session_binders: BTreeMap::new(),
    })
    .unwrap();
    let server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNK,
            self_static_private_key: Some(identity_key),
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        false,
    );
    do_handshake(client_handshaker, server_handshaker);
}

#[test]
fn process_nn_handshake() {
    let client_handshaker = ClientHandshakeHandler::create(HandshakeHandlerConfig {
        handshake_type: HandshakeType::NoiseNN,
        self_static_private_key: None,
        peer_static_public_key: None,
        session_binders: BTreeMap::new(),
    })
    .unwrap();
    let server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        false,
    );
    do_handshake(client_handshaker, server_handshaker);
}

fn do_handshake(
    mut client_handshaker: ClientHandshakeHandler,
    mut server_handshaker: ServerHandshakeHandler,
) {
    let request = client_handshaker.get_outgoing_message().unwrap().unwrap();
    server_handshaker
        .put_incoming_message(request)
        .expect("Failed to process the incoming message from the client");
    let response = server_handshaker.get_outgoing_message().unwrap().unwrap();
    client_handshaker
        .put_incoming_message(response)
        .expect("Failed to process the response from the server");
    if let Some(followup) = client_handshaker.get_outgoing_message().unwrap() {
        server_handshaker
            .put_incoming_message(followup)
            .expect("Failed to process the follow up from the client");
    }
    let session_keys_client = client_handshaker.take_session_keys().unwrap();
    let session_keys_server = server_handshaker.take_session_keys().unwrap();
    assert_that!(session_keys_client.request_key, eq(&session_keys_server.response_key));
    assert_that!(session_keys_server.request_key, eq(&session_keys_client.response_key));

    let mut encryptor_client: OrderedChannelEncryptor = session_keys_client.try_into().unwrap();
    let mut encryptor_server: OrderedChannelEncryptor = session_keys_server.try_into().unwrap();

    for message in test_messages() {
        let ciphertext = encryptor_client.encrypt(message.clone().into()).unwrap();
        let plaintext: PlaintextMessage = encryptor_server.decrypt(ciphertext).unwrap().into();
        assert_that!(message, eq(&plaintext));
    }

    for message in test_messages() {
        let ciphertext = encryptor_server.encrypt(message.clone().into()).unwrap();
        let plaintext: PlaintextMessage = encryptor_client.decrypt(ciphertext).unwrap().into();
        assert_that!(message, eq(&plaintext));
    }
}
fn test_messages() -> Vec<PlaintextMessage> {
    vec![
        PlaintextMessage { plaintext: vec![1u8, 2u8, 3u8, 4u8] },
        PlaintextMessage { plaintext: vec![4u8, 3u8, 2u8, 1u8] },
        PlaintextMessage { plaintext: vec![] },
    ]
}
