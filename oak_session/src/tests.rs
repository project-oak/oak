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

use alloc::boxed::Box;

use oak_crypto::{
    encryptor::Encryptor,
    identity_key::{IdentityKey, IdentityKeyHandle},
};
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};

use crate::{
    attestation::AttestationType,
    config::{HandshakerConfig, SessionConfig},
    encryptors::OrderedChannelEncryptor,
    handshake::{ClientHandshaker, HandshakeType, Handshaker, ServerHandshaker},
    ClientSession, ProtocolEngine, ServerSession, Session,
};

const TEST_MESSAGES: &[&[u8]] = &[&[1u8, 2u8, 3u8, 4u8], &[4u8, 3u8, 2u8, 1u8], &[]];

#[test]
fn process_nk_handshake() {
    let identity_key = Box::new(IdentityKey::generate());
    let client_handshaker = ClientHandshaker::create(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNK,
        self_static_private_key: None,
        peer_static_public_key: Some(identity_key.get_public_key().unwrap()),
        peer_attestation_binding_public_key: None,
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNK,
        self_static_private_key: Some(identity_key),
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

    let mut encryptor_client: OrderedChannelEncryptor = session_keys_client.try_into().unwrap();
    let mut encryptor_server: OrderedChannelEncryptor = session_keys_server.try_into().unwrap();

    for &message in TEST_MESSAGES {
        let ciphertext = encryptor_client.encrypt(message.into()).unwrap();
        let plaintext = encryptor_server.decrypt(ciphertext.as_slice().into()).unwrap();
        assert_eq!(message, &plaintext);
        assert_eq!(message, &plaintext);
    }

    for &message in TEST_MESSAGES {
        let ciphertext = encryptor_server.encrypt(message.into()).unwrap();
        let plaintext = encryptor_client.decrypt(ciphertext.as_slice().into()).unwrap();
        assert_eq!(message, &plaintext);
    }
}

#[test]
fn session_nn_succeeds() {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut server_session = ServerSession::new(server_config);
    do_session_handshake(&mut client_session, &mut server_session);

    for &message in TEST_MESSAGES {
        verify_session_message(&mut client_session, &mut server_session, message);
        verify_session_message(&mut server_session, &mut client_session, message);
    }
}

#[test]
fn session_nk_succeeds() {
    let identity_key = Box::new(IdentityKey::generate());
    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_peer_static_public_key(identity_key.get_public_key().unwrap().as_slice())
        .build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_private_key(identity_key)
        .build();
    let mut server_session = ServerSession::new(server_config);
    do_session_handshake(&mut client_session, &mut server_session);

    for &message in TEST_MESSAGES {
        verify_session_message(&mut client_session, &mut server_session, message);
        verify_session_message(&mut server_session, &mut client_session, message);
    }
}
#[test]
#[should_panic]
fn session_nk_key_mismatch() {
    let identity_key1 = Box::new(IdentityKey::generate());
    let identity_key2 = Box::new(IdentityKey::generate());
    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_peer_static_public_key(identity_key1.get_public_key().unwrap().as_slice())
        .build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_private_key(identity_key2)
        .build();
    let mut server_session = ServerSession::new(server_config);
    do_session_handshake(&mut client_session, &mut server_session);
}

fn do_session_handshake(client_session: &mut ClientSession, server_session: &mut ServerSession) {
    while !client_session.is_open() {
        let request = client_session.get_outgoing_message().unwrap().unwrap();
        assert!(server_session.put_incoming_message(&request).is_ok());
        let response = server_session.get_outgoing_message().unwrap().unwrap();
        assert!(client_session.put_incoming_message(&response).is_ok());
    }
    assert!(server_session.is_open());
}

trait ProtocolSession<I, O>: Session + ProtocolEngine<I, O> {}

impl ProtocolSession<SessionResponse, SessionRequest> for ClientSession {}
impl ProtocolSession<SessionRequest, SessionResponse> for ServerSession {}

fn verify_session_message<I, O>(
    session1: &mut dyn ProtocolSession<I, O>,
    session2: &mut dyn ProtocolSession<O, I>,
    message: &[u8],
) {
    assert!(session1.write(message).is_ok());
    let outgoing_message = session1.get_outgoing_message().unwrap().unwrap();
    assert!(session2.put_incoming_message(&outgoing_message).is_ok());
    assert_eq!(message, session2.read().unwrap().unwrap());
}
