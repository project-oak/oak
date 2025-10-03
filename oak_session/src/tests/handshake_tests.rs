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

use std::{
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use googletest::prelude::*;
use oak_crypto::{
    encryptor::Encryptor,
    identity_key::{IdentityKey, IdentityKeyHandle},
};
use oak_proto_rust::oak::{
    attestation::v1::Assertion,
    session::v1::{PlaintextMessage, SessionBinding},
};
use oak_session::{
    attestation::{AttestationState, PeerAttestationVerdict},
    config::HandshakeHandlerConfig,
    encryptors::OrderedChannelEncryptor,
    generator::{BindableAssertion, BindableAssertionGeneratorError},
    handshake::{ClientHandshakeHandler, HandshakeHandler, HandshakeType, ServerHandshakeHandler},
    ProtocolEngine,
};

#[test]
fn process_kk_handshake() {
    let initiator_identity_key: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let responder_identity_key: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let responder_public_key = responder_identity_key.get_public_key().unwrap();
    let client_handshaker = ClientHandshakeHandler::create(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseKK,
            self_static_private_key: Some(responder_identity_key),
            peer_static_public_key: Some(initiator_identity_key.get_public_key().unwrap()),
            session_binders: BTreeMap::new(),
        },
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    )
    .unwrap();
    let server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseKK,
            self_static_private_key: Some(initiator_identity_key),
            peer_static_public_key: Some(responder_public_key),
            session_binders: BTreeMap::new(),
        },
        false,
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    );
    do_handshake(client_handshaker, server_handshaker);
}

#[test]
fn process_nk_handshake() {
    let identity_key = Box::new(IdentityKey::generate());
    let client_handshaker = ClientHandshakeHandler::create(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNK,
            self_static_private_key: None,
            peer_static_public_key: Some(identity_key.get_public_key().unwrap()),
            session_binders: BTreeMap::new(),
        },
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    )
    .unwrap();
    let server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNK,
            self_static_private_key: Some(identity_key),
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        false,
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    );
    do_handshake(client_handshaker, server_handshaker);
}

#[test]
fn process_nn_handshake() {
    let client_handshaker = ClientHandshakeHandler::create(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    )
    .unwrap();
    let server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        false,
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
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
    let crypter_client = client_handshaker.take_handshake_result().unwrap().0.crypter;
    let crypter_server = server_handshaker.take_handshake_result().unwrap().0.crypter;

    let mut encryptor_client: OrderedChannelEncryptor = crypter_client.try_into().unwrap();
    let mut encryptor_server: OrderedChannelEncryptor = crypter_server.try_into().unwrap();

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

struct TestBindableAssertion {
    assertion: Assertion,
}

impl BindableAssertion for TestBindableAssertion {
    fn assertion(&self) -> &Assertion {
        &self.assertion
    }

    fn bind(
        &self,
        bound_data: &[u8],
    ) -> core::result::Result<SessionBinding, BindableAssertionGeneratorError> {
        let mut binding = b"bound:".to_vec();
        binding.extend_from_slice(&self.assertion.content);
        binding.extend_from_slice(b":");
        binding.extend_from_slice(bound_data);
        Ok(SessionBinding { binding })
    }
}

#[test]
fn client_sends_assertion_bindings() {
    let assertion_id = "ASSERTION_ID";
    let mut self_assertions: BTreeMap<String, Box<dyn BindableAssertion>> = BTreeMap::new();
    self_assertions.insert(
        assertion_id.to_string(),
        Box::new(TestBindableAssertion {
            assertion: Assertion { content: b"test assertion content".to_vec() },
        }),
    );

    let mut client_handshaker = ClientHandshakeHandler::create(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions,
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: b"attestation_binding_token".to_vec(),
        },
    )
    .unwrap();

    let mut server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        true, // Expect client binding
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: b"attestation_binding_token".to_vec(),
        },
    );

    let request = client_handshaker.get_outgoing_message().unwrap().unwrap();
    server_handshaker.put_incoming_message(request).unwrap();
    let response = server_handshaker.get_outgoing_message().unwrap().unwrap();
    client_handshaker.put_incoming_message(response).unwrap();
    let followup = client_handshaker.get_outgoing_message().unwrap().unwrap();

    assert!(followup.assertion_bindings.contains_key(assertion_id));
}

#[test]
fn server_sends_assertion_bindings() {
    let assertion_id = "test_assertion";
    let mut self_assertions: BTreeMap<String, Box<dyn BindableAssertion>> = BTreeMap::new();
    self_assertions.insert(
        assertion_id.to_string(),
        Box::new(TestBindableAssertion {
            assertion: Assertion { content: b"test assertion content".to_vec() },
        }),
    );

    let mut client_handshaker = ClientHandshakeHandler::create(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions: BTreeMap::new(),
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    )
    .unwrap();

    let mut server_handshaker = ServerHandshakeHandler::new(
        HandshakeHandlerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        false,
        AttestationState {
            peer_attestation_verdict: PeerAttestationVerdict::AttestationPassed {
                legacy_verification_results: BTreeMap::new(),
                assertion_verification_results: BTreeMap::new(),
            },
            self_assertions,
            peer_session_binding_verifiers: BTreeMap::new(),
            attestation_binding_token: Vec::new(),
        },
    );

    let request = client_handshaker.get_outgoing_message().unwrap().unwrap();
    server_handshaker.put_incoming_message(request).unwrap();
    let response = server_handshaker.get_outgoing_message().unwrap().unwrap();

    assert!(response.assertion_bindings.contains_key(assertion_id));
}
