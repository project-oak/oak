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

use alloc::{boxed::Box, collections::BTreeMap, string::String, vec::Vec};

use oak_crypto::{
    encryptor::Encryptor,
    identity_key::{IdentityKey, IdentityKeyHandle},
};
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results, AttestationResults, Endorsements, Evidence},
    session::v1::{EndorsedEvidence, PlaintextMessage, SessionRequest, SessionResponse},
};

use crate::{
    alloc::string::ToString,
    attestation::{
        AttestationProvider, AttestationType, AttestationVerifier, Attester,
        ClientAttestationProvider, DefaultAttestationAggregator, MockAttestationVerifier,
        MockAttester, ServerAttestationProvider,
    },
    config::{AttestationProviderConfig, HandshakerConfig, SessionConfig},
    encryptors::OrderedChannelEncryptor,
    handshake::{ClientHandshaker, HandshakeType, Handshaker, ServerHandshaker},
    ClientSession, ProtocolEngine, ServerSession, Session,
};

fn test_messages() -> Vec<PlaintextMessage> {
    vec![
        PlaintextMessage { plaintext: vec![1u8, 2u8, 3u8, 4u8] },
        PlaintextMessage { plaintext: vec![4u8, 3u8, 2u8, 1u8] },
        PlaintextMessage { plaintext: vec![] },
    ]
}

const MATCHED_ATTESTER_ID1: &str = "MATCHED_ATTESTER_ID1";
const MATCHED_ATTESTER_ID2: &str = "MATCHED_ATTESTER_ID2";
const UNMATCHED_ATTESTER_ID: &str = "UNMATCHED_ATTESTER_ID";
const UNMATCHED_VERIFIER_ID: &str = "UNMATCHED_VERIFIER_ID";

#[test]
fn attestation_verification_succeeds() {
    let client_config = AttestationProviderConfig {
        attestation_type: AttestationType::Bidirectional,
        self_attesters: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_mock_attester()),
            (MATCHED_ATTESTER_ID2.to_string(), create_mock_attester()),
            (UNMATCHED_ATTESTER_ID.to_string(), create_mock_attester()),
        ]),
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_passing_mock_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_passing_mock_verifier()),
        ]),
        attestation_aggregator: Box::new(DefaultAttestationAggregator {}),
    };
    let server_config = AttestationProviderConfig {
        attestation_type: AttestationType::Bidirectional,
        self_attesters: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_mock_attester()),
            (MATCHED_ATTESTER_ID2.to_string(), create_mock_attester()),
            (UNMATCHED_ATTESTER_ID.to_string(), create_mock_attester()),
        ]),
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_passing_mock_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_passing_mock_verifier()),
        ]),
        attestation_aggregator: Box::new(DefaultAttestationAggregator {}),
    };
    let mut client_attestation_provider = ClientAttestationProvider::new(client_config);
    let mut server_attestation_provider = ServerAttestationProvider::new(server_config);

    let attest_request = client_attestation_provider.get_outgoing_message();
    assert!(attest_request.is_ok());
    assert!(
        server_attestation_provider.put_incoming_message(&attest_request.unwrap().unwrap()).is_ok()
    );

    let attest_response = server_attestation_provider.get_outgoing_message();
    assert!(attest_response.is_ok());
    assert!(
        client_attestation_provider
            .put_incoming_message(&attest_response.unwrap().unwrap(),)
            .is_ok()
    );

    let client_attestation_result = client_attestation_provider.take_attestation_report().unwrap();
    assert_eq!(
        client_attestation_result.status,
        attestation_results::Status::Success.into(),
        "Client attestation verification failed: {}",
        client_attestation_result.reason
    );
    let server_attestation_result = server_attestation_provider.take_attestation_report().unwrap();
    assert_eq!(
        server_attestation_result.status,
        attestation_results::Status::Success.into(),
        "Server attestation verification failed: {}",
        server_attestation_result.reason
    );
}

#[test]
fn attestation_verification_fails() {
    let client_config = AttestationProviderConfig {
        attestation_type: AttestationType::Bidirectional,
        self_attesters: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_mock_attester()),
            (MATCHED_ATTESTER_ID2.to_string(), create_mock_attester()),
            (UNMATCHED_ATTESTER_ID.to_string(), create_mock_attester()),
        ]),
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_passing_mock_verifier()),
        ]),
        attestation_aggregator: Box::new(DefaultAttestationAggregator {}),
    };
    let server_config = AttestationProviderConfig {
        attestation_type: AttestationType::Bidirectional,
        self_attesters: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_mock_attester()),
            (MATCHED_ATTESTER_ID2.to_string(), create_mock_attester()),
            (UNMATCHED_ATTESTER_ID.to_string(), create_mock_attester()),
        ]),
        peer_verifiers: BTreeMap::from([
            (MATCHED_ATTESTER_ID1.to_string(), create_passing_mock_verifier()),
            (MATCHED_ATTESTER_ID2.to_string(), create_failing_mock_verifier()),
            (UNMATCHED_VERIFIER_ID.to_string(), create_passing_mock_verifier()),
        ]),
        attestation_aggregator: Box::new(DefaultAttestationAggregator {}),
    };
    let mut client_attestation_provider = ClientAttestationProvider::new(client_config);
    let mut server_attestation_provider = ServerAttestationProvider::new(server_config);

    let attest_request = client_attestation_provider.get_outgoing_message();
    assert!(attest_request.is_ok());
    assert!(
        server_attestation_provider.put_incoming_message(&attest_request.unwrap().unwrap()).is_ok()
    );

    let attest_response = server_attestation_provider.get_outgoing_message();
    assert!(attest_response.is_ok());
    assert!(
        client_attestation_provider
            .put_incoming_message(&attest_response.unwrap().unwrap(),)
            .is_ok()
    );

    let client_attestation_result = client_attestation_provider.take_attestation_report().unwrap();
    assert_eq!(
        client_attestation_result.status,
        attestation_results::Status::GenericFailure.into()
    );
    let server_attestation_result = server_attestation_provider.take_attestation_report().unwrap();
    assert_eq!(
        server_attestation_result.status,
        attestation_results::Status::GenericFailure.into()
    );
}

fn create_mock_attester() -> Box<dyn Attester> {
    let mut attester = MockAttester::new();
    attester.expect_get_endorsed_evidence().returning(|| {
        Ok(EndorsedEvidence {
            evidence: Some(Evidence { ..Default::default() }),
            endorsements: Some(Endorsements { ..Default::default() }),
        })
    });
    Box::new(attester)
}

fn create_passing_mock_verifier() -> Box<dyn AttestationVerifier> {
    let mut verifier = MockAttestationVerifier::new();
    verifier.expect_verify().returning(|_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            ..Default::default()
        })
    });
    Box::new(verifier)
}

fn create_failing_mock_verifier() -> Box<dyn AttestationVerifier> {
    let mut verifier = MockAttestationVerifier::new();
    verifier.expect_verify().returning(|_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::GenericFailure.into(),
            reason: String::from("Mock failure"),
            ..Default::default()
        })
    });
    Box::new(verifier)
}

#[test]
fn process_kk_handshake() {
    let initiator_identity_key: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let responder_identity_key: Box<dyn IdentityKeyHandle> = Box::new(IdentityKey::generate());
    let responder_public_key = responder_identity_key.get_public_key().unwrap();
    let client_handshaker = ClientHandshaker::create(HandshakerConfig {
        handshake_type: HandshakeType::NoiseKK,
        self_static_private_key: Some(responder_identity_key),
        peer_static_public_key: Some(initiator_identity_key.get_public_key().unwrap()),
        peer_attestation_binding_public_key: None,
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(HandshakerConfig {
        handshake_type: HandshakeType::NoiseKK,
        self_static_private_key: Some(initiator_identity_key),
        peer_static_public_key: Some(responder_public_key),
        peer_attestation_binding_public_key: None,
    });
    do_handshake(client_handshaker, server_handshaker);
}

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

    for message in test_messages() {
        let ciphertext = encryptor_client.encrypt(&message.clone().into()).unwrap();
        let plaintext = encryptor_server.decrypt(&ciphertext).unwrap();
        assert_eq!(message, plaintext.into());
    }

    for message in test_messages() {
        let ciphertext = encryptor_server.encrypt(&message.clone().into()).unwrap();
        let plaintext = encryptor_client.decrypt(&ciphertext).unwrap();
        assert_eq!(message, plaintext.into());
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

    for message in test_messages() {
        verify_session_message(&mut client_session, &mut server_session, &message);
        verify_session_message(&mut server_session, &mut client_session, &message);
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

    for message in test_messages() {
        verify_session_message(&mut client_session, &mut server_session, &message);
        verify_session_message(&mut server_session, &mut client_session, &message);
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
        server_session.put_incoming_message(&request).unwrap();
        let response = server_session.get_outgoing_message().unwrap().unwrap();
        client_session.put_incoming_message(&response).unwrap();
    }
    assert!(server_session.is_open());
}

trait ProtocolSession<I, O>: Session + ProtocolEngine<I, O> {}

impl ProtocolSession<SessionResponse, SessionRequest> for ClientSession {}
impl ProtocolSession<SessionRequest, SessionResponse> for ServerSession {}

fn verify_session_message<I, O>(
    session1: &mut dyn ProtocolSession<I, O>,
    session2: &mut dyn ProtocolSession<O, I>,
    message: &PlaintextMessage,
) {
    session1.write(message).unwrap();
    let outgoing_message = session1.get_outgoing_message().unwrap().unwrap();
    session2.put_incoming_message(&outgoing_message).unwrap();
    assert_eq!(message, &session2.read().unwrap().unwrap());
}

#[test]
fn test_session_sendable() {
    fn foo<T: Send>(_: T) {}

    fn test(s: ServerSession) {
        foo(s)
    }

    let identity_key = Box::new(IdentityKey::generate());
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_private_key(identity_key)
        .build();
    let server_session = ServerSession::new(server_config);
    test(server_session);
}
