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

use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};

use googletest::prelude::*;
use mockall::mock;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_crypto::{
    encryptor::{Encryptor, Payload},
    identity_key::{IdentityKey, IdentityKeyHandle},
    noise_handshake::{UnorderedCrypter, SYMMETRIC_KEY_LEN},
};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results, AttestationResults, Endorsements, Evidence, ExtractedEvidence,
    },
    session::v1::{PlaintextMessage, SessionRequest, SessionResponse},
};
use p256::ecdsa::SigningKey;
use rand_core::OsRng;

use crate::{
    alloc::string::ToString,
    attestation::AttestationType,
    config::{HandshakerConfig, SessionConfig},
    encryptors::{OrderedChannelEncryptor, UnorderedChannelEncryptor},
    handshake::{ClientHandshaker, HandshakeType, Handshaker, ServerHandshaker},
    session_binding::SignatureBinderBuilder,
    ClientSession, ProtocolEngine, ServerSession, Session,
};

fn test_messages() -> Vec<PlaintextMessage> {
    vec![
        PlaintextMessage { plaintext: vec![1u8, 2u8, 3u8, 4u8] },
        PlaintextMessage { plaintext: vec![4u8, 3u8, 2u8, 1u8] },
        PlaintextMessage { plaintext: vec![] },
    ]
}

// Since [`Attester`], [`Endorser`] and [`AttestationVerifier`] are external
// traits, we have to use `mock!` instead of `[automock]` and define a test
// struct that implements those traits.
// <https://docs.rs/mockall/latest/mockall/#external-traits>
mock! {
    TestAttester {}
    impl Attester for TestAttester {
        fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()>;
        fn quote(&self) -> anyhow::Result<Evidence>;
    }
}

mock! {
    TestEndorser {}
    impl Endorser for TestEndorser {
        fn endorse<'a>(&self, evidence: Option<&'a Evidence>) -> anyhow::Result<Endorsements>;
    }
}

mock! {
    TestAttestationVerifier {}
    impl AttestationVerifier for TestAttestationVerifier {
        fn verify(
            &self,
            evidence: &Evidence,
            endorsements: &Endorsements,
        ) -> anyhow::Result<AttestationResults>;
    }
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
        session_binders: BTreeMap::new(),
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(
        HandshakerConfig {
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
    let client_handshaker = ClientHandshaker::create(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNK,
        self_static_private_key: None,
        peer_static_public_key: Some(identity_key.get_public_key().unwrap()),
        session_binders: BTreeMap::new(),
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(
        HandshakerConfig {
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
    let client_handshaker = ClientHandshaker::create(HandshakerConfig {
        handshake_type: HandshakeType::NoiseNN,
        self_static_private_key: None,
        peer_static_public_key: None,
        session_binders: BTreeMap::new(),
    })
    .unwrap();
    let server_handshaker = ServerHandshaker::new(
        HandshakerConfig {
            handshake_type: HandshakeType::NoiseNN,
            self_static_private_key: None,
            peer_static_public_key: None,
            session_binders: BTreeMap::new(),
        },
        false,
    );
    do_handshake(client_handshaker, server_handshaker);
}

fn do_handshake(mut client_handshaker: ClientHandshaker, mut server_handshaker: ServerHandshaker) {
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

#[test]
fn session_succeeds_with_bidirectional_attestation() {
    let attester_id = "id".to_string();
    let binding_key_client = SigningKey::random(&mut OsRng);
    let verifying_key_client_vec: Vec<u8> =
        binding_key_client.verifying_key().to_sec1_bytes().to_vec();
    let binding_key_server = SigningKey::random(&mut OsRng);
    let verifying_key_server_vec: Vec<u8> =
        binding_key_server.verifying_key().to_sec1_bytes().to_vec();
    let mut client_attester = MockTestAttester::new();
    let mut client_endorser = MockTestEndorser::new();
    let mut client_verifier = MockTestAttestationVerifier::new();
    client_attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    client_endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    client_verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            extracted_evidence: Some(ExtractedEvidence {
                signing_public_key: verifying_key_server_vec.clone(),
                ..Default::default()
            }),
            ..Default::default()
        })
    });
    let mut server_attester = MockTestAttester::new();
    let mut server_endorser = MockTestEndorser::new();
    let mut server_verifier = MockTestAttestationVerifier::new();
    server_attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    server_endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    server_verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            extracted_evidence: Some(ExtractedEvidence {
                signing_public_key: verifying_key_client_vec.clone(),
                ..Default::default()
            }),
            ..Default::default()
        })
    });
    let client_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(attester_id.clone(), Box::new(client_attester))
            .add_self_endorser(attester_id.clone(), Box::new(client_endorser))
            .add_peer_verifier(attester_id.clone(), Box::new(client_verifier))
            .add_session_binder(
                attester_id.clone(),
                Box::new(
                    SignatureBinderBuilder::default()
                        .signer(Box::new(binding_key_client.clone()))
                        .build()
                        .unwrap(),
                ),
            )
            .build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(attester_id.clone(), Box::new(server_attester))
            .add_self_endorser(attester_id.clone(), Box::new(server_endorser))
            .add_peer_verifier(attester_id.clone(), Box::new(server_verifier))
            .add_session_binder(
                attester_id.clone(),
                Box::new(
                    SignatureBinderBuilder::default()
                        .signer(Box::new(binding_key_server.clone()))
                        .build()
                        .unwrap(),
                ),
            )
            .build();
    let mut server_session = ServerSession::create(server_config).unwrap();
    do_session_handshake(&mut client_session, &mut server_session);

    for message in test_messages() {
        verify_session_message(&mut client_session, &mut server_session, &message);
        verify_session_message(&mut server_session, &mut client_session, &message);
    }
}

#[test]
fn session_succeeds_with_unidirectional_attestation() {
    let attester_id = "id".to_string();
    let binding_key_server = SigningKey::random(&mut OsRng);
    let verifying_key_server_vec: Vec<u8> =
        binding_key_server.verifying_key().to_sec1_bytes().to_vec();
    let mut client_verifier = MockTestAttestationVerifier::new();
    client_verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            extracted_evidence: Some(ExtractedEvidence {
                signing_public_key: verifying_key_server_vec.clone(),
                ..Default::default()
            }),
            ..Default::default()
        })
    });
    let mut server_attester = MockTestAttester::new();
    let mut server_endorser = MockTestEndorser::new();
    server_attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    server_endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier(attester_id.clone(), Box::new(client_verifier))
            .build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(attester_id.clone(), Box::new(server_attester))
            .add_self_endorser(attester_id.clone(), Box::new(server_endorser))
            .add_session_binder(
                attester_id.clone(),
                Box::new(
                    SignatureBinderBuilder::default()
                        .signer(Box::new(binding_key_server.clone()))
                        .build()
                        .unwrap(),
                ),
            )
            .build();
    let mut server_session = ServerSession::create(server_config).unwrap();
    do_session_handshake(&mut client_session, &mut server_session);

    for message in test_messages() {
        verify_session_message(&mut client_session, &mut server_session, &message);
        verify_session_message(&mut server_session, &mut client_session, &message);
    }
}

#[test]
fn session_fails_with_attestation_binding_fail() {
    let attester_id = "id".to_string();
    let binding_key_server = SigningKey::random(&mut OsRng);
    let mismatched_verifying_key_server_vec: Vec<u8> =
        SigningKey::random(&mut OsRng).verifying_key().to_sec1_bytes().to_vec();
    let mut client_verifier = MockTestAttestationVerifier::new();
    client_verifier.expect_verify().returning(move |_, _| {
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            extracted_evidence: Some(ExtractedEvidence {
                signing_public_key: mismatched_verifying_key_server_vec.clone(),
                ..Default::default()
            }),
            ..Default::default()
        })
    });
    let mut server_attester = MockTestAttester::new();
    let mut server_endorser = MockTestEndorser::new();
    server_attester.expect_quote().returning(|| Ok(Evidence { ..Default::default() }));
    server_endorser.expect_endorse().returning(|_| Ok(Endorsements { ..Default::default() }));
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier(attester_id.clone(), Box::new(client_verifier))
            .build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(attester_id.clone(), Box::new(server_attester))
            .add_self_endorser(attester_id.clone(), Box::new(server_endorser))
            .add_session_binder(
                attester_id.clone(),
                Box::new(
                    SignatureBinderBuilder::default()
                        .signer(Box::new(binding_key_server.clone()))
                        .build()
                        .unwrap(),
                ),
            )
            .build();
    let mut server_session = ServerSession::create(server_config).unwrap();

    // Attestation succeeds
    let attest_request = client_session.get_outgoing_message().unwrap().unwrap();
    server_session.put_incoming_message(attest_request).unwrap();
    let attest_response = server_session.get_outgoing_message().unwrap().unwrap();
    client_session.put_incoming_message(attest_response).unwrap();

    // Handshake fails
    let handshake_request = client_session.get_outgoing_message().unwrap().unwrap();
    server_session.put_incoming_message(handshake_request).unwrap();
    let handshake_response = server_session.get_outgoing_message().unwrap().unwrap();
    assert_that!(client_session.put_incoming_message(handshake_response), err(anything()));
}

#[test]
fn session_nn_succeeds() {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut client_session = ClientSession::create(client_config).unwrap();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut server_session = ServerSession::create(server_config).unwrap();
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
        .set_self_static_private_key(identity_key)
        .build();
    let mut server_session = ServerSession::create(server_config).unwrap();
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
        .set_self_static_private_key(identity_key2)
        .build();
    let mut server_session = ServerSession::create(server_config).unwrap();
    do_session_handshake(&mut client_session, &mut server_session);
}

fn do_session_handshake(client_session: &mut ClientSession, server_session: &mut ServerSession) {
    while !client_session.is_open() || !server_session.is_open() {
        let request = client_session.get_outgoing_message().unwrap().unwrap();
        server_session.put_incoming_message(request).unwrap();
        if let Some(response) = server_session.get_outgoing_message().unwrap() {
            client_session.put_incoming_message(response).unwrap();
        }
    }
}

trait ProtocolSession<I, O>: Session + ProtocolEngine<I, O> {}

impl ProtocolSession<SessionResponse, SessionRequest> for ClientSession {}
impl ProtocolSession<SessionRequest, SessionResponse> for ServerSession {}

fn verify_session_message<I, O>(
    session1: &mut dyn ProtocolSession<I, O>,
    session2: &mut dyn ProtocolSession<O, I>,
    message: &PlaintextMessage,
) {
    session1.write(message.clone()).unwrap();
    let outgoing_message = session1.get_outgoing_message().unwrap().unwrap();
    assert_that!(session2.put_incoming_message(outgoing_message), ok(some(())));
    let decrypted_message = session2.read().unwrap().unwrap();
    assert_that!(decrypted_message, eq(message));
}

#[test]
fn test_session_sendable() {
    fn foo<T: Send>(_: T) {}

    fn test(s: ServerSession) {
        foo(s)
    }

    let identity_key = Box::new(IdentityKey::generate());
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(identity_key)
        .build();
    let server_session = ServerSession::create(server_config).unwrap();
    test(server_session);
}

#[test]
fn test_unordered_encryptor_inorder_messages() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 0) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 0) };

    for message in test_messages() {
        let payload = Payload { message: message.plaintext.to_vec(), nonce: None, aad: None };
        let encrypted_payload = replica_1.encrypt(payload).unwrap();
        let plaintext = replica_2.decrypt(encrypted_payload).unwrap().message;
        assert_that!(message.plaintext, eq(&plaintext));
    }
}

#[test]
fn test_unordered_encryptor_window_size_0() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 0) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 0) };
    let test_messages = test_messages();

    let encrypted_payload_1 = replica_1
        .encrypt(Payload { message: test_messages[0].plaintext.to_vec(), nonce: None, aad: None })
        .unwrap();
    let encrypted_payload_2 = replica_1
        .encrypt(Payload { message: test_messages[1].plaintext.to_vec(), nonce: None, aad: None })
        .unwrap();

    // Decrypt in reverse order
    let plaintext_2 = replica_2.decrypt(encrypted_payload_2).unwrap().message;
    assert_that!(test_messages[1].plaintext, eq(&plaintext_2));
    // Decrypting first message fails since it is from a lower nonce.
    assert_that!(replica_2.decrypt(encrypted_payload_1).is_err(), eq(true));
}

fn clone_payload(payload: &Payload) -> Payload {
    Payload {
        message: payload.message.clone(),
        nonce: payload.nonce.clone(),
        aad: payload.aad.clone(),
    }
}

#[test]
fn test_unordered_encryptor_window_size_3() {
    let key_1 = &[42u8; SYMMETRIC_KEY_LEN];
    let key_2 = &[52u8; SYMMETRIC_KEY_LEN];
    let test_messages = &[
        vec![1u8, 2u8, 3u8, 4u8],
        vec![4u8, 3u8, 2u8, 1u8],
        vec![1u8, 1u8, 1u8, 1u8],
        vec![2u8, 2u8, 2u8, 2u8],
        vec![3u8, 3u8, 3u8, 3u8],
        vec![4u8, 4u8, 4u8, 4u8],
    ];
    let mut replica_1 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_1, key_2, 3) };
    let mut replica_2 =
        UnorderedChannelEncryptor { crypter: UnorderedCrypter::new(key_2, key_1, 3) };
    let mut encrypted_payloads = vec![];
    for item in test_messages {
        encrypted_payloads.push(
            replica_1.encrypt(Payload { message: item.to_vec(), nonce: None, aad: None }).unwrap(),
        );
    }

    // Out-of-order decryption
    let plaintext_3 = replica_2.decrypt(clone_payload(&encrypted_payloads[3])).unwrap();
    assert_that!(test_messages[3], eq(&plaintext_3.message));
    // Decrypting messages within the window should be ok.
    let plaintext_1 = replica_2.decrypt(clone_payload(&encrypted_payloads[1])).unwrap();
    assert_that!(test_messages[1], eq(&plaintext_1.message));
    let plaintext_2 = replica_2.decrypt(clone_payload(&encrypted_payloads[2])).unwrap();
    assert_that!(test_messages[2], eq(&plaintext_2.message));
    // Replaying message should fail.
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[3])).is_err(), eq(true));
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[2])).is_err(), eq(true));
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[1])).is_err(), eq(true));
    // Decrypting messages outside the window should fail.
    assert_that!(replica_2.decrypt(clone_payload(&encrypted_payloads[0])).is_err(), eq(true));

    // Decrypt more messages in order.
    let plaintext_4 = replica_2.decrypt(clone_payload(&encrypted_payloads[4])).unwrap();
    assert_that!(test_messages[4], eq(&plaintext_4.message));
    let plaintext_5 = replica_2.decrypt(clone_payload(&encrypted_payloads[5])).unwrap();
    assert_that!(test_messages[5], eq(&plaintext_5.message));
}
