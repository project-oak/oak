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
    string::{String, ToString},
    sync::Arc,
};

use anyhow::Context;
use googletest::prelude::*;
use oak_crypto::identity_key::{IdentityKey, IdentityKeyHandle};
use oak_proto_rust::oak::{
    attestation::v1::{Assertion, Endorsements, Evidence},
    session::v1::{
        AttestRequest, AttestResponse, EndorsedEvidence, PlaintextMessage, SessionBinding,
        SessionRequest, SessionResponse, session_request::Request, session_response::Response,
    },
};
use oak_session::{
    ClientSession, ProtocolEngine, ServerSession, Session,
    aggregators::PassThrough,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    session::{
        AttestationEvidence, AttestationPublisher, DEFAULT_MAX_ATTESTATION_SIZE,
        DEFAULT_MAX_MESSAGE_QUEUE_LEN,
    },
};
use oak_session_testing::{
    HandshakeFollowup, TestAttestationPublisher,
    create_failing_mock_session_binding_verifier_provider, create_failing_mock_verifier,
    create_mock_attester, create_mock_binder, create_mock_endorser, create_mock_key_extractor,
    create_mock_session_binding_verifier_provider, create_mock_session_key_assertion_generator,
    create_passing_mock_session_key_assertion_verifier, create_passing_mock_verifier, do_attest,
    do_handshake, invoke_hello_world,
};

const MATCHED_ATTESTER_ID1: &str = "MATCHED_ATTESTER_ID1";
const MATCHED_ATTESTER_ID2: &str = "MATCHED_ATTESTER_ID2";
const MATCHED_ATTESTER_ID3: &str = "MATCHED_ATTESTER_ID3";
const MATCHED_ATTESTER_ID4: &str = "MATCHED_ATTESTER_ID4";

#[googletest::test]
fn pairwise_nn_unattested_succeeds() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nk_unattested_succeeds() -> anyhow::Result<()> {
    let identity_key = Box::new(IdentityKey::generate());
    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_peer_static_public_key(identity_key.get_public_key().unwrap().as_slice())
        .build();
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(identity_key)
        .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[should_panic]
#[googletest::test]
fn pairwise_nk_unattested_mismatched_keys_fails() -> anyhow::Result<()> {
    let identity_key = Box::new(IdentityKey::generate());
    let wrong_identity_key = Box::new(IdentityKey::generate());
    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_peer_static_public_key(identity_key.get_public_key().unwrap().as_slice())
        .build();
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(wrong_identity_key)
        .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    Ok(())
}

#[googletest::test]
fn pairwise_nn_unattested_self_succeeds() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let client_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN)
        .add_attestation_publisher(
            &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
        )
        .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_unattested_compatible() -> anyhow::Result<()> {
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;
    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_peer_self_succeeds() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_session_key_assertion_generator(assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: anything(),
            assertion_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID2.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            handshake_hash: not(is_empty()),
        }))
    );

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_peer_broken() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;
    assert_that!(server_session.get_outgoing_message(), ok(none()));

    assert_that!(client_session.is_open(), eq(true));
    assert_that!(server_session.is_open(), eq(true));

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_self_bidi() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());
    let server_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID2.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID2.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID2.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_attestation_publisher(
                &(server_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID2.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID2.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );

    assert_that!(
        server_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );
    Ok(())
}

#[googletest::test]
fn pairwise_nn_bidirectional_succeeds() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID2.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID2.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID2.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn pairwise_nn_peer_self_succeeds_custom_session_binding_verifier() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_session_binding_verifier_provider(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn get_peer_attestation_evidence() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_session_binding_verifier_provider(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    assert_that!(
        client_session.get_peer_attestation_evidence(),
        ok(matches_pattern!(AttestationEvidence {
            evidence: elements_are![(
                &MATCHED_ATTESTER_ID1.to_string(),
                &EndorsedEvidence {
                    evidence: Some(Evidence { ..Default::default() }),
                    endorsements: Some(Endorsements { ..Default::default() })
                }
            )],
            evidence_bindings: elements_are![(
                eq(&MATCHED_ATTESTER_ID1.to_string()),
                field!(&SessionBinding.binding, ref not(is_empty()))
            )],
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty()),
        }))
    );
    // The client does not send any attestation evidence/bindings to the server.
    assert_that!(
        server_session.get_peer_attestation_evidence(),
        ok(matches_pattern!(AttestationEvidence {
            evidence: is_empty(),
            evidence_bindings: is_empty(),
            assertions: is_empty(),
            assertion_bindings: is_empty(),
            handshake_hash: not(is_empty())
        }))
    );

    Ok(())
}

#[googletest::test]
fn successful_session_publishes_evidence() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());
    let server_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let server_assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_assertion = Assertion { content: "client test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .add_self_attester(MATCHED_ATTESTER_ID3.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID3.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID4.to_string(),
                create_mock_session_key_assertion_generator(client_assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID3.to_string(), create_mock_binder())
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::Bidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_session_key_assertion_generator(server_assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID3.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID4.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(server_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;
    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected)?;

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        }))
    );
    assert_that!(
        client_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        })
    );
    assert_that!(
        server_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        }))
    );
    assert_that!(
        server_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        })
    );
    Ok(())
}

#[googletest::test]
fn handshake_failure_client_publishes_evidence() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_failing_mock_session_binding_verifier_provider(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_session_key_assertion_generator(assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    assert_that!(
        do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected),
        err(anything())
    );

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        }))
    );
    assert_that!(
        client_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        })
    );
    Ok(())
}

#[googletest::test]
fn attestation_failure_client_publishes_evidence() -> anyhow::Result<()> {
    let client_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_failing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(client_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_session_key_assertion_generator(assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    assert_that!(do_attest(&mut client_session, &mut server_session), err(anything()));

    assert_that!(
        client_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: is_empty(),
            assertions: not(is_empty()),
            assertion_bindings: is_empty(),
            handshake_hash: is_empty(),
        }))
    );
    assert_that!(
        client_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: is_empty(),
            assertions: not(is_empty()),
            assertion_bindings: is_empty(),
            handshake_hash: is_empty(),
        })
    );
    Ok(())
}

#[googletest::test]
fn handshake_failure_server_publishes_evidence() -> anyhow::Result<()> {
    let server_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_session_key_assertion_generator(assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_failing_mock_session_binding_verifier_provider(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(server_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    // The handshake should now return an error due to the failing binder.
    assert_that!(
        do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::Expected),
        err(anything())
    );

    assert_that!(
        server_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        }))
    );
    assert_that!(
        server_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: not(is_empty()),
            assertions: not(is_empty()),
            assertion_bindings: not(is_empty()),
            handshake_hash: not(is_empty()),
        })
    );
    Ok(())
}

#[googletest::test]
fn attestation_failure_server_publishes_evidence() -> anyhow::Result<()> {
    let server_attestation_publisher = Arc::new(TestAttestationPublisher::new());

    let assertion = Assertion { content: "test".as_bytes().to_vec() };
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_self_assertion_generator(
                MATCHED_ATTESTER_ID2.to_string(),
                create_mock_session_key_assertion_generator(assertion.clone()),
            )
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_failing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .add_peer_assertion_verifier(
                MATCHED_ATTESTER_ID2.to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .add_attestation_publisher(
                &(server_attestation_publisher.clone() as Arc<dyn AttestationPublisher>),
            )
            .build();
    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    let attestation_result = do_attest(&mut client_session, &mut server_session);
    assert_that!(attestation_result, err(anything()));

    assert_that!(
        server_attestation_publisher.take(),
        some(matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: is_empty(),
            assertions: not(is_empty()),
            assertion_bindings: is_empty(),
            handshake_hash: is_empty(),
        }))
    );
    assert_that!(
        server_session.get_peer_attestation_evidence()?,
        matches_pattern!(AttestationEvidence {
            evidence: not(is_empty()),
            evidence_bindings: is_empty(),
            assertions: not(is_empty()),
            assertion_bindings: is_empty(),
            handshake_hash: is_empty(),
        })
    );
    Ok(())
}

#[googletest::test]
fn test_session_sendable() -> anyhow::Result<()> {
    fn foo<T: Send>(_: T) {}

    fn test(s: ServerSession) {
        foo(s)
    }

    let identity_key = Box::new(IdentityKey::generate());
    let server_config = SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNK)
        .set_self_static_private_key(identity_key)
        .build();
    let server_session = ServerSession::create(server_config)?;
    test(server_session);
    Ok(())
}

#[googletest::test]
fn test_outgoing_message_queue_fails_when_exceeded() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    for _ in 0..DEFAULT_MAX_MESSAGE_QUEUE_LEN {
        assert_that!(client_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
        assert_that!(server_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
    }
    assert_that!(
        client_session.write(PlaintextMessage { plaintext: "Hello".into() }),
        err(anything())
    );
    assert_that!(
        server_session.write(PlaintextMessage { plaintext: "Hello".into() }),
        err(anything())
    );

    Ok(())
}

#[googletest::test]
fn test_client_incoming_message_queue_fails_when_exceeded() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    for _ in 0..DEFAULT_MAX_MESSAGE_QUEUE_LEN {
        assert_that!(server_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
        let encrypted_message = server_session
            .get_outgoing_message()
            .expect("An error occurred while getting the client outgoing message")
            .expect("No client outgoing message was produced");
        assert_that!(client_session.put_incoming_message(encrypted_message), ok(some(())));
    }
    assert_that!(server_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
    let encrypted_message = server_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client outgoing message")
        .expect("No client outgoing message was produced");
    assert_that!(client_session.put_incoming_message(encrypted_message), err(anything()));

    Ok(())
}

#[googletest::test]
fn test_server_incoming_message_queue_fails_when_exceeded() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    for _ in 0..DEFAULT_MAX_MESSAGE_QUEUE_LEN {
        assert_that!(client_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
        let encrypted_message = client_session
            .get_outgoing_message()
            .expect("An error occurred while getting the client outgoing message")
            .expect("No client outgoing message was produced");
        assert_that!(server_session.put_incoming_message(encrypted_message), ok(some(())));
    }
    assert_that!(client_session.write(PlaintextMessage { plaintext: "Hello".into() }), ok(()));
    let encrypted_message = client_session
        .get_outgoing_message()
        .expect("An error occurred while getting the client outgoing message")
        .expect("No client outgoing message was produced");
    assert_that!(server_session.put_incoming_message(encrypted_message), err(anything()));

    Ok(())
}

#[googletest::test]
fn client_fails_when_attest_message_size_limit_exceeded() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_assertion_verifier(
                "0".to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .build();
    let mut client_session = ClientSession::create(client_config)?;

    let mut large_attest_message = AttestResponse { ..Default::default() };
    for i in 0..DEFAULT_MAX_ATTESTATION_SIZE {
        large_attest_message.assertions.insert(i.to_string(), Assertion { content: "test".into() });
    }
    client_session.get_outgoing_message()?;
    assert_that!(
        client_session.put_incoming_message(SessionResponse {
            response: Some(Response::AttestResponse(large_attest_message))
        }),
        err(anything())
    );

    Ok(())
}

#[googletest::test]
fn server_fails_when_attest_message_size_limit_exceeded() -> anyhow::Result<()> {
    let server_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_assertion_verifier(
                "0".to_string(),
                create_passing_mock_session_key_assertion_verifier(),
            )
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .build();
    let mut server_session = ServerSession::create(server_config)?;

    let mut large_attest_message = AttestRequest { ..Default::default() };
    for i in 0..DEFAULT_MAX_ATTESTATION_SIZE {
        large_attest_message.assertions.insert(i.to_string(), Assertion { content: "test".into() });
    }
    assert_that!(
        server_session.put_incoming_message(SessionRequest {
            request: Some(Request::AttestRequest(large_attest_message))
        }),
        err(anything())
    );

    Ok(())
}

/// SessionChannel/SessionInitializer Tests
#[googletest::gtest]
#[tokio::test]
async fn channel_unattested_nn_pair() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    channel_pair_test(client_config, server_config).await
}

#[googletest::gtest]
#[tokio::test]
async fn channel_nn_peer_self_succeeds() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_key_extractor(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_key_extractor(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    channel_pair_test(client_config, server_config).await
}

#[googletest::gtest]
#[tokio::test]
async fn channel_bidi_nn_pair() -> anyhow::Result<()> {
    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                MATCHED_ATTESTER_ID1.to_string(),
                create_passing_mock_verifier(),
                create_mock_session_binding_verifier_provider(),
            )
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(MATCHED_ATTESTER_ID1.to_string(), create_mock_attester())
            .add_self_endorser(MATCHED_ATTESTER_ID1.to_string(), create_mock_endorser())
            .add_session_binder(MATCHED_ATTESTER_ID1.to_string(), create_mock_binder())
            .build();
    channel_pair_test(client_config, server_config).await
}

async fn channel_pair_test(
    client_config: SessionConfig,
    server_config: SessionConfig,
) -> anyhow::Result<()> {
    // Use channels for simple client-server implementation.
    let (client_tx, mut client_rx) = tokio::sync::mpsc::channel::<SessionRequest>(10);
    let (server_tx, mut server_rx) = tokio::sync::mpsc::channel::<SessionResponse>(10);

    // Start a server
    let server_join: tokio::task::JoinHandle<anyhow::Result<()>> = tokio::task::spawn(async move {
        let mut server_session = ServerSession::create(server_config)?;

        // Handshake Sequence
        while !server_session.is_open() {
            let next_request = client_rx.recv().await.context("getting next client message")?;
            server_session.handle_init_message(next_request).context("handling init message")?;
            if !server_session.is_open() {
                let next_response =
                    server_session.next_init_message().context("getting next init message")?;
                server_tx.send(next_response).await.context("sending response to client")?
            }
        }

        // Receive a Request
        let request: SessionRequest = client_rx.recv().await.context("receiving client request")?;
        let decrypted_request = server_session.decrypt(request).context("decrypting request")?;

        // Process Request
        let response = format!("Hello {}", String::from_utf8_lossy(decrypted_request.as_slice()));

        // Send Response
        let encrypted_response =
            server_session.encrypt(response.as_bytes()).context("encrypting response")?;
        server_tx.send(encrypted_response).await.context("sending response")?;

        // All done
        Ok(())
    });

    let mut client_session = ClientSession::create(client_config)?;

    // Handshake sequence
    while !client_session.is_open() {
        let request = client_session.next_init_message().expect("failed to get init messge");
        client_tx.send(request).await.expect("failed to send init message");
        let response = server_rx.recv().await.context("getting next server message")?;
        client_session.handle_init_message(response).expect("failed to handle init response");
    }

    // Send Message
    let message_to_server = client_session.encrypt(b"Mister Tester")?;
    client_tx.send(message_to_server).await.context("sending message to server")?;

    // Receive Response
    let response = server_rx.recv().await.context("getting server response")?;
    assert_that!(client_session.decrypt(response)?, eq(b"Hello Mister Tester"));

    server_join.await.context("joining server")?.context("server failing")
}
