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

use std::{boxed::Box, string::ToString, sync::Arc};

use googletest::prelude::*;
use oak_session::{
    aggregators::PassThrough, attestation::AttestationType, config::SessionConfig,
    handshake::HandshakeType, ClientSession, ServerSession,
};
use oak_session_endorsed_evidence::{
    EndorsedEvidenceBindableAssertionGenerator, EndorsedEvidenceBoundAssertionVerifier,
};
use oak_session_testing::{
    create_failing_mock_session_binding_verifier_provider, create_failing_mock_verifier,
    create_mock_attester, create_mock_binder, create_mock_endorser,
    create_mock_session_binding_verifier_provider, create_passing_mock_verifier, do_attest,
    do_handshake, invoke_hello_world, HandshakeFollowup,
};

const ATTESTER_ID: &str = "ATTESTER_ID";

#[googletest::test]
fn attestation_succeeds() -> anyhow::Result<()> {
    let server_assertion_generator = {
        let attester = create_mock_attester();
        let endorser = create_mock_endorser();
        Box::new(EndorsedEvidenceBindableAssertionGenerator::new(
            attester.into(),
            endorser.into(),
            Arc::from(create_mock_binder()),
        ))
    };

    let client_assertion_verifier = {
        let verifier = create_passing_mock_verifier();
        let provider = create_mock_session_binding_verifier_provider();
        Box::new(EndorsedEvidenceBoundAssertionVerifier::new(
            Arc::from(verifier),
            Arc::from(provider),
        ))
    };

    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_assertion_verifier(ATTESTER_ID.to_string(), client_assertion_verifier)
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_assertion_generator(ATTESTER_ID.to_string(), server_assertion_generator)
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;

    do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected)?;

    invoke_hello_world(&mut client_session, &mut server_session);

    Ok(())
}

#[googletest::test]
fn attestation_fails() -> anyhow::Result<()> {
    let server_assertion_generator = {
        let attester = create_mock_attester();
        let endorser = create_mock_endorser();
        Box::new(EndorsedEvidenceBindableAssertionGenerator::new(
            attester.into(),
            endorser.into(),
            Arc::from(create_mock_binder()),
        ))
    };

    let client_assertion_verifier = {
        let verifier = create_failing_mock_verifier();
        let provider = create_mock_session_binding_verifier_provider();
        Box::new(EndorsedEvidenceBoundAssertionVerifier::new(
            Arc::from(verifier),
            Arc::from(provider),
        ))
    };

    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_assertion_verifier(ATTESTER_ID.to_string(), client_assertion_verifier)
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_assertion_generator(ATTESTER_ID.to_string(), server_assertion_generator)
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    assert_that!(do_attest(&mut client_session, &mut server_session), err(anything()));

    Ok(())
}

#[googletest::test]
fn session_binding_fails() -> anyhow::Result<()> {
    let server_assertion_generator = {
        let attester = create_mock_attester();
        let endorser = create_mock_endorser();
        Box::new(EndorsedEvidenceBindableAssertionGenerator::new(
            attester.into(),
            endorser.into(),
            Arc::from(create_mock_binder()),
        ))
    };

    let client_assertion_verifier = {
        let verifier = create_passing_mock_verifier();
        let provider = create_failing_mock_session_binding_verifier_provider();
        Box::new(EndorsedEvidenceBoundAssertionVerifier::new(
            Arc::from(verifier),
            Arc::from(provider),
        ))
    };

    let client_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_assertion_verifier(ATTESTER_ID.to_string(), client_assertion_verifier)
            .set_assertion_attestation_aggregator(Box::new(PassThrough {}))
            .build();
    let server_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_assertion_generator(ATTESTER_ID.to_string(), server_assertion_generator)
            .build();

    let mut client_session = ClientSession::create(client_config)?;
    let mut server_session = ServerSession::create(server_config)?;

    do_attest(&mut client_session, &mut server_session)?;
    assert_that!(
        do_handshake(&mut client_session, &mut server_session, HandshakeFollowup::NotExpected),
        err(anything())
    );

    Ok(())
}
