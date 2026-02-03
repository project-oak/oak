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
//

extern crate alloc;

use alloc::{boxed::Box, collections::BTreeMap};

use criterion::{Criterion, criterion_group, criterion_main};
use oak_crypto::identity_key::{IdentityKey, IdentityKeyHandle};
use oak_session::{
    ProtocolEngine,
    attestation::{AttestationState, PeerAttestationVerdict},
    config::HandshakeHandlerConfig,
    handshake::{ClientHandshakeHandler, HandshakeType, ServerHandshakeHandler},
};
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

pub fn do_handshake(
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
}

pub fn handshake_nn_benchmark(c: &mut Criterion) {
    c.bench_function("handshake NN", |b| b.iter(process_nn_handshake));
}

pub fn handshake_nk_benchmark(c: &mut Criterion) {
    c.bench_function("handshake NK", |b| b.iter(process_nk_handshake));
}

pub fn handshake_kk_benchmark(c: &mut Criterion) {
    c.bench_function("handshake KK", |b| b.iter(process_kk_handshake));
}

criterion_group!(benches, handshake_nn_benchmark, handshake_nk_benchmark, handshake_kk_benchmark);
criterion_main!(benches);
