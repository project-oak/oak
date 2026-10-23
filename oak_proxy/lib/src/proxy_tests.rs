//
// Copyright 2026 The Project Oak Authors
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

use base64::Engine;
use oak_attestation::public_key::{PublicKeyAttester, PublicKeyEndorser};
use oak_proto_rust::{
    attestation::CONFIDENTIAL_SPACE_ATTESTATION_ID,
    oak::attestation::v1::ConfidentialSpaceEndorsement,
};
use oak_session::{
    ClientSession, ProtocolEngine, ServerSession, Session, attestation::AttestationType,
    config::SessionConfig, handshake::HandshakeType, session_binding::SignatureBinder,
};
use p256::ecdsa::SigningKey;

use crate::{
    config,
    proxy::{NoiseProxySession, ProxySession},
};

/// Returns a JWT with Confidential Space claims and no valid signature.
fn unsigned_jwt(image_digest: &str) -> String {
    let encode = |data: &str| base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(data);
    let claims = format!(
        r#"{{"aud":"","iss":"","sub":"","iat":0,"exp":0,"nbf":0,"dbgstat":"disabled-since-boot","eat_nonce":"","swname":"CONFIDENTIAL_SPACE","submods":{{"confidential_space":{{}},"container":{{"image_reference":"","image_digest":"{image_digest}","env":{{}},"args":[]}}}}}}"#
    );
    format!("{}.{}.{}", encode(r#"{"alg":"none"}"#), encode(&claims), encode("signature"))
}

#[test]
fn test_attestation_header_ignores_unverified_peer_evidence() {
    let binding_key = SigningKey::from_slice(&[1; 32]).unwrap();
    let client_config =
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester(
                CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
                Box::new(PublicKeyAttester::new(*binding_key.verifying_key())),
            )
            .add_self_endorser(
                CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
                Box::new(PublicKeyEndorser::new(ConfidentialSpaceEndorsement {
                    jwt_token: unsigned_jwt("sha256:forged"),
                    ..Default::default()
                })),
            )
            .add_session_binder(
                CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
                Box::new(SignatureBinder::new(Box::new(binding_key))),
            )
            .build();
    // A server proxy without attestation verifiers.
    let server_config = config::build_session_config(&vec![], &vec![], None).unwrap();

    let mut client = ClientSession::create(client_config).unwrap();
    let mut server = ServerSession::create(server_config).unwrap();
    while !client.is_open() || !server.is_open() {
        if let Some(request) = client.get_outgoing_message().unwrap() {
            server.put_incoming_message(request).unwrap();
        }
        if let Some(response) = server.get_outgoing_message().unwrap() {
            client.put_incoming_message(response).unwrap();
        }
    }
    assert_eq!(server.get_peer_attestation_evidence().unwrap().evidence.len(), 1);

    let proxy_session = NoiseProxySession::new(server, config::verified_attestation_ids(&[]));
    assert_eq!(proxy_session.attestation_header_payload(), None);
}
