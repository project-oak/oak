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

use oak_time::Instant;
use p256::{
    ecdsa::{Signature, SigningKey, signature::Signer},
    pkcs8::EncodePublicKey,
};
use tempfile::tempdir;

use crate::config::{
    authorized_endorsement::AuthorizedWorkloadEndorsementParams,
    confidential_space::ConfidentialSpaceVerifierParams,
};

#[test]
fn test_get_authorized_digests_with_manual_list() {
    let dir = tempdir().unwrap();
    let root_cert_path = dir.path().join("root.pem");

    let params = ConfidentialSpaceVerifierParams {
        root_certificate_pem_path: root_cert_path.to_str().unwrap().to_string(),
        container_reference_prefix: None,
        authorized_workload_endorsement: AuthorizedWorkloadEndorsementParams {
            authorized_image_digests: Some(vec![hex::encode(b"digest1"), hex::encode(b"digest2")]),
            authorized_endorsement_path: None,
            authorized_endorsement_signature_path: None,
            authorized_endorsement_verifying_key_pem_path: None,
        },
    };

    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let digests = params
        .authorized_workload_endorsement
        .get_authorized_digests(verification_time)
        .expect("failed to get digests");
    assert_eq!(digests.len(), 2);
    assert!(digests.contains(&b"digest1".to_vec()));
    assert!(digests.contains(&b"digest2".to_vec()));
}

#[test]
fn test_get_authorized_digests_merging() {
    let dir = tempdir().unwrap();

    use p256::elliptic_curve::rand_core::OsRng;
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = signing_key.verifying_key();
    let public_key_pem = verifying_key.to_public_key_pem(Default::default()).unwrap();

    let endorsement_path = dir.path().join("endorsement.json");
    let sig_path = dir.path().join("endorsement.sig");
    let key_path = dir.path().join("key.pem");

    let endorsement_json = format!(
        r#"{{
        "_type": "https://in-toto.io/Statement/v1",
        "subject": [
            {{
                "name": "test",
                "digest": {{
                    "sha256": "{}"
                }}
            }}
        ],
        "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
        "predicate": {{
            "issuedOn": "2026-07-14T12:00:00Z",
            "validity": {{
                "notBefore": "2026-07-01T12:00:00Z",
                "notAfter": "2027-07-01T12:00:00Z"
            }}
        }}
    }}"#,
        hex::encode(b"endorsement_digest")
    );

    std::fs::write(&endorsement_path, endorsement_json.as_bytes()).unwrap();
    std::fs::write(&key_path, public_key_pem).unwrap();

    let signature: Signature = signing_key.sign(endorsement_json.as_bytes());
    std::fs::write(&sig_path, signature.to_der()).unwrap();

    let params = ConfidentialSpaceVerifierParams {
        root_certificate_pem_path: "dummy.pem".to_string(),
        container_reference_prefix: None,
        authorized_workload_endorsement: AuthorizedWorkloadEndorsementParams {
            authorized_image_digests: Some(vec![hex::encode(b"manual_digest")]),
            authorized_endorsement_path: Some(endorsement_path.to_str().unwrap().to_string()),
            authorized_endorsement_signature_path: Some(sig_path.to_str().unwrap().to_string()),
            authorized_endorsement_verifying_key_pem_path: Some(
                key_path.to_str().unwrap().to_string(),
            ),
        },
    };

    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let digests = params
        .authorized_workload_endorsement
        .get_authorized_digests(verification_time)
        .expect("failed to get digests");
    assert_eq!(digests.len(), 2);
    assert!(digests.contains(&b"manual_digest".to_vec()));
    assert!(digests.contains(&b"endorsement_digest".to_vec()));
}

#[test]
fn test_mutual_exclusion_error() {
    let dir = tempdir().unwrap();
    let root_cert_path = dir.path().join("root.pem");
    std::fs::write(&root_cert_path, "dummy cert").unwrap();

    let params = ConfidentialSpaceVerifierParams {
        root_certificate_pem_path: root_cert_path.to_str().unwrap().to_string(),
        container_reference_prefix: Some("gcr.io/my-project/my-app".to_string()),
        authorized_workload_endorsement: AuthorizedWorkloadEndorsementParams {
            authorized_image_digests: Some(vec![hex::encode(b"digest1")]),
            authorized_endorsement_path: None,
            authorized_endorsement_signature_path: None,
            authorized_endorsement_verifying_key_pem_path: None,
        },
    };

    let builder = oak_session::config::SessionConfig::builder(
        oak_session::attestation::AttestationType::Bidirectional,
        oak_session::handshake::HandshakeType::NoiseNN,
    );
    let result = params.apply(builder);
    match result {
        Err(err) => assert!(err.to_string().contains(
            "cannot specify both container_reference_prefix and authorized_image_digests / authorized_endorsement_path"
        )),
        Ok(_) => panic!("expected mutual exclusion error"),
    }
}
