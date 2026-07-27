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

use oak_time::Instant;
use p256::{
    ecdsa::{Signature, SigningKey, signature::Signer},
    elliptic_curve::rand_core::OsRng,
    pkcs8::EncodePublicKey,
};
use tempfile::tempdir;

use super::*;

fn create_test_keys() -> (SigningKey, String) {
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = signing_key.verifying_key();
    let public_key_pem = verifying_key.to_public_key_pem(Default::default()).unwrap();
    (signing_key, public_key_pem)
}

#[test]
fn test_verify_and_parse_valid_endorsement_succeeds() {
    let (signing_key, public_key_pem) = create_test_keys();

    let endorsement_json = r#"{
        "_type": "https://in-toto.io/Statement/v1",
        "subject": [
            {
                "name": "gcr.io/my-project/my-image",
                "digest": {
                    "sha256": "cc564c5f64a18fc6e53dd737ec19774b68b609eb59cac4f13dcfd25cb61f3f68"
                }
            }
        ],
        "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
        "predicate": {
            "issuedOn": "2026-07-14T12:00:00Z",
            "validity": {
                "notBefore": "2026-07-14T12:00:00Z",
                "notAfter": "2026-07-21T12:00:00Z"
            },
            "claims": [
                {
                    "type": "https://github.com/project-oak/oak/blob/main/docs/tr/claim/13420.md"
                }
            ]
        }
    }"#;
    let endorsement_bytes = endorsement_json.as_bytes();
    let signature: Signature = signing_key.sign(endorsement_bytes);
    let signature_bytes = signature.to_der();

    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let endorsement = AuthorizedEndorsement::verify_and_parse(
        endorsement_bytes,
        signature_bytes.as_bytes(),
        &public_key_pem,
        verification_time,
    )
    .expect("failed to verify and parse valid endorsement");

    assert_eq!(
        endorsement.authorized_digests,
        vec!["cc564c5f64a18fc6e53dd737ec19774b68b609eb59cac4f13dcfd25cb61f3f68"]
    );
}

#[test]
fn test_verify_and_parse_expired_endorsement_fails() {
    let (signing_key, public_key_pem) = create_test_keys();

    let endorsement_json = r#"{
        "_type": "https://in-toto.io/Statement/v1",
        "subject": [
            {
                "digest": {
                    "sha256": "cc564c5f64a18fc6e53dd737ec19774b68b609eb59cac4f13dcfd25cb61f3f68"
                }
            }
        ],
        "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
        "predicate": {
            "issuedOn": "2026-07-14T12:00:00Z",
            "validity": {
                "notBefore": "2026-07-14T12:00:00Z",
                "notAfter": "2026-07-21T12:00:00Z"
            }
        }
    }"#;
    let endorsement_bytes = endorsement_json.as_bytes();
    let signature: Signature = signing_key.sign(endorsement_bytes);
    let signature_bytes = signature.to_der();

    let verification_time = oak_time::make_instant!("2026-07-22T12:00:00Z");
    let result = AuthorizedEndorsement::verify_and_parse(
        endorsement_bytes,
        signature_bytes.as_bytes(),
        &public_key_pem,
        verification_time,
    );
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("endorsement has expired"));
}

#[test]
fn test_verify_and_parse_not_yet_valid_endorsement_fails() {
    let (signing_key, public_key_pem) = create_test_keys();

    let endorsement_json = r#"{
        "_type": "https://in-toto.io/Statement/v1",
        "subject": [
            {
                "digest": {
                    "sha256": "cc564c5f64a18fc6e53dd737ec19774b68b609eb59cac4f13dcfd25cb61f3f68"
                }
            }
        ],
        "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
        "predicate": {
            "issuedOn": "2026-07-14T12:00:00Z",
            "validity": {
                "notBefore": "2026-07-14T12:00:00Z",
                "notAfter": "2026-07-21T12:00:00Z"
            }
        }
    }"#;
    let endorsement_bytes = endorsement_json.as_bytes();
    let signature: Signature = signing_key.sign(endorsement_bytes);
    let signature_bytes = signature.to_der();

    let verification_time = oak_time::make_instant!("2026-07-13T12:00:00Z");
    let result = AuthorizedEndorsement::verify_and_parse(
        endorsement_bytes,
        signature_bytes.as_bytes(),
        &public_key_pem,
        verification_time,
    );
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("endorsement is not yet valid"));
}

#[test]
fn test_verify_and_parse_invalid_signature_fails() {
    let (signing_key, public_key_pem) = create_test_keys();

    let endorsement_json = r#"{
        "_type": "https://in-toto.io/Statement/v1",
        "subject": [],
        "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
        "predicate": {
            "issuedOn": "2026-07-14T12:00:00Z",
            "validity": { "notBefore": "2026-07-14T12:00:00Z", "notAfter": "2026-07-21T12:00:00Z" }
        }
    }"#;
    let endorsement_bytes = endorsement_json.as_bytes();
    let signature: Signature = signing_key.sign(b"tampered payload");
    let signature_bytes = signature.to_der();

    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let result = AuthorizedEndorsement::verify_and_parse(
        endorsement_bytes,
        signature_bytes.as_bytes(),
        &public_key_pem,
        verification_time,
    );
    assert!(result.is_err());
}

#[test]
fn test_verify_and_parse_wrong_predicate_type_fails() {
    let (signing_key, public_key_pem) = create_test_keys();

    let endorsement_json = r#"{
        "_type": "https://in-toto.io/Statement/v1",
        "subject": [],
        "predicateType": "https://example.com/custom/v1",
        "predicate": {
            "issuedOn": "2026-07-14T12:00:00Z",
            "validity": { "notBefore": "2026-07-14T12:00:00Z", "notAfter": "2026-07-21T12:00:00Z" }
        }
    }"#;
    let endorsement_bytes = endorsement_json.as_bytes();
    let signature: Signature = signing_key.sign(endorsement_bytes);
    let signature_bytes = signature.to_der();

    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let result = AuthorizedEndorsement::verify_and_parse(
        endorsement_bytes,
        signature_bytes.as_bytes(),
        &public_key_pem,
        verification_time,
    );
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("unsupported predicate type"));
}

#[test]
fn test_get_authorized_digests_partial_params_fails() {
    let params = AuthorizedWorkloadEndorsementParams {
        authorized_image_digests: None,
        authorized_endorsement_path: Some("/etc/proxy/endorsement.json".to_string()),
        authorized_endorsement_signature_path: None,
        authorized_endorsement_verifying_key_pem_path: None,
    };
    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let result = params.get_authorized_digests(verification_time);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("must all be specified together"));
}

#[test]
fn test_get_authorized_digests_merges_static_and_dynamic() {
    let dir = tempdir().unwrap();
    let (signing_key, public_key_pem) = create_test_keys();

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
                "notBefore": "2026-07-14T12:00:00Z",
                "notAfter": "2026-07-21T12:00:00Z"
            }}
        }}
    }}"#,
        hex::encode(b"endorsement_digest")
    );

    std::fs::write(&endorsement_path, endorsement_json.as_bytes()).unwrap();
    std::fs::write(&key_path, public_key_pem).unwrap();

    let signature: Signature = signing_key.sign(endorsement_json.as_bytes());
    std::fs::write(&sig_path, signature.to_der()).unwrap();

    let params = AuthorizedWorkloadEndorsementParams {
        authorized_image_digests: Some(vec![hex::encode(b"static_digest")]),
        authorized_endorsement_path: Some(endorsement_path.to_str().unwrap().to_string()),
        authorized_endorsement_signature_path: Some(sig_path.to_str().unwrap().to_string()),
        authorized_endorsement_verifying_key_pem_path: Some(key_path.to_str().unwrap().to_string()),
    };

    let verification_time = oak_time::make_instant!("2026-07-15T12:00:00Z");
    let digests = params.get_authorized_digests(verification_time).expect("failed to get digests");
    assert_eq!(digests.len(), 2);
    assert!(digests.contains(&b"static_digest".to_vec()));
    assert!(digests.contains(&b"endorsement_digest".to_vec()));
}
