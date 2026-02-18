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

use p256::{
    ecdsa::{signature::Signer, Signature, SigningKey},
    pkcs8::EncodePublicKey,
};
use tempfile::tempdir;

use crate::config::confidential_space::ConfidentialSpaceVerifierParams;

#[test]
fn test_get_allowed_digests_with_manual_list() {
    let dir = tempdir().unwrap();
    let root_cert_path = dir.path().join("root.pem");
    // We don't need to write the file content if we don't call apply(),
    // but the struct fields need to be valid strings.

    let params = ConfidentialSpaceVerifierParams {
        root_certificate_pem_path: root_cert_path.to_str().unwrap().to_string(),
        expected_image_digests: Some(vec![hex::encode(b"digest1"), hex::encode(b"digest2")]),
        signed_policy_path: None,
        policy_signature_path: None,
        policy_public_key_pem_path: None,
    };

    let digests = params.get_allowed_digests().expect("failed to get digests");
    assert_eq!(digests.len(), 2);
    // Digests are stored as Vec<u8> (decoded from hex) in get_allowed_digests
    // return
    assert!(digests.contains(&b"digest1".to_vec()));
    assert!(digests.contains(&b"digest2".to_vec()));
}

#[test]
fn test_get_allowed_digests_merging() {
    let dir = tempdir().unwrap();

    // Setup Policy
    let mut rng = rand::thread_rng();
    let signing_key = SigningKey::random(&mut rng);
    let verifying_key = signing_key.verifying_key();
    let public_key_pem = verifying_key.to_public_key_pem(Default::default()).unwrap();

    let policy_path = dir.path().join("policy.json");
    let sig_path = dir.path().join("policy.sig");
    let key_path = dir.path().join("key.pem");

    let policy_json = format!(
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
        "predicateType": "custom",
        "predicate": {{}}
    }}"#,
        hex::encode(b"policy_digest")
    );

    std::fs::write(&policy_path, policy_json.as_bytes()).unwrap();
    std::fs::write(&key_path, public_key_pem).unwrap();

    let signature: Signature = signing_key.sign(policy_json.as_bytes());
    std::fs::write(&sig_path, signature.to_der()).unwrap();

    // Setup Params
    let params = ConfidentialSpaceVerifierParams {
        root_certificate_pem_path: "dummy.pem".to_string(),
        expected_image_digests: Some(vec![hex::encode(b"manual_digest")]),
        signed_policy_path: Some(policy_path.to_str().unwrap().to_string()),
        policy_signature_path: Some(sig_path.to_str().unwrap().to_string()),
        policy_public_key_pem_path: Some(key_path.to_str().unwrap().to_string()),
    };

    let digests = params.get_allowed_digests().expect("failed to get digests");
    assert_eq!(digests.len(), 2);
    assert!(digests.contains(&b"manual_digest".to_vec()));
    assert!(digests.contains(&b"policy_digest".to_vec()));
}
