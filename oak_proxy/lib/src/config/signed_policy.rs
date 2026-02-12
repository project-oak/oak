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

use std::{collections::HashMap, path::Path};

use anyhow::Context;
use p256::{
    ecdsa::{signature::Verifier, Signature, VerifyingKey},
    pkcs8::DecodePublicKey,
};
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct InTotoStatement {
    #[serde(rename = "subject")]
    subjects: Vec<InTotoSubject>,
}

#[derive(Deserialize, Debug)]
struct InTotoSubject {
    digest: HashMap<String, String>,
}

pub struct SignedPolicy {
    pub allowed_digests: Vec<String>,
}

impl SignedPolicy {
    pub fn load(
        policy_path: &Path,
        signature_path: &Path,
        public_key_pem_path: &Path,
    ) -> anyhow::Result<Self> {
        let policy_bytes = std::fs::read(policy_path).context("reading policy file")?;
        let signature_bytes = std::fs::read(signature_path).context("reading signature file")?;
        let public_key_pem =
            std::fs::read_to_string(public_key_pem_path).context("reading public key pem")?;

        Self::verify_and_parse(&policy_bytes, &signature_bytes, &public_key_pem)
    }

    fn verify_and_parse(
        policy_bytes: &[u8],
        signature_bytes: &[u8],
        public_key_pem: &str,
    ) -> anyhow::Result<Self> {
        // 1. Verify Signature
        Self::verify_signature(policy_bytes, signature_bytes, public_key_pem)
            .context("verifying policy signature")?;

        // 2. Parse Policy
        let statement: InTotoStatement =
            serde_json::from_slice(policy_bytes).context("parsing in-toto statement")?;

        // 3. Extract Digests
        let mut allowed_digests = Vec::new();
        for subject in statement.subjects {
            if let Some(sha256) = subject.digest.get("sha256") {
                allowed_digests.push(sha256.clone());
            }
        }

        Ok(Self { allowed_digests })
    }

    fn verify_signature(
        message: &[u8],
        signature_bytes: &[u8],
        public_key_pem: &str,
    ) -> anyhow::Result<()> {
        let verifying_key = VerifyingKey::from_public_key_pem(public_key_pem)
            .map_err(|e| anyhow::anyhow!("failed to parse public key pem: {}", e))?;

        let signature = Signature::from_der(signature_bytes)
            .map_err(|e| anyhow::anyhow!("invalid DER signature: {}", e))?;

        verifying_key
            .verify(message, &signature)
            .map_err(|e| anyhow::anyhow!("signature verification failed: {}", e))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use p256::{
        ecdsa::{signature::Signer, SigningKey},
        pkcs8::EncodePublicKey,
    };

    use super::*;

    #[test]
    fn test_verify_and_parse_valid() {
        let mut rng = rand::thread_rng();
        let signing_key = SigningKey::random(&mut rng);
        let verifying_key = signing_key.verifying_key();
        let public_key_pem = verifying_key.to_public_key_pem(Default::default()).unwrap();

        let policy_json = r#"{
            "_type": "https://in-toto.io/Statement/v1",
            "subject": [
                {
                    "name": "test",
                    "digest": {
                        "sha256": "aabbcc"
                    }
                }
            ],
            "predicateType": "custom",
            "predicate": {}
        }"#;
        let policy_bytes = policy_json.as_bytes();
        let signature: Signature = signing_key.sign(policy_bytes);
        let signature_bytes = signature.to_der();

        let policy = SignedPolicy::verify_and_parse(
            policy_bytes,
            signature_bytes.as_bytes(),
            &public_key_pem,
        )
        .expect("failed to verify and parse");

        assert_eq!(policy.allowed_digests, vec!["aabbcc"]);
    }

    #[test]
    fn test_verify_invalid_signature() {
        let mut rng = rand::thread_rng();
        let signing_key = SigningKey::random(&mut rng);
        let verifying_key = signing_key.verifying_key();
        let public_key_pem = verifying_key.to_public_key_pem(Default::default()).unwrap();

        let policy_json = r#"{}"#;
        let policy_bytes = policy_json.as_bytes();
        // Sign different data
        let signature: Signature = signing_key.sign(b"different data");
        let signature_bytes = signature.to_der();

        let result = SignedPolicy::verify_and_parse(
            policy_bytes,
            signature_bytes.as_bytes(),
            &public_key_pem,
        );
        assert!(result.is_err());
    }
}
