//
// Copyright 2023 The Project Oak Authors
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

use chrono::Utc;
use hex;
use sha2::{Digest, Sha256};

pub fn generate_claim(
    model_name: &str,
    model_digest: &str,
    script_name: &str,
    script_digest: &str,
    result: &str,
) -> String {
    format!(
        r#"{{
            "_type": "https://in-toto.io/Statement/v0.1",
            "subject": [{{
                "name":"{}",
                "digest":{{"sha256":"{}"}}
            }}],
            "predicateType": "https://github.com/project-oak/transparent-release/schema/claim/v1",
            "predicate": {{
                "claimType": "https://github.com/project-oak/transparent-release/ml-eval/v0",
                "issuedOn": "{}",
                "claimSpec": {{
                    "script": {{
                        "name":"{}",
                        "digest":{{"sha256":"{}"}}
                    }},
                    "result": {}
                }}
            }}
        }}"#,
        model_name,
        model_digest,
        Utc::now().to_rfc3339(),
        script_name,
        script_digest,
        result
    )
}

/// Computes a SHA-256 digest of `input` and returns it as a hex-encoded string.
pub fn get_sha256_hex(input: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hex::encode::<[u8; 32]>(hasher.finalize().into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Result, Value};

    #[test]
    fn generate_claim_is_valid_json() {
        let claim = generate_claim(
            "mnist",
            "63ea4a9906dbbb3a154f069a0d4bc6a2272b9b8151e69fbd57029c826c2cd779",
            "eval.py",
            "bbfb80f90fb8ebc98f29ccc2a258ba88e712ab0ba754cc1749cb9e8413ac26b0",
            r#"{"acc": "80.9"}"#,
        );
        let v: Result<Value> = serde_json::from_str(&claim);
        assert!(v.is_ok());
    }

    #[test]
    fn get_sha256_hex_hello() {
        let got = get_sha256_hex(b"hello");
        let want = "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824";
        assert_eq!(want, got);
    }
}
