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

use std::{collections::HashMap, path::Path};

use anyhow::Context;
use oak_time::Instant;
use p256::{
    ecdsa::{Signature, VerifyingKey, signature::Verifier},
    pkcs8::DecodePublicKey,
};
use serde::{Deserialize, Serialize};

const IN_TOTO_STATEMENT_V1: &str = "https://in-toto.io/Statement/v1";
const ENDORSEMENT_PREDICATE_TYPE_V1: &str = "https://project-oak.github.io/oak/tr/endorsement/v1";

/// Claim type specifically for Confidential Space container image endorsements.
pub const CLAIM_TYPE_CONFIDENTIAL_SPACE_IMAGE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/13420.md";

/// Parameters for configuring operator-authorized workload digests and signed
/// deployment endorsements.
///
/// For schema details on `authorized_endorsement_path` and `endorsement/v1`
/// statements, see <https://project-oak.github.io/oak/tr/endorsement/v1> and
/// <https://github.com/project-oak/oak/blob/main/docs/tr/endorsement_v1.md>.
#[derive(Deserialize, Serialize, Debug, Clone, Default, PartialEq, Eq)]
pub struct AuthorizedWorkloadEndorsementParams {
    pub authorized_image_digests: Option<Vec<String>>,
    pub authorized_endorsement_path: Option<String>,
    pub authorized_endorsement_signature_path: Option<String>,
    pub authorized_endorsement_verifying_key_pem_path: Option<String>,
}

impl AuthorizedWorkloadEndorsementParams {
    /// Collects and returns all authorized sha256 digests (`Vec<u8>`) from both
    /// static allowlists (`authorized_image_digests`) and dynamic operator
    /// deployment endorsements (`authorized_endorsement_path`).
    pub fn get_authorized_digests(
        &self,
        verification_time: Instant,
    ) -> anyhow::Result<Vec<Vec<u8>>> {
        let mut allowed_digests = Vec::new();

        if let Some(digests) = &self.authorized_image_digests {
            allowed_digests.extend(digests.clone());
        }

        match (
            &self.authorized_endorsement_path,
            &self.authorized_endorsement_signature_path,
            &self.authorized_endorsement_verifying_key_pem_path,
        ) {
            (Some(endorsement_path), Some(sig_path), Some(key_path)) => {
                let endorsement = AuthorizedEndorsement::load(
                    Path::new(endorsement_path),
                    Path::new(sig_path),
                    Path::new(key_path),
                    verification_time,
                )?;
                allowed_digests.extend(endorsement.authorized_digests);
            }
            (None, None, None) => {}
            _ => {
                anyhow::bail!(
                    "authorized_endorsement_path, authorized_endorsement_signature_path, and authorized_endorsement_verifying_key_pem_path must all be specified together when loading a dynamic endorsement"
                );
            }
        }

        allowed_digests
            .into_iter()
            .map(|hex_digest| hex::decode(hex_digest).context("decoding hex digest"))
            .collect()
    }
}

#[derive(Deserialize, Debug)]
struct EndorsementStatement {
    #[serde(rename = "_type")]
    statement_type: String,
    #[serde(rename = "predicateType")]
    predicate_type: String,
    subject: Vec<EndorsementSubject>,
    predicate: EndorsementPredicate,
}

#[derive(Deserialize, Debug)]
struct EndorsementSubject {
    #[serde(default)]
    #[allow(dead_code)]
    name: Option<String>,
    digest: HashMap<String, String>,
}

#[derive(Deserialize, Debug)]
struct EndorsementPredicate {
    #[serde(rename = "issuedOn", with = "oak_time::instant::rfc3339")]
    #[allow(dead_code)]
    issued_on: Instant,
    validity: EndorsementValidity,
    #[serde(default)]
    #[allow(dead_code)]
    claims: Option<Vec<EndorsementClaim>>,
}

#[derive(Deserialize, Debug)]
struct EndorsementValidity {
    #[serde(rename = "notBefore", with = "oak_time::instant::rfc3339")]
    not_before: Instant,
    #[serde(rename = "notAfter", with = "oak_time::instant::rfc3339")]
    not_after: Instant,
}

#[derive(Deserialize, Debug)]
struct EndorsementClaim {
    #[allow(dead_code)]
    r#type: String,
}

/// Operator deployment authorization endorsement loaded from disk and verified
/// against a public key.
///
/// For schema and specification details, see <https://project-oak.github.io/oak/tr/endorsement/v1>
/// and <https://github.com/project-oak/oak/blob/main/docs/tr/endorsement_v1.md>.
/// For Confidential Space container claim representations, see
/// <https://github.com/project-oak/oak/blob/main/docs/tr/claim/confidential_space_image.md>.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorizedEndorsement {
    pub authorized_digests: Vec<String>,
}

impl AuthorizedEndorsement {
    /// Loads, verifies, and parses a signed operator deployment endorsement
    /// from disk.
    pub fn load(
        endorsement_path: &Path,
        signature_path: &Path,
        public_key_pem_path: &Path,
        verification_time: Instant,
    ) -> anyhow::Result<Self> {
        let endorsement_bytes =
            std::fs::read(endorsement_path).context("reading endorsement file")?;
        let signature_bytes = std::fs::read(signature_path).context("reading signature file")?;
        let public_key_pem =
            std::fs::read_to_string(public_key_pem_path).context("reading public key pem")?;

        Self::verify_and_parse(
            &endorsement_bytes,
            &signature_bytes,
            &public_key_pem,
            verification_time,
        )
    }

    /// Verifies the cryptographic signature over the endorsement bytes and
    /// parses the allowlist.
    ///
    /// Enforces that `notBefore <= verification_time <= notAfter`.
    pub fn verify_and_parse(
        endorsement_bytes: &[u8],
        signature_bytes: &[u8],
        public_key_pem: &str,
        verification_time: Instant,
    ) -> anyhow::Result<Self> {
        Self::verify_signature(endorsement_bytes, signature_bytes, public_key_pem)
            .context("verifying endorsement signature")?;

        let statement: EndorsementStatement = serde_json::from_slice(endorsement_bytes)
            .context("parsing in-toto endorsement statement")?;

        anyhow::ensure!(
            statement.statement_type == IN_TOTO_STATEMENT_V1,
            "unsupported statement type: expected {}, found {}",
            IN_TOTO_STATEMENT_V1,
            statement.statement_type
        );
        anyhow::ensure!(
            statement.predicate_type == ENDORSEMENT_PREDICATE_TYPE_V1,
            "unsupported predicate type: expected {}, found {}",
            ENDORSEMENT_PREDICATE_TYPE_V1,
            statement.predicate_type
        );

        anyhow::ensure!(
            verification_time >= statement.predicate.validity.not_before,
            "endorsement is not yet valid: verification time is before notBefore"
        );
        anyhow::ensure!(
            verification_time <= statement.predicate.validity.not_after,
            "endorsement has expired: verification time is after notAfter"
        );

        let mut authorized_digests = Vec::new();
        for subject in statement.subject {
            if let Some(sha256) = subject.digest.get("sha256") {
                authorized_digests.push(sha256.clone());
            }
        }

        Ok(Self { authorized_digests })
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
#[path = "authorized_endorsement_tests.rs"]
mod tests;
