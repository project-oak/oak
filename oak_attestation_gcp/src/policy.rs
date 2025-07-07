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

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
};

use anyhow::Context;
use jwt::Token;
use oak_attestation_verification::{decode_event_proto, policy::SESSION_BINDING_PUBLIC_KEY_ID};
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    attestation::v1::{
        ConfidentialSpaceEndorsement, EventAttestationResults, SessionBindingPublicKeyData,
    },
    Variant,
};
use oak_time::Instant;
use serde::Deserialize;
use serde_json::Value;
use sha2::Digest;
use x509_cert::Certificate;

use crate::{jwt::Header, verification::verify_attestation_token};

// Private claim field in Confidential Space attestation tokens with
// the attestation nonce.
// https://cloud.google.com/confidential-computing/confidential-space/docs/connect-external-resources#attestation_token_structure
const EAT_NONCE: &str = "eat_nonce";

pub struct ConfidentialSpacePolicy {
    root_certificate: Certificate,
}

impl ConfidentialSpacePolicy {
    pub fn new(root_certificate: Certificate) -> Self {
        Self { root_certificate }
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl Policy<[u8]> for ConfidentialSpacePolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let public_key_data = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            evidence,
        )?;

        let endorsement =
            <&Variant as TryInto<Option<ConfidentialSpaceEndorsement>>>::try_into(endorsement)
                .map_err(anyhow::Error::msg)?
                .context("confidential space endorsement is not present")?;

        let public_key_hash = sha2::Sha256::digest(&public_key_data.session_binding_public_key);
        let public_key_hash = hex::encode(public_key_hash);

        let token: Token<Header, Value, _> = Token::parse_unverified(&endorsement.jwt_token)?;
        let token = verify_attestation_token(token, &self.root_certificate, &verification_time)?;
        let claims = token.claims();

        // We expect only one nonce, therefore a scalar string rather than an array.
        let eat_nonce: String = String::deserialize(&claims[EAT_NONCE])?;
        anyhow::ensure!(
            eat_nonce == public_key_hash,
            "nonce mismatch: {public_key_hash} != {eat_nonce}"
        );

        // TODO: b/426463266 - Verify claims about the platform/container

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults {
            artifacts: BTreeMap::from([(
                SESSION_BINDING_PUBLIC_KEY_ID.to_string(),
                public_key_data.session_binding_public_key.to_vec(),
            )]),
        })
    }
}

#[cfg(test)]
mod tests {
    use oak_proto_rust::oak::attestation::v1::Event;
    use prost::Message;
    use x509_cert::{
        der::{self, DecodePem},
        spki::DecodePublicKey,
    };

    use super::*;

    #[test]
    fn confidential_space_policy_verify_succeeds() {
        // The time has been set inside the validity interval of the test token and the
        // root certificate.
        const TOKEN: &str = include_str!("../testdata/confidential_space_valid.jwt");
        const PUBLIC_KEY: &str = include_str!("../testdata/confidential_space_public_key.pem");
        const CONFIDENTIAL_SPACE_ROOT_CERT_PEM: &str =
            include_str!("../testdata/confidential_space_root.pem");

        let current_time: oak_time::Instant =
            time::macros::datetime!(2025-07-01 17:31:32 UTC).into();

        let public_key = der::Document::from_public_key_pem(PUBLIC_KEY).unwrap().to_vec();
        let event = create_public_key_event(&public_key);

        let endorsement = ConfidentialSpaceEndorsement { jwt_token: TOKEN.to_owned() };

        let root_cert = Certificate::from_pem(CONFIDENTIAL_SPACE_ROOT_CERT_PEM).unwrap();

        let policy = ConfidentialSpacePolicy::new(root_cert);
        let result = policy.verify(current_time, &event.encode_to_vec(), &endorsement.into());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    fn create_public_key_event(session_binding_public_key: &[u8]) -> Event {
        Event {
            tag: "session_binding_key".to_string(),
            event: Some(prost_types::Any {
                type_url: "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData"
                    .to_string(),
                value: SessionBindingPublicKeyData {
                    session_binding_public_key: session_binding_public_key.to_vec(),
                }
                .encode_to_vec(),
            }),
        }
    }
}
