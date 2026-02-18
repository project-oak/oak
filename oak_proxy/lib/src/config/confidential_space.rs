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

use std::sync::Arc;

use anyhow::Context;
use oak_attestation::public_key::{PublicKeyAttester, PublicKeyEndorser};
use oak_attestation_gcp::{
    OAK_SESSION_NOISE_V1_AUDIENCE, attestation::request_attestation_token,
    policy_generator::confidential_space_policy_from_reference_values,
};
use oak_attestation_verification::EventLogVerifier;
use oak_proto_rust::{
    attestation::CONFIDENTIAL_SPACE_ATTESTATION_ID,
    oak::{
        attestation::v1::{
            binary_reference_value, confidential_space_reference_values, BinaryReferenceValue,
            ConfidentialSpaceEndorsement, ConfidentialSpaceReferenceValues, Digests,
        },
        RawDigest as CommonRawDigest,
    },
};
use oak_session::{
    config::SessionConfigBuilder, key_extractor::DefaultBindingKeyExtractor,
    session_binding::SignatureBinder,
};
use p256::ecdsa::{SigningKey, VerifyingKey, signature::rand_core::OsRng};
use serde::{Deserialize, Serialize};
use sha2::Digest;

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct ConfidentialSpaceGeneratorParams {}

impl ConfidentialSpaceGeneratorParams {
    pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
        println!("Generating binding key...");
        let binding_key = SigningKey::random(&mut OsRng);
        let public_key_hash = sha2::Sha256::digest(binding_key.verifying_key().to_sec1_bytes());
        let public_key_hash = hex::encode(public_key_hash);

        println!("Requesting attestation token for {public_key_hash}...");
        let jwt_token =
            request_attestation_token(OAK_SESSION_NOISE_V1_AUDIENCE, public_key_hash.as_str())?;

        let public_key_attester = PublicKeyAttester::new(VerifyingKey::from(&binding_key));
        let public_key_endorser = PublicKeyEndorser::new(ConfidentialSpaceEndorsement {
            jwt_token,
            ..Default::default()
        });
        let public_key_binder = SignatureBinder::new(Box::new(binding_key));

        Ok(builder
            .add_self_attester(
                CONFIDENTIAL_SPACE_ATTESTATION_ID.to_owned(),
                Box::new(public_key_attester),
            )
            .add_self_endorser(
                CONFIDENTIAL_SPACE_ATTESTATION_ID.to_owned(),
                Box::new(public_key_endorser),
            )
            .add_session_binder(
                CONFIDENTIAL_SPACE_ATTESTATION_ID.to_owned(),
                Box::new(public_key_binder),
            ))
    }
}

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct ConfidentialSpaceVerifierParams {
    pub root_certificate_pem_path: String,
    pub expected_image_digests: Option<Vec<String>>,
    pub signed_policy_path: Option<String>,
    pub policy_signature_path: Option<String>,
    pub policy_public_key_pem_path: Option<String>,
}

impl ConfidentialSpaceVerifierParams {
    fn get_allowed_digests(&self) -> anyhow::Result<Vec<Vec<u8>>> {
        let mut allowed_digests = Vec::new();

        if let Some(digests) = &self.expected_image_digests {
            allowed_digests.extend(digests.clone());
        }

        if let (Some(policy_path), Some(sig_path), Some(key_path)) = (
            &self.signed_policy_path,
            &self.policy_signature_path,
            &self.policy_public_key_pem_path,
        ) {
            let policy = crate::config::signed_policy::SignedPolicy::load(
                std::path::Path::new(policy_path),
                std::path::Path::new(sig_path),
                std::path::Path::new(key_path),
            )?;
            allowed_digests.extend(policy.allowed_digests);
        }

        allowed_digests
            .into_iter()
            .map(|hex_digest| hex::decode(hex_digest).context("decoding hex digest"))
            .collect()
    }

    pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
        let root_pem = std::fs::read_to_string(&self.root_certificate_pem_path)
            .expect("could not read root certificate");

        let allowed_digests = self.get_allowed_digests()?;

        let container_image = if allowed_digests.is_empty() {
            None
        } else {
            let raw_digests: Vec<CommonRawDigest> = allowed_digests
                .into_iter()
                .map(|digest| CommonRawDigest { sha2_256: digest, ..Default::default() })
                .collect();

            let digests = Digests {
                #[allow(deprecated)]
                digests: raw_digests,
            };
            let binary_reference_value = BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Digests(digests)),
            };
            Some(confidential_space_reference_values::ContainerImage::ImageReferenceValue(
                binary_reference_value,
            ))
        };

        let reference_values =
            ConfidentialSpaceReferenceValues { root_certificate_pem: root_pem, container_image };
        let policy = confidential_space_policy_from_reference_values(&reference_values)?;
        let attestation_verifier = EventLogVerifier::new(
            vec![Box::new(policy)],
            // Use the current time for verifying endorsements.
            Arc::new(oak_time_std::clock::SystemTimeClock),
        );

        Ok(builder.add_peer_verifier_with_key_extractor(
            CONFIDENTIAL_SPACE_ATTESTATION_ID.to_string(),
            Box::new(attestation_verifier),
            Box::new(DefaultBindingKeyExtractor {}),
        ))
    }
}

#[cfg(test)]
#[path = "confidential_space_tests.rs"]
mod tests;
