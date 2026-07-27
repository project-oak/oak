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

use oak_attestation::public_key::{PublicKeyAttester, PublicKeyEndorser};
use oak_attestation_gcp::{
    OAK_SESSION_NOISE_V1_AUDIENCE, attestation::request_attestation_token,
    policy_generator::confidential_space_policy_from_reference_values,
};
use oak_attestation_verification::EventLogVerifier;
use oak_proto_rust::{
    attestation::CONFIDENTIAL_SPACE_ATTESTATION_ID,
    oak::{
        RawDigest as CommonRawDigest,
        attestation::v1::{
            BinaryReferenceValue, ConfidentialSpaceEndorsement, ConfidentialSpaceReferenceValues,
            Digests, binary_reference_value, confidential_space_reference_values,
        },
    },
};
use oak_session::{
    config::SessionConfigBuilder, key_extractor::DefaultBindingKeyExtractor,
    session_binding::SignatureBinder,
};
use oak_time::Clock;
use p256::ecdsa::{SigningKey, VerifyingKey, signature::rand_core::OsRng};
use serde::{Deserialize, Serialize};
use sha2::Digest;

use super::authorized_endorsement::AuthorizedWorkloadEndorsementParams;

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
    pub container_reference_prefix: Option<String>,
    #[serde(flatten)]
    pub authorized_workload_endorsement: AuthorizedWorkloadEndorsementParams,
}

impl ConfidentialSpaceVerifierParams {
    pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
        let root_pem = std::fs::read_to_string(&self.root_certificate_pem_path)
            .expect("could not read root certificate");

        let clock = Arc::new(oak_time_std::clock::SystemTimeClock);
        let verification_time = clock.get_time();
        let allowed_digests =
            self.authorized_workload_endorsement.get_authorized_digests(verification_time)?;

        if self.container_reference_prefix.is_some() && !allowed_digests.is_empty() {
            anyhow::bail!(
                "cannot specify both container_reference_prefix and authorized_image_digests / authorized_endorsement_path: choose either prefix verification or exact digest authorization"
            );
        }

        let container_image = if !allowed_digests.is_empty() {
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
        } else {
            self.container_reference_prefix.clone().map(
                confidential_space_reference_values::ContainerImage::ContainerImageReferencePrefix,
            )
        };

        let reference_values =
            ConfidentialSpaceReferenceValues { root_certificate_pem: root_pem, container_image };
        let policy = confidential_space_policy_from_reference_values(&reference_values)?;
        let attestation_verifier = EventLogVerifier::new(
            vec![Box::new(policy)],
            // Use the current time for verifying endorsements.
            clock,
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
