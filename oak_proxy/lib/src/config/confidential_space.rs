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
    attestation::request_attestation_token,
    policy_generator::confidential_space_policy_from_reference_values,
    CONFIDENTIAL_SPACE_ATTESTATION_ID,
};
use oak_attestation_verification::EventLogVerifier;
use oak_proto_rust::oak::attestation::v1::{
    ConfidentialSpaceEndorsement, ConfidentialSpaceReferenceValues,
};
use oak_session::{
    config::SessionConfigBuilder, key_extractor::DefaultBindingKeyExtractor,
    session_binding::SignatureBinder,
};
use p256::ecdsa::{signature::rand_core::OsRng, SigningKey, VerifyingKey};
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
            request_attestation_token("oak://session/attestation", public_key_hash.as_str())?;

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
}

impl ConfidentialSpaceVerifierParams {
    pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
        let root_pem = std::fs::read_to_string(&self.root_certificate_pem_path)
            .expect("could not read root certificate");

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem: root_pem,
            r#container_image: None,
        };
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
