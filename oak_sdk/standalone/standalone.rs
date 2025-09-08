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

//! The Oak Standalone SDK allows easy development iteration and testing for an
//! Oak-enabled trusted binary without requiring the entire Oak containers
//! stack.
//!
//! Oak Standalone supports setting up an encrypted channel based on randomly
//! generated public keys.
//!
//! It does not currently support any sort of attestation flow.

use anyhow::{Context, Result};
#[allow(deprecated)]
use oak_attestation::{dice::DiceAttester, ApplicationKeysAttester};
use oak_attestation_types::attester::Attester;
use oak_containers_attestation::{InstanceKeys, InstancePublicKeys};
use oak_crypto::encryption_key::{generate_encryption_key_pair, EncryptionKey};
use oak_dice::cert::generate_ecdsa_key_pair;
use oak_proto_rust::oak::{
    attestation::v1::{endorsements, AmdSevSnpEndorsement, Endorsements, Stage0Measurements},
    session::v1::EndorsedEvidence,
    Variant,
};
use oak_sdk_common::StaticEncryptionKeyHandle;
use p256::ecdsa::{SigningKey, VerifyingKey};
use prost::Message;

/// Default values for StandaloneOrchestrator to measure
const DEFAULT_STAGE1_SYSTEM_IMAGE: &[u8] = &[];
const DEFAULT_APPLICATION_IMAGE: &[u8] = &[];
const DEFAULT_APPLICATION_CONFIG: &[u8] = &[1, 2, 3, 4];

/// The components needed to run an Oak Standalone instance
pub struct Standalone {
    endorsed_evidence: EndorsedEvidence,
    encryption_key: EncryptionKey,
}

impl Standalone {
    fn new(endorsed_evidence: EndorsedEvidence, encryption_key: EncryptionKey) -> Self {
        Self { endorsed_evidence, encryption_key }
    }

    pub fn builder<'a>() -> StandaloneBuilder<'a> {
        StandaloneBuilder::new()
    }

    /// The EndorsedEvidence that the instance can use for attestation.
    pub fn endorsed_evidence(&self) -> EndorsedEvidence {
        self.endorsed_evidence.clone()
    }

    /// The encryption key that the application can use to construct a new
    /// server encryptor.
    pub fn encryption_key_handle(&self) -> StaticEncryptionKeyHandle {
        StaticEncryptionKeyHandle::new(self.encryption_key.clone())
    }
}

pub struct StandaloneBuilder<'a> {
    stage0_measurements: Stage0Measurements,
    stage1_system_image: &'a [u8],
    application_image: &'a [u8],
    application_config: Vec<u8>,
    encryption_key_pair: Option<(EncryptionKey, Vec<u8>)>,
    signing_key_pair: Option<(SigningKey, VerifyingKey)>,
    session_binding_key_pair: Option<(SigningKey, VerifyingKey)>,
}

macro_rules! builder_param {
    ($name:ident: $type:ty) => {
        pub fn $name(mut self, value: $type) -> StandaloneBuilder<'a> {
            self.$name = value;
            self
        }
    };
}

impl Default for StandaloneBuilder<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> StandaloneBuilder<'a> {
    pub fn build(self) -> Result<Standalone> {
        let encryption_key_pair = match self.encryption_key_pair {
            Some((public, private)) => (public, private),
            None => generate_encryption_key_pair(),
        };

        let signing_key_pair = match self.signing_key_pair {
            Some((public, private)) => (public, private),
            None => generate_ecdsa_key_pair(),
        };

        let session_binding_key_pair = match self.session_binding_key_pair {
            Some((public, private)) => (public, private),
            None => generate_ecdsa_key_pair(),
        };

        Self::create(
            self.stage0_measurements,
            self.stage1_system_image,
            self.application_image,
            self.application_config,
            encryption_key_pair,
            signing_key_pair,
            session_binding_key_pair,
        )
    }

    builder_param!(stage0_measurements: Stage0Measurements);
    builder_param!(stage1_system_image: &'a [u8]);
    builder_param!(application_image: &'a [u8]);
    builder_param!(application_config: Vec<u8>);
    builder_param!(encryption_key_pair: Option<(EncryptionKey, Vec<u8>)>);
    builder_param!(signing_key_pair: Option<(SigningKey, VerifyingKey)>);
    builder_param!(session_binding_key_pair: Option<(SigningKey, VerifyingKey)>);

    pub fn new() -> StandaloneBuilder<'a> {
        StandaloneBuilder {
            stage0_measurements: oak_proto_rust::oak::attestation::v1::Stage0Measurements::default(
            ),
            stage1_system_image: DEFAULT_STAGE1_SYSTEM_IMAGE,
            application_image: DEFAULT_APPLICATION_IMAGE,
            application_config: DEFAULT_APPLICATION_CONFIG.to_vec(),
            encryption_key_pair: None,
            signing_key_pair: None,
            session_binding_key_pair: None,
        }
    }

    fn create(
        root_layer_event: oak_proto_rust::oak::attestation::v1::Stage0Measurements,
        stage1_system_image: &[u8],
        application_image: &[u8],
        application_config: Vec<u8>,
        encryption_key_pair: (EncryptionKey, Vec<u8>),
        signing_key_pair: (SigningKey, VerifyingKey),
        session_binding_key_pair: (SigningKey, VerifyingKey),
    ) -> Result<Standalone> {
        let (encryption_key, encryption_public_key) = encryption_key_pair;
        let (signing_key, signing_public_key) = signing_key_pair;
        let (session_binding_key, session_binding_public_key) = session_binding_key_pair;

        let instance_private_keys =
            InstanceKeys { encryption_key, signing_key, session_binding_key };
        let instance_public_keys = InstancePublicKeys {
            encryption_public_key,
            signing_public_key,
            session_binding_public_key,
        };

        // Generate the root layer (Stage0) event
        let encoded_stage0_event = oak_stage0_dice::encode_stage0_event(root_layer_event.clone());

        // Create a mock event log with the root layer event
        let mut mock_event_log = oak_proto_rust::oak::attestation::v1::EventLog::default();
        mock_event_log.encoded_events.push(encoded_stage0_event.to_vec());

        // Create a DICE attester from the mock Stage0 data
        let mut attester: DiceAttester = oak_stage0_dice::generate_initial_dice_data(
            oak_stage0_dice::mock_attestation_report,
            oak_dice::evidence::TeePlatform::None,
        )
        .map_err(|e| anyhow::anyhow!("couldn't create initial DICE data: {e}"))?
        .try_into()
        .context("couldn't convert dice data to an attester")?;

        attester.extend(&encoded_stage0_event).context("couldn't extend attester evidence")?;

        // Add Stage1 event.
        let stage1_event =
            oak_containers_attestation::create_system_layer_event(stage1_system_image);
        attester
            .extend(&stage1_event.encode_to_vec())
            .context("couldn't add system event to the evidence")?;

        // Add container event and add it to the event log.
        let container_event = oak_containers_attestation::create_container_event(
            application_image,
            &application_config[..],
            &instance_public_keys,
        );
        attester
            .extend(&container_event.encode_to_vec())
            .context("couldn't add container event to the evidence")?;

        // Add container DICE layer data.
        let container_layer =
            oak_containers_attestation::create_container_dice_layer(&container_event);

        // Add application keys and generate the final evidence.
        #[allow(deprecated)]
        let evidence = attester.add_application_keys(
            container_layer,
            &instance_public_keys.encryption_public_key,
            &instance_public_keys.signing_public_key,
            None,
            None,
        )?;

        Ok(Standalone::new(EndorsedEvidence {
            evidence: Some(evidence),
            endorsements: Some(Endorsements {
                r#type: Some(endorsements::Type::OakContainers(
                    oak_proto_rust::oak::attestation::v1::OakContainersEndorsements {
                        root_layer: Some(
                            oak_proto_rust::oak::attestation::v1::RootLayerEndorsements::default(),
                        ),
                        ..Default::default()
                    },
                )),
                platform: Some(AmdSevSnpEndorsement::default().into()),
                events: vec![Variant::default(), Variant::default(), Variant::default()],
                ..Default::default()
            }),
        }, instance_private_keys.encryption_key))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oak_attestation_verification::{
        ContainerPolicy, InsecureAttestationVerifier, KernelPolicy, SystemPolicy,
    };
    use oak_attestation_verification_results::unique_signing_public_key;
    use oak_attestation_verification_types::verifier::AttestationVerifier;
    use oak_proto_rust::oak::attestation::v1::{
        attestation_results, binary_reference_value, kernel_binary_reference_value,
        text_reference_value, BinaryReferenceValue, ContainerLayerReferenceValues,
        KernelBinaryReferenceValue, KernelLayerReferenceValues, SkipVerification,
        SystemLayerReferenceValues, TextReferenceValue,
    };
    use oak_time_std::clock::SystemTimeClock;

    use super::*;

    #[test]
    fn test_standalone_evidence_verification() {
        let endorsed_evidence = Standalone::builder().build().unwrap().endorsed_evidence();
        let verifier = InsecureAttestationVerifier::new(
            Arc::new(SystemTimeClock {}),
            vec![
                Box::new(KernelPolicy::new(&KernelLayerReferenceValues {
                    kernel: Some(KernelBinaryReferenceValue {
                        r#type: Some(kernel_binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                    kernel_cmd_line_text: Some(TextReferenceValue {
                        r#type: Some(text_reference_value::Type::Skip(SkipVerification::default())),
                    }),
                    init_ram_fs: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                    memory_map: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                    acpi: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                })),
                Box::new(SystemPolicy::new(&SystemLayerReferenceValues {
                    system_image: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                })),
                Box::new(ContainerPolicy::new(&ContainerLayerReferenceValues {
                    binary: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                    configuration: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Skip(
                            SkipVerification::default(),
                        )),
                    }),
                })),
            ],
        );
        let results = verifier
            .verify(
                &endorsed_evidence.evidence.expect("missing evidence"),
                &endorsed_evidence.endorsements.expect("missing endorsements"),
            )
            .expect("attestation verification failed");
        assert_eq!(results.status, attestation_results::Status::Success as i32);
        unique_signing_public_key(&results).expect("missing signing public key");
    }
}
