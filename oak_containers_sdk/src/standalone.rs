//
// Copyright 2024 The Project Oak Authors
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

use oak_crypto::{
    encryption_key::{generate_encryption_key_pair, AsyncEncryptionKeyHandle, EncryptionKey},
    hpke::RecipientContext,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        endorsements, ApplicationKeys, Endorsements, Evidence, OakStandaloneEndorsements,
        RootLayerEvidence, TeePlatform,
    },
    session::v1::EndorsedEvidence,
};

/// Create an [`EndorsedEvidence`] instance that your TEE application can use.
/// This can be provided in circumstances where you'd normally request an
/// [`EndorsedEvidence`] from the Orchestrator.
pub fn standalone_endorsed_evidence_containing_only_public_keys(
    public_key: impl Into<Vec<u8>>,
) -> EndorsedEvidence {
    // TODO: b/347970899 - Create mock events and dice data for the subsequent
    // layers.
    let (mock_event_log, mock_stage0_dice_data): (
        oak_proto_rust::oak::attestation::v1::EventLog,
        oak_dice::evidence::Stage0DiceData,
    ) = {
        let mut mock_stage0_measurements = oak_stage0_dice::Measurements::default();
        let (mock_event_log, stage0_event_sha2_256_digest) = oak_stage0_dice::generate_event_log(
            mock_stage0_measurements.kernel_sha2_256_digest.to_vec(),
            mock_stage0_measurements.acpi_sha2_256_digest.to_vec(),
            mock_stage0_measurements.memory_map_sha2_256_digest.to_vec(),
            mock_stage0_measurements.ram_disk_sha2_256_digest.to_vec(),
            mock_stage0_measurements.setup_data_sha2_256_digest.to_vec(),
            mock_stage0_measurements.cmdline.clone(),
        );
        mock_stage0_measurements.event_sha2_256_digest = stage0_event_sha2_256_digest;
        let (stage0_dice_data, _) = oak_stage0_dice::generate_dice_data(
            &mock_stage0_measurements,
            oak_stage0_dice::mock_attestation_report,
            oak_stage0_dice::mock_derived_key,
            oak_dice::evidence::TeePlatform::None,
            oak_proto_rust::oak::attestation::v1::EventLog::default(),
        );
        (mock_event_log, stage0_dice_data)
    };
    let mut attester = oak_containers_stage1_dice::stage0_dice_data_into_dice_attester(
        mock_stage0_dice_data,
        mock_event_log,
    )
    .expect("failed to create dice attester");
    let layer_data = oak_containers_stage1_dice::get_layer_data(&[]);
    attester.add_layer(layer_data).expect("failred to add stage1 layer data");

    EndorsedEvidence {
        evidence: Some(Evidence {
            // TODO: b/347970899 - Create something here that will be compatible with the
            // verification framework.
            root_layer: Some(RootLayerEvidence {
                platform: TeePlatform::None.into(),
                eca_public_key: vec![],
                remote_attestation_report: vec![],
            }),
            layers: vec![],
            application_keys: Some(ApplicationKeys {
                // TODO: b/347970899 - Store the public key in the format expected by
                // the attestation verification framework.
                encryption_public_key_certificate: public_key.into(),
                group_encryption_public_key_certificate: vec![],
                signing_public_key_certificate: vec![],
                group_signing_public_key_certificate: vec![],
            }),
            event_log: None,
        }),
        endorsements: Some(Endorsements {
            r#type: Some(endorsements::Type::Standalone(OakStandaloneEndorsements {})),
        }),
    }
}

/// A structure implementing [`AsyncEncryptionKeyHandle``] trait, which can be
/// provided to a TEE application instead of the normal orchestrator-driven
/// instance type.
pub struct StandaloneEncryptionKeyHandle {
    public_key: Vec<u8>,
    private_key: EncryptionKey,
}

impl StandaloneEncryptionKeyHandle {
    /// Generates a new public/private keypair and returns a new instance
    /// containing them.
    pub fn new(
        private_key: EncryptionKey,
        public_key: impl Into<Vec<u8>>,
    ) -> StandaloneEncryptionKeyHandle {
        Self { private_key, public_key: public_key.into() }
    }

    /// Return the public_key created on construction.
    pub fn public_key(&self) -> &[u8] {
        &self.public_key
    }
}

impl Default for StandaloneEncryptionKeyHandle {
    fn default() -> Self {
        let (private_key, public_key) = generate_encryption_key_pair();
        Self::new(private_key, public_key)
    }
}

#[async_trait::async_trait]
impl AsyncEncryptionKeyHandle for StandaloneEncryptionKeyHandle {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        self.private_key.generate_recipient_context(encapsulated_public_key).await
    }
}
