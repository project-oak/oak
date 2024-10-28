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

use anyhow::{Context, Result};
use async_trait::async_trait;
use oak_attestation::{attester::Attester, dice::DiceAttester};
use oak_containers_attestation::{InstanceKeys, InstancePublicKeys};
use oak_crypto::{
    encryption_key::{generate_encryption_key_pair, AsyncEncryptionKeyHandle, EncryptionKey},
    hpke::RecipientContext,
};
use oak_dice::cert::generate_ecdsa_key_pair;
use oak_proto_rust::oak::{
    attestation::v1::{endorsements, Endorsements, Evidence, Stage0Measurements},
    crypto::v1::Signature,
    session::v1::EndorsedEvidence,
};
use p256::ecdsa::{signature::Signer, SigningKey, VerifyingKey};

use crate::OrchestratorInterface;

/// Default values for StandaloneOrchestrator to measure
const DEFAULT_STAGE1_SYSTEM_IMAGE: &[u8] = &[];
const DEFAULT_APPLICATION_IMAGE: &[u8] = &[];
const DEFAULT_APPLICATION_CONFIG: &[u8] = &[1, 2, 3, 4];

/// A mock implementation of the OrchestratorInterface for standalone testing
pub struct StandaloneOrchestrator {
    instance_private_keys: oak_containers_attestation::InstanceKeys,
    evidence: Evidence,
    application_config: Vec<u8>,
}

pub struct KeyPair {
    pub private: InstanceKeys,
    pub public: InstancePublicKeys,
}

pub struct StandaloneOrchestratorBuilder<'a> {
    stage0_measurements: Stage0Measurements,
    stage1_system_image: &'a [u8],
    application_image: &'a [u8],
    application_config: Vec<u8>,
    encryption_key_pair: Option<(EncryptionKey, Vec<u8>)>,
    signing_key_pair: Option<(SigningKey, VerifyingKey)>,
}

macro_rules! builder_param {
    ($name:ident: $type:ty) => {
        pub fn $name(mut self, value: $type) -> StandaloneOrchestratorBuilder<'a> {
            self.$name = value;
            self
        }
    };
}

impl<'a> StandaloneOrchestratorBuilder<'a> {
    pub fn build(self) -> Result<StandaloneOrchestrator> {
        let encryption_key_pair = match self.encryption_key_pair {
            Some((public, private)) => (public, private),
            None => generate_encryption_key_pair(),
        };

        let signing_key_pair = match self.signing_key_pair {
            Some((public, private)) => (public, private),
            None => generate_ecdsa_key_pair(),
        };

        StandaloneOrchestrator::create(
            self.stage0_measurements,
            self.stage1_system_image,
            self.application_image,
            self.application_config,
            encryption_key_pair,
            signing_key_pair,
        )
    }

    builder_param!(stage0_measurements: Stage0Measurements);
    builder_param!(stage1_system_image: &'a [u8]);
    builder_param!(application_image: &'a [u8]);
    builder_param!(application_config: Vec<u8>);
    builder_param!(encryption_key_pair: Option<(EncryptionKey, Vec<u8>)>);
    builder_param!(signing_key_pair: Option<(SigningKey, VerifyingKey)>);
}

impl Default for StandaloneOrchestrator {
    fn default() -> Self {
        Self::builder().build().expect("Failed to create default StandaloneOrchestrator")
    }
}

impl StandaloneOrchestrator {
    pub fn builder<'a>() -> StandaloneOrchestratorBuilder<'a> {
        StandaloneOrchestratorBuilder {
            stage0_measurements: oak_proto_rust::oak::attestation::v1::Stage0Measurements::default(
            ),
            stage1_system_image: DEFAULT_STAGE1_SYSTEM_IMAGE,
            application_image: DEFAULT_APPLICATION_IMAGE,
            application_config: DEFAULT_APPLICATION_CONFIG.to_vec(),
            encryption_key_pair: None,
            signing_key_pair: None,
        }
    }

    pub fn create(
        root_layer_event: oak_proto_rust::oak::attestation::v1::Stage0Measurements,
        stage1_system_image: &[u8],
        application_image: &[u8],
        application_config: Vec<u8>,
        encryption_key_pair: (EncryptionKey, Vec<u8>),
        signing_key_pair: (SigningKey, VerifyingKey),
    ) -> Result<Self> {
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

        // Add Stage1 layer data
        let stage1_layer_data = oak_containers_stage1_dice::get_layer_data(stage1_system_image);
        attester.add_layer(stage1_layer_data)?;

        // Add Orchestrator layer data
        let orchestrator_layer_data = oak_containers_attestation::measure_container_and_config(
            application_image,
            &application_config,
        );

        // Add application keys and generate the final evidence
        let evidence = attester.add_application_keys(
            orchestrator_layer_data,
            &encryption_key_pair.1,
            &signing_key_pair.1,
            None,
            None,
        )?;

        let instance_private_keys =
            InstanceKeys { encryption_key: encryption_key_pair.0, signing_key: signing_key_pair.0 };

        Ok(Self { instance_private_keys, evidence, application_config })
    }

    pub fn get_instance_encryption_key_handle(&self) -> StandaloneInstanceEncryptionKeyHandle {
        StandaloneInstanceEncryptionKeyHandle {
            encryption_key: self.instance_private_keys.encryption_key.clone(),
        }
    }

    pub fn get_instance_signer(&self) -> StandaloneInstanceSigner {
        StandaloneInstanceSigner { signing_key: self.instance_private_keys.signing_key.clone() }
    }

    pub fn get_endorsed_evidence(&self) -> EndorsedEvidence {
        EndorsedEvidence {
            evidence: Some(self.evidence.clone()),
            endorsements: Some(Endorsements {
                r#type: Some(endorsements::Type::OakContainers(
                    oak_proto_rust::oak::attestation::v1::OakContainersEndorsements {
                        root_layer: Some(
                            oak_proto_rust::oak::attestation::v1::RootLayerEndorsements::default(),
                        ),
                        ..Default::default()
                    },
                )),
                // TODO: b/375137648 - Populate `event_endorsements` proto field.
                event_endorsements: None,
            }),
        }
    }
}

#[async_trait]
impl OrchestratorInterface for StandaloneOrchestrator {
    async fn get_application_config(&mut self) -> Result<Vec<u8>> {
        Ok(self.application_config.clone())
    }

    async fn notify_app_ready(&mut self) -> Result<()> {
        // In standalone mode, we don't need to notify anyone
        Ok(())
    }

    async fn get_endorsed_evidence(&mut self) -> Result<EndorsedEvidence> {
        Ok(StandaloneOrchestrator::get_endorsed_evidence(self))
    }
}

pub struct StandaloneInstanceEncryptionKeyHandle {
    encryption_key: EncryptionKey,
}

#[async_trait::async_trait]
impl AsyncEncryptionKeyHandle for StandaloneInstanceEncryptionKeyHandle {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        self.encryption_key.generate_recipient_context(encapsulated_public_key).await
    }
}

pub struct StandaloneInstanceSigner {
    signing_key: p256::ecdsa::SigningKey,
}

#[async_trait::async_trait(?Send)]
impl crate::crypto::Signer for StandaloneInstanceSigner {
    async fn sign(&self, message: &[u8]) -> anyhow::Result<Signature> {
        let signature: p256::ecdsa::Signature = self.signing_key.sign(message);
        Ok(Signature { signature: signature.to_vec() })
    }
}
