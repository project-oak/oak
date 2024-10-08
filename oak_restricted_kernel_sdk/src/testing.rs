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
//

//! Mock attestation evidence and crypto logic. Useful for testing where an
//! attestation rooted in a real TEE may not be available.

use alloc::vec::Vec;

use oak_crypto::{
    encryption_key::{EncryptionKey, EncryptionKeyHandle},
    hpke::RecipientContext,
};
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, Stage0DiceData, TeePlatform};
use oak_proto_rust::oak::{
    attestation::v1::{ApplicationLayerData, EventLog},
    crypto::v1::Signature,
    RawDigest,
};
use p256::ecdsa::SigningKey;
use prost::Message;

use crate::{
    alloc::string::ToString,
    attestation::{DiceWrapper, EvidenceProvider},
    crypto::Signer,
};

lazy_static::lazy_static! {
  static ref MOCK_DICE_WRAPPER: anyhow::Result<DiceWrapper> = {
      let (dice_data, encoded_event_log) = get_mock_dice_data_and_event_log();
      let mut dice_wrapper: DiceWrapper = dice_data.try_into()?;
      dice_wrapper.encoded_event_log = Some(encoded_event_log);
      Ok(dice_wrapper)
  };
}

fn get_mock_dice_data_and_event_log() -> (RestrictedKernelDiceData, Vec<u8>) {
    let (mut mock_event_log, stage0_dice_data): (EventLog, Stage0DiceData) = {
        let stage0_event = oak_stage0_dice::encode_stage0_event(
            oak_proto_rust::oak::attestation::v1::Stage0Measurements::default(),
        );
        let mock_event_log = {
            let mut base = oak_proto_rust::oak::attestation::v1::EventLog::default();
            base.encoded_events.push(stage0_event.to_vec());
            base
        };
        let (stage0_dice_data, _) = oak_stage0_dice::generate_dice_data(
            oak_stage0_dice::mock_attestation_report,
            oak_stage0_dice::mock_derived_key,
            TeePlatform::None,
            &stage0_event,
        );
        (mock_event_log, stage0_dice_data)
    };

    let application_digest = oak_restricted_kernel_dice::DigestSha2_256::default();
    let config_digest = oak_restricted_kernel_dice::DigestSha2_256::default();
    let application_event = oak_proto_rust::oak::attestation::v1::Event {
        tag: "application_layer".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ApplicationLayerData".to_string(),
            value: ApplicationLayerData {
                binary: Some(RawDigest {
                    sha2_256: application_digest.to_vec(),
                    ..RawDigest::default()
                }),
                config: Some(RawDigest {
                    sha2_256: config_digest.to_vec(),
                    ..RawDigest::default()
                }),
            }
            .encode_to_vec(),
        }),
    };
    let encoded_application_event = application_event.encode_to_vec();
    mock_event_log.encoded_events.push(encoded_application_event.clone());
    let dice_data = oak_restricted_kernel_dice::generate_dice_data(
        stage0_dice_data,
        &oak_restricted_kernel_dice::DigestSha2_256::default(),
        &oak_restricted_kernel_dice::measure_digest_sha2_256(&encoded_application_event),
    );
    (dice_data, mock_event_log.encode_to_vec())
}

/// [`Signer`] implementation that using mock evidence and corresponding mock
/// private keys.
#[derive(Clone)]
pub struct MockSigner {
    key: &'static SigningKey,
}

impl MockSigner {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .map(|d| MockSigner { key: &d.signing_key })
    }
}

impl Signer for MockSigner {
    fn sign(&self, message: &[u8]) -> anyhow::Result<Signature> {
        Ok(Signature {
            signature: <SigningKey as oak_crypto::signer::Signer>::sign(self.key, message),
        })
    }
}

/// [`EncryptionKeyHandle`] implementation that using mock evidence and
/// corresponding mock private keys.
#[derive(Clone)]
pub struct MockEncryptionKeyHandle {
    key: &'static EncryptionKey,
}

impl MockEncryptionKeyHandle {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .map(|d| MockEncryptionKeyHandle { key: &d.encryption_key })
    }
}

impl EncryptionKeyHandle for MockEncryptionKeyHandle {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        self.key.generate_recipient_context(encapsulated_public_key)
    }
}

/// [`EvidenceProvider`] implementation that exposes mock evidence.
pub struct MockEvidenceProvider {
    evidence: &'static Evidence,
    encoded_event_log: &'static [u8],
}

impl MockEvidenceProvider {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER.as_ref().map_err(anyhow::Error::msg).map(|d| MockEvidenceProvider {
            evidence: &d.evidence,
            encoded_event_log: &d
                .encoded_event_log
                .as_ref()
                .expect("mock dice wrapper contains event log"),
        })
    }
}

impl EvidenceProvider for MockEvidenceProvider {
    fn get_evidence(&self) -> &Evidence {
        self.evidence
    }
    fn get_encoded_event_log(&self) -> Option<&[u8]> {
        Some(self.encoded_event_log)
    }
}
