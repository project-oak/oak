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

use oak_crypto::{
    encryption_key::{EncryptionKey, EncryptionKeyHandle},
    hpke::RecipientContext,
};
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, TeePlatform};
use oak_proto_rust::oak::crypto::v1::Signature;
use p256::ecdsa::SigningKey;

use crate::{
    attestation::{DiceWrapper, EvidenceProvider},
    crypto::Signer,
};

lazy_static::lazy_static! {
  static ref MOCK_DICE_WRAPPER: anyhow::Result<DiceWrapper> = {
      let dice_data = get_mock_dice_data();
      let dice_wrapper = dice_data.try_into()?;
      Ok(dice_wrapper)
  };
}

fn get_mock_dice_data() -> RestrictedKernelDiceData {
    let stage0_dice_data = oak_stage0_dice::generate_dice_data(
        &oak_stage0_dice::Measurements::default(),
        oak_stage0_dice::mock_attestation_report,
        oak_stage0_dice::mock_derived_key,
        TeePlatform::None,
    );

    oak_restricted_kernel_dice::generate_dice_data(
        stage0_dice_data,
        &oak_restricted_kernel_dice::AppDigestSha2_256::default(),
    )
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
        Ok(<SigningKey as oak_crypto::signer::Signer>::sign(self.key, message))
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
}

impl MockEvidenceProvider {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .map(|d| MockEvidenceProvider { evidence: &d.evidence })
    }
}

impl EvidenceProvider for MockEvidenceProvider {
    fn get_evidence(&self) -> &Evidence {
        self.evidence
    }
}
