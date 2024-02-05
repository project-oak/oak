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

//! Structs for signing and encryption using keys attested in the instance's attestation evidence.

use anyhow::Ok;
use oak_crypto::{
    encryptor::{EncryptionKeyHandle, EncryptionKeyProvider},
    hpke::RecipientContext,
};
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, P256_PRIVATE_KEY_SIZE};
use oak_restricted_kernel_interface::{syscall::read, DICE_DATA_FD};
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

use crate::{DiceWrapper, EvidenceProvider, Signer};

lazy_static::lazy_static! {
    static ref DICE_WRAPPER: anyhow::Result<DiceWrapper> = {
        let dice_data = get_restricted_kernel_dice_data()?;
        let dice_wrapper = dice_data.try_into()?;
        Ok(dice_wrapper)
    };
}

fn get_restricted_kernel_dice_data() -> anyhow::Result<RestrictedKernelDiceData> {
    let mut result = RestrictedKernelDiceData::new_zeroed();
    let buffer = result.as_bytes_mut();
    let len = read(DICE_DATA_FD, buffer).map_err(|err| anyhow::anyhow!("read failure: {err}"))?;
    if len != buffer.len() {
        anyhow::bail!("invalid dice data size");
    }
    Ok(result)
}

impl TryFrom<RestrictedKernelDiceData> for DiceWrapper {
    type Error = anyhow::Error;
    fn try_from(dice_data: RestrictedKernelDiceData) -> Result<Self, Self::Error> {
        let encryption_key = EncryptionKeyProvider::try_from(&dice_data)?;
        let signing_key = SigningKey::from_slice(
            &dice_data.application_private_keys.signing_private_key[..P256_PRIVATE_KEY_SIZE],
        )
        .map_err(|error| anyhow::anyhow!("couldn't deserialize signing key: {}", error))?;
        let evidence = dice_data.evidence;
        Ok(DiceWrapper {
            evidence,
            encryption_key,
            signing_key,
        })
    }
}

/// [`Signer`] implementation that using the instance's evidence and corresponding private keys.
#[derive(Clone)]
pub struct InstanceSigner {
    key: &'static SigningKey,
}

impl InstanceSigner {
    pub fn create() -> anyhow::Result<Self> {
        DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(InstanceSigner {
                    key: &d.signing_key,
                })
            })
    }
}

impl Signer for InstanceSigner {
    fn sign(&self, message: &[u8]) -> anyhow::Result<oak_crypto::signer::Signature> {
        Ok(<SigningKey as oak_crypto::signer::Signer>::sign(
            self.key, message,
        ))
    }
}

/// [`EncryptionKeyHandle`] implementation that using the instance's evidence and corresponding
/// private keys.
#[derive(Clone)]
pub struct InstanceEncryptionKeyHandle {
    key: &'static EncryptionKeyProvider,
}

impl InstanceEncryptionKeyHandle {
    pub fn create() -> anyhow::Result<Self> {
        DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(InstanceEncryptionKeyHandle {
                    key: &d.encryption_key,
                })
            })
    }
}

impl EncryptionKeyHandle for InstanceEncryptionKeyHandle {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        self.key.generate_recipient_context(encapsulated_public_key)
    }
}

/// [`EvidenceProvider`] implementation that exposes the instance's evidence.
pub struct InstanceEvidenceProvider {
    evidence: &'static Evidence,
}

impl InstanceEvidenceProvider {
    pub fn create() -> anyhow::Result<Self> {
        DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(InstanceEvidenceProvider {
                    evidence: &d.evidence,
                })
            })
    }
}

impl EvidenceProvider for InstanceEvidenceProvider {
    fn get_evidence(&self) -> &Evidence {
        self.evidence
    }
}
