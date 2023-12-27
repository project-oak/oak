//
// Copyright 2023 The Project Oak Authors
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

use anyhow::Ok;
use oak_crypto::encryptor::{EncryptionKeyProvider, RecipientContextGenerator};
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, P256_PRIVATE_KEY_SIZE};
use oak_restricted_kernel_interface::{syscall::read, DICE_DATA_FD};
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

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

#[cfg(feature = "mock_attestion")]
lazy_static::lazy_static! {
    static ref MOCK_DICE_WRAPPER: anyhow::Result<DiceWrapper> = {
        let dice_data = get_mock_dice_data();
        let dice_wrapper = dice_data.try_into()?;
        Ok(dice_wrapper)
    };
}

#[cfg(feature = "mock_attestion")]
fn get_mock_dice_data() -> RestrictedKernelDiceData {
    let stage0_dice_data = oak_stage0_dice::generate_dice_data(
        &oak_stage0_dice::Measurements::default(),
        oak_stage0_dice::mock_attestation_report,
    );

    oak_restricted_kernel_dice::generate_dice_data(stage0_dice_data, &[])
}

/// Wrapper for DICE evidence and application private keys.
struct DiceWrapper {
    pub evidence: Evidence,
    pub encryption_key: EncryptionKeyProvider,
    pub signing_key: p256::ecdsa::SigningKey,
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

/// Defines the origin of the key that should be used.
pub enum KeyOrigin {
    /// Describes the key originating in the hardware of the current TEE.
    Instance,
    /// Use a key that is shared across enclaves executing the same task.
    /// Not yet supported on the restricted kernel.
    Group,
    #[cfg(feature = "mock_attestion")]
    Mock,
}

#[derive(core::marker::Copy, Clone)]
pub struct Signer {
    key: &'static SigningKey,
}

impl Signer {
    pub fn create(key_origin: KeyOrigin) -> anyhow::Result<Self> {
        match key_origin {
            KeyOrigin::Instance => {
                DICE_WRAPPER
                    .as_ref()
                    .map_err(anyhow::Error::msg)
                    .and_then(|d| {
                        Ok(Signer {
                            key: &d.signing_key,
                        })
                    })
            }
            KeyOrigin::Group => Err(anyhow::Error::msg(
                "Group keys are not yet implemented for the restricted kernel.",
            )),
            #[cfg(feature = "mock_attestion")]
            KeyOrigin::Mock => MOCK_DICE_WRAPPER
                .as_ref()
                .map_err(anyhow::Error::msg)
                .and_then(|d| {
                    Ok(Signer {
                        key: &d.signing_key,
                    })
                }),
        }
    }
    pub fn sign(&self, message: &[u8]) -> oak_crypto::signer::Signature {
        <SigningKey as oak_crypto::signer::Signer>::sign(self.key, message)
    }
}

#[derive(core::marker::Copy, Clone)]
pub struct EncryptionKeyHandle {
    key: &'static EncryptionKeyProvider,
}

impl EncryptionKeyHandle {
    pub fn create(key_origin: KeyOrigin) -> anyhow::Result<Self> {
        match key_origin {
            KeyOrigin::Instance => {
                DICE_WRAPPER
                    .as_ref()
                    .map_err(anyhow::Error::msg)
                    .and_then(|d| {
                        Ok(EncryptionKeyHandle {
                            key: &d.encryption_key,
                        })
                    })
            }
            KeyOrigin::Group => Err(anyhow::Error::msg(
                "Group keys are not yet implemented for the restricted kernel.",
            )),
            #[cfg(feature = "mock_attestion")]
            KeyOrigin::Mock => MOCK_DICE_WRAPPER
                .as_ref()
                .map_err(anyhow::Error::msg)
                .and_then(|d| {
                    Ok(EncryptionKeyHandle {
                        key: &d.encryption_key,
                    })
                }),
        }
    }
}

impl RecipientContextGenerator for EncryptionKeyHandle {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<oak_crypto::hpke::RecipientContext> {
        self.key.generate_recipient_context(encapsulated_public_key)
    }
}

pub struct Attester {
    evidence: &'static Evidence,
}

impl Attester {
    pub fn create(key_origin: KeyOrigin) -> anyhow::Result<Self> {
        match key_origin {
            KeyOrigin::Instance => {
                DICE_WRAPPER
                    .as_ref()
                    .map_err(anyhow::Error::msg)
                    .and_then(|d| {
                        Ok(Attester {
                            evidence: &d.evidence,
                        })
                    })
            }
            KeyOrigin::Group => Err(anyhow::Error::msg(
                "Group evidence is not yet implemented for the restricted kernel.",
            )),
            #[cfg(feature = "mock_attestion")]
            KeyOrigin::Mock => MOCK_DICE_WRAPPER
                .as_ref()
                .map_err(anyhow::Error::msg)
                .and_then(|d| {
                    Ok(Attester {
                        evidence: &d.evidence,
                    })
                }),
        }
    }
    /// Get the attestation evidence of the current enclave.
    pub fn get_evidence(&self) -> &Evidence {
        self.evidence
    }
}
