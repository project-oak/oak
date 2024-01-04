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
pub use oak_crypto::encryptor::EncryptionKeyHandle;
use oak_crypto::{
    encryptor::{EncryptionKeyProvider, RecipientContextGenerator},
    hpke::RecipientContext as SessionKeys,
};
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, P256_PRIVATE_KEY_SIZE};
use oak_restricted_kernel_interface::{syscall::read, DICE_DATA_FD};
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

/// Sign the provided message bytestring using a signing private key, a
/// corresponding public key of which is contained in the Attestation Evidence.
pub trait Signer {
    /// Attempt to sign the provided message bytestring using a signing private key, a
    /// corresponding public key of which is contained in the Attestation Evidence.
    fn sign(&self, message: &[u8]) -> anyhow::Result<oak_crypto::signer::Signature>;
}

/// Exposes the ability to read the Attestation Evidence. It is discouraged for enclave applications
/// to operate with evidences. The evidence should only be used to forward it to the host
/// application once, which then sends it to the clients.
pub trait Evidencer {
    fn get_evidence(&self) -> &Evidence;
}

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

#[cfg(feature = "mock_attestion")]
/// [`Signer`] implementation that using mock evidence and corresponding mock private keys.
#[derive(Clone)]
pub struct MockSigner {
    key: &'static SigningKey,
}
#[cfg(feature = "mock_attestion")]
impl MockSigner {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(MockSigner {
                    key: &d.signing_key,
                })
            })
    }
}
#[cfg(feature = "mock_attestion")]
impl Signer for MockSigner {
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
    fn generate_session_keys(&self, encapsulated_public_key: &[u8]) -> anyhow::Result<SessionKeys> {
        self.key.generate_recipient_context(encapsulated_public_key)
    }
}

#[cfg(feature = "mock_attestion")]
/// [`EncryptionKeyHandle`] implementation that using mock evidence and corresponding mock
/// private keys.
#[derive(Clone)]
pub struct MockEncryptionKeyHandle {
    key: &'static EncryptionKeyProvider,
}

#[cfg(feature = "mock_attestion")]
impl MockEncryptionKeyHandle {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(MockEncryptionKeyHandle {
                    key: &d.encryption_key,
                })
            })
    }
}

#[cfg(feature = "mock_attestion")]
impl RecipientContextGenerator for MockEncryptionKeyHandle {
    fn generate_session_keys(&self, encapsulated_public_key: &[u8]) -> anyhow::Result<SessionKeys> {
        self.key.generate_recipient_context(encapsulated_public_key)
    }
}

/// [`Evidencer`] implementation that exposes the instance's evidence.
pub struct InstanceEvidencer {
    evidence: &'static Evidence,
}

impl InstanceEvidencer {
    pub fn create() -> anyhow::Result<Self> {
        DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(InstanceEvidencer {
                    evidence: &d.evidence,
                })
            })
    }
}

impl Evidencer for InstanceEvidencer {
    fn get_evidence(&self) -> &Evidence {
        self.evidence
    }
}

/// [`Evidencer`] implementation that exposes mock evidence.
#[cfg(feature = "mock_attestion")]
pub struct MockEvidencer {
    evidence: &'static Evidence,
}

#[cfg(feature = "mock_attestion")]
impl MockEvidencer {
    pub fn create() -> anyhow::Result<Self> {
        MOCK_DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(MockEvidencer {
                    evidence: &d.evidence,
                })
            })
    }
}

#[cfg(feature = "mock_attestion")]
impl Evidencer for MockEvidencer {
    fn get_evidence(&self) -> &Evidence {
        self.evidence
    }
}
