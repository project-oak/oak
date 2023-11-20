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

use crate::syscall::read;
use oak_crypto::{
    encryptor::EncryptionKeyProvider,
    hpke::{Deserializable, PrivateKey, PublicKey},
};
use oak_dice::evidence::{
    RestrictedKernelDiceData, P256_PRIVATE_KEY_SIZE, X25519_PRIVATE_KEY_SIZE,
};
use oak_remote_attestation::proto::oak::attestation::v1::Evidence;
use oak_restricted_kernel_interface::DICE_DATA_FD;
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

/// Wrapper for DICE evidence and application private keys.
pub struct DiceWrapper {
    pub evidence: Evidence,
    pub encryption_key: EncryptionKeyProvider,
    pub signing_key: SigningKey,
}

/// Get the DICE evidence and application private keys from the Restricted Kernel
pub fn get_dice_evidence_and_keys() -> anyhow::Result<DiceWrapper> {
    let dice_data = get_restricted_kernel_dice_data()?;
    let evidence: Evidence = dice_data.evidence.try_into()?;
    let private_key = PrivateKey::from_bytes(
        &dice_data.application_private_keys.encryption_private_key[..X25519_PRIVATE_KEY_SIZE],
    )
    .map_err(|error| anyhow::anyhow!("couldn't deserialize private key: {}", error))?;
    let application_keys = evidence
        .application_keys
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("no application keys"))?;
    let public_key = PublicKey::from_bytes(application_keys.encryption_public_key_certificate())
        .map_err(|error| anyhow::anyhow!("couldn't deserialize public key: {}", error))?;
    let encryption_key = EncryptionKeyProvider::new_from_keys(private_key, public_key);
    let signing_key = SigningKey::from_slice(
        &dice_data.application_private_keys.signing_private_key[..P256_PRIVATE_KEY_SIZE],
    )
    .map_err(|error| anyhow::anyhow!("couldn't deserialize signing key: {}", error))?;
    Ok(DiceWrapper {
        evidence,
        encryption_key,
        signing_key,
    })
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
