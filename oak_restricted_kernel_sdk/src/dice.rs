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
use anyhow::Ok;
use oak_core::sync::OnceCell;
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, P256_PRIVATE_KEY_SIZE};
use oak_restricted_kernel_interface::DICE_DATA_FD;
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

static DICE_WRAPPER: OnceCell<anyhow::Result<DiceWrapper>> = OnceCell::new();

/// Wrapper for DICE evidence and application private keys.
#[allow(dead_code)]
struct DiceWrapper {
    pub evidence: Evidence,
    pub encryption_key: EncryptionKeyProvider,
    pub signing_key: p256::ecdsa::SigningKey,
}

/// Reads the dice data from the kernel
fn read_dice_wrapper() -> anyhow::Result<DiceWrapper> {
    let dice_data = {
        let mut result = RestrictedKernelDiceData::new_zeroed();
        let buffer = result.as_bytes_mut();
        let len =
            read(DICE_DATA_FD, buffer).map_err(|err| anyhow::anyhow!("read failure: {err}"))?;
        if len != buffer.len() {
            anyhow::bail!("invalid dice data size");
        }

        result
    };

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

pub struct Signer {
    key: &'static SigningKey,
}

impl Signer {
    pub fn create() -> anyhow::Result<Self> {
        DICE_WRAPPER
            .get_or_init(read_dice_wrapper)
            .as_ref()
            .map_err(anyhow::Error::msg)
            .and_then(|d| {
                Ok(Signer {
                    key: &d.signing_key,
                })
            })
    }
    pub fn sign(&self, message: &[u8]) -> oak_crypto::signer::Signature {
        <SigningKey as oak_crypto::signer::Signer>::sign(&self.key, message)
    }
}
