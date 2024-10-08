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

//! Structs for providing attestation related logic such as getting an evidence.

use alloc::vec::Vec;

use anyhow::Context;
use oak_crypto::encryption_key::EncryptionKey;
use oak_dice::evidence::{Evidence, RestrictedKernelDiceData, P256_PRIVATE_KEY_SIZE};
use oak_restricted_kernel_interface::{syscall::read, DICE_DATA_FD, EVENT_LOG_FD};
use p256::ecdsa::SigningKey;
use zerocopy::{AsBytes, FromZeroes};

lazy_static::lazy_static! {
    pub(crate) static ref DICE_WRAPPER: anyhow::Result<DiceWrapper> = {
        let dice_data = get_restricted_kernel_dice_data().context("couldn't get DICE data")?;
        let encoded_event_log = get_encoded_event_log().context("couldn't get event log")?;
        let mut dice_wrapper: DiceWrapper = dice_data.try_into()?;
        dice_wrapper.encoded_event_log = Some(encoded_event_log);
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

/// Requests encoded event log from Restricted Kernel via syscall.
fn get_encoded_event_log() -> anyhow::Result<Vec<u8>> {
    let mut event_log = Vec::new();
    let mut buffer = [0u8; 4 * 1024]; // Read in 4KB chunks

    loop {
        match read(EVENT_LOG_FD, &mut buffer) {
            Ok(0) => break, // End of file
            Ok(n) => event_log.extend_from_slice(&buffer[..n]),
            Err(e) => anyhow::bail!("failed to read event log: {:?}", e),
        }
    }
    Ok(event_log)
}

/// Wrapper for DICE evidence and application private keys.
pub(crate) struct DiceWrapper {
    pub evidence: Evidence,
    pub encryption_key: EncryptionKey,
    pub signing_key: p256::ecdsa::SigningKey,
    pub encoded_event_log: Option<Vec<u8>>,
}

impl TryFrom<RestrictedKernelDiceData> for DiceWrapper {
    type Error = anyhow::Error;
    fn try_from(mut dice_data: RestrictedKernelDiceData) -> Result<Self, Self::Error> {
        let encryption_key = EncryptionKey::deserialize(
            &mut dice_data.application_private_keys.encryption_private_key
                [..oak_dice::evidence::X25519_PRIVATE_KEY_SIZE],
        )?;
        let signing_key = SigningKey::from_slice(
            &dice_data.application_private_keys.signing_private_key[..P256_PRIVATE_KEY_SIZE],
        )
        .map_err(|error| anyhow::anyhow!("couldn't deserialize signing key: {}", error))?;
        let evidence = dice_data.evidence;
        Ok(DiceWrapper { evidence, encryption_key, signing_key, encoded_event_log: None })
    }
}

/// Exposes the ability to read the Attestation Evidence.
/// Note: Applications should only use the evidence to initially send it to the
/// host application once, which then sends it to the clients. It is discouraged
/// for enclave applications to operate directly with evidences.
pub trait EvidenceProvider {
    fn get_evidence(&self) -> &Evidence;
    fn get_encoded_event_log(&self) -> Option<&[u8]>;
}

/// [`EvidenceProvider`] implementation that exposes the instance's evidence.
pub struct InstanceEvidenceProvider {
    evidence: &'static Evidence,
    encoded_event_log: Option<&'static [u8]>,
}

impl InstanceEvidenceProvider {
    pub fn create() -> anyhow::Result<Self> {
        DICE_WRAPPER.as_ref().map_err(anyhow::Error::msg).map(|d| InstanceEvidenceProvider {
            evidence: &d.evidence,
            encoded_event_log: d.encoded_event_log.as_ref().map(|buffer| buffer.as_slice()),
        })
    }
}

impl EvidenceProvider for InstanceEvidenceProvider {
    fn get_evidence(&self) -> &Evidence {
        self.evidence
    }

    fn get_encoded_event_log(&self) -> Option<&[u8]> {
        self.encoded_event_log
    }
}
