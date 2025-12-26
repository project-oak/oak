//
// Copyright 2025 The Project Oak Authors
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

//! Unified Attester implementation for Oak Containers that works with AMD
//! SEV-SNP and Intel TDX.

extern crate alloc;

use alloc::vec::Vec;
use core::convert::TryInto;

use anyhow::Context;
use oak_attestation::LayerData;
#[allow(deprecated)]
use oak_attestation::{dice::DiceAttester, ApplicationKeysAttester};
use oak_attestation_tdx::RtmrAttester;
use oak_attestation_types::{
    attester::Attester,
    util::{try_decode_length_delimited_proto, Serializable},
};
use oak_proto_rust::oak::attestation::v1::{DiceData, Evidence, TeePlatform};
use p256::ecdsa::VerifyingKey;

enum InnerAttester {
    Rtmr(RtmrAttester),
    Dice(DiceAttester),
}

// Unified Attester implementation that supports AMD SEV-SNP and Intel TDX.
pub struct UnifiedAttester {
    inner: InnerAttester,
}

// TODO: b/368030563 - Remove this implementation once all client library
// instances use the applications keys from the event log.
#[allow(deprecated)]
impl ApplicationKeysAttester for UnifiedAttester {
    fn add_application_keys(
        self,
        layer_data: LayerData,
        kem_public_key: &[u8],
        verifying_key: &VerifyingKey,
        group_kem_public_key: Option<&[u8]>,
        group_verifying_key: Option<&VerifyingKey>,
    ) -> anyhow::Result<Evidence> {
        match self.inner {
            InnerAttester::Rtmr(attester) => attester.add_application_keys(
                layer_data,
                kem_public_key,
                verifying_key,
                group_kem_public_key,
                group_verifying_key,
            ),
            InnerAttester::Dice(attester) => attester.add_application_keys(
                layer_data,
                kem_public_key,
                verifying_key,
                group_kem_public_key,
                group_verifying_key,
            ),
        }
    }
}

impl Attester for UnifiedAttester {
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()> {
        match &mut self.inner {
            InnerAttester::Rtmr(attester) => attester.extend(encoded_event),
            InnerAttester::Dice(attester) => attester.extend(encoded_event),
        }
    }

    fn quote(&self) -> anyhow::Result<Evidence> {
        match &self.inner {
            InnerAttester::Rtmr(attester) => attester.quote(),
            InnerAttester::Dice(attester) => attester.quote(),
        }
    }
}

impl Serializable for UnifiedAttester {
    fn deserialize(bytes: &[u8]) -> anyhow::Result<Self> {
        // TODO: b/368023328 - Rename DiceData.
        let attestation_data: DiceData = try_decode_length_delimited_proto(bytes)
            .context("couldn't parse attestation data: {:?}")?;
        let tee_platform: TeePlatform = attestation_data
            .evidence
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no evidence"))?
            .root_layer
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no root_layer"))?
            .platform
            .try_into()?;
        let inner = match tee_platform {
            TeePlatform::AmdSevSnp | TeePlatform::None => {
                InnerAttester::Dice(attestation_data.try_into()?)
            }
            TeePlatform::IntelTdx => InnerAttester::Rtmr(attestation_data.try_into()?),
            TeePlatform::Unspecified => anyhow::bail!("invalid TEE platform"),
        };
        Ok(Self { inner })
    }

    fn serialize(self) -> Vec<u8> {
        match self.inner {
            InnerAttester::Rtmr(attester) => attester.serialize(),
            InnerAttester::Dice(attester) => attester.serialize(),
        }
    }
}
