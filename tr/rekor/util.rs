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
//

//! Provides utilities around Rekor log entry verification.

use alloc::vec::Vec;

use key_util::convert_pem_to_raw;
use oak_proto_rust::oak::attestation::v1::TimestampReferenceValue;
use oak_time::{Duration, Instant};

const REKOR_V1_PUBLIC_KEY_PEM: &str =
    include_str!("../../oak_attestation_verification/testdata/rekor_public_key.pem");

/// Returns the verifying key from rekor.sigstore.dev as PEM.
pub const fn get_rekor_v1_public_key_pem() -> &'static str {
    REKOR_V1_PUBLIC_KEY_PEM
}

/// Returns the verifying key from rekor.sigstore.dev as raw.
pub fn get_rekor_v1_public_key_raw() -> Vec<u8> {
    convert_pem_to_raw(get_rekor_v1_public_key_pem()).unwrap()
}

/// Verifies the given timestamp is valid based on the current time and the
/// TimestampReferenceValue.
///
/// Arguments:
///   current_time: The current time as instant.
///   timestamp: The timestamp of the signature, e.g. signedLogEntryTimestamp
///   reference_value: The reference value from the client.
pub(crate) fn verify_timestamp(
    current_time: Instant,
    timestamp: Instant,
    reference_value: &TimestampReferenceValue,
) -> anyhow::Result<()> {
    // if not_before_absolute is set, check that the timestamp is not before
    // that time.
    if let Some(not_before_absolute) = &reference_value.not_before_absolute {
        let not_before_absolute_time = Instant::from(not_before_absolute);
        if timestamp < not_before_absolute_time {
            anyhow::bail!(
                "Timestamp is too early: timestamp = {}, must not be before = {}",
                timestamp,
                not_before_absolute_time
            );
        }
    }

    // if not_before_relative is set, check that the given timestamp is not
    // after the current time plus that (signed) duration.
    if let Some(not_before_relative) = &reference_value.not_before_relative {
        let offset = Duration::from(not_before_relative);
        if timestamp < current_time + offset {
            anyhow::bail!(
                "Timestamp is out of range: timestamp = {}, range [{}, {}]",
                timestamp,
                current_time + offset,
                current_time
            );
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests;
