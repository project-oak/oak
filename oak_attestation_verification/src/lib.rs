//
// Copyright 2022 The Project Oak Authors
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

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(let_chains)]

extern crate alloc;

pub(crate) mod amd;
pub(crate) mod compare;
pub(crate) mod endorsement;
pub mod expect;
pub mod extract;
pub(crate) mod platform;
pub mod policy;
pub(crate) mod rekor;
pub mod statement;
pub(crate) mod util;
pub mod verifier;

#[cfg(test)]
mod test_util;

use anyhow::Context;
use oak_proto_rust::oak::attestation::v1::{
    EndorsementDetails, EndorsementReferenceValue, SignedEndorsement, Validity,
};
use oak_time::Instant;
pub use util::{
    convert_pem_to_raw, hex_to_raw_digest, raw_to_hex_digest, reference_values_from_evidence,
    UnixTimestampMillis,
};

/// Verifies a signed endorsement against a reference value.
///
/// `now_utc_millis`: The current time in milliseconds UTC since Unix Epoch.
/// `signed_endorsement`: The endorsement along with signature and (optional)
///     Rekor log entry.
/// `ref_value`: A reference value containing e.g. the public keys needed
///     for the verification.
pub fn verify_endorsement(
    now_utc_millis: i64,
    signed_endorsement: &SignedEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<EndorsementDetails> {
    let s = endorsement::verify_endorsement(now_utc_millis, signed_endorsement, ref_value)?;
    let digest = hex_to_raw_digest(&statement::get_digest(&s)?)?;
    let validity = s.predicate.validity.context("missing validity in statement")?;
    let not_before = Instant::from_unix_millis(
        validity
            .not_before
            .unix_timestamp_millis()
            .try_into()
            .context("failed to convert between signed and unsigned")?,
    );
    let not_after = Instant::from_unix_millis(
        validity
            .not_after
            .unix_timestamp_millis()
            .try_into()
            .context("failed to convert between signed and unsigned")?,
    );

    #[allow(deprecated)]
    Ok(EndorsementDetails {
        subject_digest: Some(digest),
        validity: Some(Validity {
            not_before: validity.not_before.unix_timestamp_millis(),
            not_after: validity.not_after.unix_timestamp_millis(),
        }),
        valid: Some(oak_proto_rust::oak::Validity {
            not_before: Some(not_before.into_timestamp()),
            not_after: Some(not_after.into_timestamp()),
        }),
        claim_types: s.predicate.claims.into_iter().map(|x| x.r#type).collect(),
    })
}
