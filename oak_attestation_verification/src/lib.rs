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

#![no_std]
#![feature(let_chains)]

use oak_proto_rust::oak::attestation::v1::{EndorsementReferenceValue, SignedEndorsement};

extern crate alloc;

pub(crate) mod amd;
pub(crate) mod endorsement;
pub mod expect;
pub(crate) mod extract;
pub mod policy;
pub(crate) mod rekor;
pub(crate) mod util;
pub mod verifier;

/// Verifies a signed endorsement against reference value.
///
/// Returns Ok whenever the verification succeeds, or an error otherwise.
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
) -> anyhow::Result<()> {
    endorsement::verify_endorsement(now_utc_millis, signed_endorsement, ref_value)
}
