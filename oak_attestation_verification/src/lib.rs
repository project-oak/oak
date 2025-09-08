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
#![feature(assert_matches)]
#![feature(let_chains)]

extern crate alloc;

mod amd;
mod compare;
mod endorsement;
mod expect;
mod extract;
mod intel;
mod platform;
mod policy;
mod rekor;
pub mod results;
mod util;
pub mod verifier;
mod verifiers;

#[cfg(test)]
mod test_util;

use anyhow::Context;
use digest_util::hex_to_raw_digest;
pub use expect::get_expected_values;
pub use extract::extract_evidence;
use intoto::statement::get_hex_digest_from_statement;
use oak_proto_rust::oak::attestation::v1::{
    EndorsementDetails, EndorsementReferenceValue, SignedEndorsement,
};
// TODO: b/437347358 - Most tests in policy_tests.rs are unit tests for a
// policy. The policies here are exported only for that purpose. This
// visibility should be revoked after moving the tests.
pub use policy::{
    application::ApplicationPolicy,
    application_keys::ApplicationKeysPolicy,
    binary::BinaryPolicy,
    container::ContainerPolicy,
    firmware::FirmwarePolicy,
    kernel::KernelPolicy,
    platform::AmdSevSnpPolicy,
    session_binding_public_key::{
        SessionBindingPublicKeyPolicy, SessionBindingPublicKeyVerificationError,
        SessionBindingPublicKeyVerificationReport,
    },
    system::SystemPolicy,
};
pub use rekor::verify_rekor_log_entry;
pub use util::{convert_pem_to_raw, decode_event_proto, decode_protobuf_any};
pub use verifiers::{
    create_amd_verifier, create_insecure_verifier, AmdSevSnpDiceAttestationVerifier,
    EventLogVerifier, InsecureAttestationVerifier,
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
    let digest = hex_to_raw_digest(&get_hex_digest_from_statement(&s)?)?;
    let validity = s.predicate.validity.context("missing validity in statement")?;

    Ok(EndorsementDetails {
        subject_digest: Some(digest),
        valid: Some(oak_proto_rust::oak::Validity::from(&validity)),
        claim_types: s.predicate.claims.into_iter().map(|x| x.r#type).collect(),
    })
}
