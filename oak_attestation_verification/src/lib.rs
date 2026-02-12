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

extern crate alloc;

mod amd;
mod compare;
mod endorsement;
mod expect;
mod extract;
mod intel;
mod platform;
mod policy;
pub mod results {
    pub use oak_attestation_verification_results::*;
}
mod util;
pub mod verifier;
mod verifiers;
mod x509;

#[cfg(test)]
mod test_util;

pub use expect::get_expected_values;
pub use extract::extract_evidence;
pub use key_util::convert_pem_to_raw;
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
    platform::{AmdSevSnpPolicy, IntelTdxPolicy},
    session_binding_public_key::{
        SessionBindingPublicKeyPolicy, SessionBindingPublicKeyVerificationError,
        SessionBindingPublicKeyVerificationReport,
    },
    system::SystemPolicy,
};
pub use rekor::log_entry::verify_rekor_log_entry; // Exported utility function.
pub use util::decode_event_proto;
pub use verifiers::{
    AmdSevSnpDiceAttestationVerifier, AmdSevSnpTransparentDiceAttestationVerifier,
    EventLogVerifier, InsecureAttestationVerifier, IntelTdxAttestationVerifier,
    create_amd_verifier, create_insecure_verifier, create_intel_tdx_verifier,
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
    let s = verify_endorsement::verify_endorsement(now_utc_millis, signed_endorsement, ref_value)?;
    s.get_details()
}
