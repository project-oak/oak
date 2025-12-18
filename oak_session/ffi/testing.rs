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

use anyhow::Result;
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_ffi_bytes::{BytesView, RustBytes};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results, ApplicationKeys, AttestationResults, Endorsements, EventLog, Evidence,
        ExtractedEvidence,
    },
    Variant,
};
use oak_session_ffi_config::FfiAttestationVerifier;
use p256::ecdsa::SigningKey;
use prost::Message;
use rand_core::OsRng;

/// Create a new fake evidence for use in unit tests.
///
/// # Safety
/// * verifying_key_bytes is a valid ByteView
/// * fake_event_log_data_bytes is a valid ByteView
#[no_mangle]
pub unsafe extern "C" fn new_fake_evidence(
    verifying_key_bytes: BytesView,
    fake_event_log_data_bytes: BytesView,
) -> RustBytes {
    #[allow(deprecated)]
    let evidence = Evidence {
        root_layer: None,
        application_keys: Some(ApplicationKeys {
            signing_public_key_certificate: unsafe { verifying_key_bytes.as_slice().to_vec() },
            ..Default::default()
        }),
        layers: vec![],
        event_log: Some(EventLog {
            encoded_events: vec![unsafe { fake_event_log_data_bytes.as_slice().to_vec() }],
        }),
        transparent_event_log: None,
        signed_user_data_certificate: None,
    };
    RustBytes::new(evidence.encode_to_vec().into_boxed_slice())
}

/// Create a new fake endorsements for use in unit tests.
///
/// # Safety
/// * fake_platform_value_bytes is a valid ByteView
#[no_mangle]
pub unsafe extern "C" fn new_fake_endorsements(fake_platform_value_bytes: BytesView) -> RustBytes {
    let endorsements = Endorsements {
        events: vec![],
        initial: None,
        platform: Some(Variant {
            id: b"fake".to_vec(),
            value: fake_platform_value_bytes.as_slice().to_vec(),
        }),
        r#type: None,
    };
    RustBytes::new(endorsements.encode_to_vec().into_boxed_slice())
}

// A test attestation verifier to use with the fake attester and endorser.
pub struct FakeAttestationVerifier {
    expected_evidence_event_log_data: Vec<u8>,
    expected_endorsement_platform_value: Vec<u8>,
}

impl FakeAttestationVerifier {
    pub fn new(fake_evidence_data: &[u8], fake_endorsement_platform_value: &[u8]) -> Self {
        Self {
            expected_evidence_event_log_data: fake_evidence_data.to_vec(),
            expected_endorsement_platform_value: fake_endorsement_platform_value.to_vec(),
        }
    }
}

/// Create a new fake attesation verifier for use in unit tests.
///
/// [`fake_evidence_data`] should be the same value provided to an evidence
/// created by [`create_fake_evidence`] that you'll verify in the test.
///
/// [`fake_endorsement_platform_value`] should be the same value provided to an
/// endorsement set created by [`create_fake_endorsements`] that you'll verify
/// in the test.
///
/// # Safety
///  * fake_evidence_data is a valid ByteView
///  * fake_endorsement_platform_value is a valid ByteView
#[no_mangle]
pub unsafe extern "C" fn new_fake_attestation_verifier(
    fake_evidence_data: BytesView,
    fake_endorsement_platform_value: BytesView,
) -> FfiAttestationVerifier {
    FfiAttestationVerifier::new(Box::new(FakeAttestationVerifier::new(
        fake_evidence_data.as_slice(),
        fake_endorsement_platform_value.as_slice(),
    )))
}

impl AttestationVerifier for FakeAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> Result<AttestationResults> {
        assert_eq!(
            evidence.event_log.as_ref().expect("no event log").encoded_events[0],
            self.expected_evidence_event_log_data
        );
        assert_eq!(
            endorsements.platform.as_ref().expect("no endorsement paltform").value,
            self.expected_endorsement_platform_value
        );
        #[allow(deprecated)]
        Ok(AttestationResults {
            status: attestation_results::Status::Success.into(),
            extracted_evidence: Some(ExtractedEvidence {
                signing_public_key: evidence
                    .application_keys
                    .as_ref()
                    .expect("no app keys")
                    .signing_public_key_certificate
                    .clone(),
                ..Default::default()
            }),
            ..Default::default()
        })
    }
}

#[no_mangle]
pub extern "C" fn new_random_signing_key() -> *mut SigningKey {
    Box::into_raw(Box::new(SigningKey::random(&mut OsRng)))
}

/// Return the SEC1 verifying key bytes for the provided Rust signing key.
///
/// # Safety
///
/// * signing_key_ptr was obtained from a suitable source and is still valid.
#[no_mangle]
pub unsafe extern "C" fn signing_key_verifying_key_bytes(
    signing_key_ptr: *const SigningKey,
) -> RustBytes {
    let verifying_key_bytes = (*signing_key_ptr).verifying_key().to_sec1_bytes().to_vec();
    RustBytes::new(verifying_key_bytes.into_boxed_slice())
}

/// Free the memory allocated by a new_random_singing_key call.
///
/// # Safety
///
/// * signing_key_ptr was obtained from a suitable source and is still valid.
#[no_mangle]
pub unsafe extern "C" fn free_signing_key(key: *mut SigningKey) {
    drop(Box::from_raw(key));
}
