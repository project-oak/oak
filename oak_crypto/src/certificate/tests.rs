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

use alloc::{vec, vec::Vec};

use oak_proto_rust::oak::{
    crypto::v1::{
        Certificate, CertificatePayload, ProofOfFreshness,
        SerializedPayloadType::PayloadTypeSerializedCertificate, SignatureInfo,
        SubjectPublicKeyInfo,
    },
    Validity,
};
use oak_time::{Duration, Instant};
use prost::Message;

use crate::{
    certificate::certificate_verifier::{
        CertificateVerificationError, CertificateVerificationReport, CertificateVerifier,
        ProofOfFreshnessVerification,
    },
    verifier::Verifier,
};

const TEST_PUBLIC_KEY: &[u8] = b"TEST_PUBLIC_KEY";
const TEST_BAD_PUBLIC_KEY: &[u8] = b"TEST_BAD_PUBLIC_KEY";
const TEST_PURPOSE_ID: &[u8] = b"TEST_PURPOSE_ID";
const TEST_BAD_PURPOSE_ID: &[u8] = b"TEST_BAD_PURPOSE_ID";
const TEST_SIGNATURE: &[u8] = b"TEST_SIGNATURE";
const TEST_BAD_SIGNATURE: &[u8] = b"TEST_BAD_SIGNATURE";
const TEST_CURRENT_TIME_MILLIS: i64 = 1_234_567;
const TEST_CURRENT_TIME: Instant = Instant::from_unix_millis(TEST_CURRENT_TIME_MILLIS);

#[derive(Clone, Debug, Default)]
struct MockVerifier {
    expected_signature: Vec<u8>,
}

impl Verifier for MockVerifier {
    fn verify(&self, _message: &[u8], signature: &[u8]) -> anyhow::Result<()> {
        anyhow::ensure!(self.expected_signature == signature, "couldn't verify signature");
        Ok(())
    }
}

fn create_test_certificate(
    not_before: Instant,
    not_after: Instant,
    public_key: &[u8],
    purpose_id: &[u8],
    signature: &[u8],
    proof_of_freshness: Option<ProofOfFreshness>,
) -> Certificate {
    let validity = Validity {
        not_before: Some(not_before.into_timestamp()),
        not_after: Some(not_after.into_timestamp()),
    };
    let subject_public_key_info =
        SubjectPublicKeyInfo { public_key: public_key.to_vec(), purpose_id: purpose_id.to_vec() };
    let payload = CertificatePayload {
        validity: Some(validity),
        subject_public_key_info: Some(subject_public_key_info),
        proof_of_freshness,
    };
    let serialized_payload = payload.encode_to_vec();

    Certificate {
        serialized_payload,
        signature_info: Some(SignatureInfo { signature: signature.to_vec() }),
        serialized_payload_type: PayloadTypeSerializedCertificate.into(),
    }
}

#[test]
fn test_verify_certificate_success() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());
}

#[test]
fn test_verify_certificate_signature_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_BAD_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_zero_validity_failure() {
    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let certificate = create_test_certificate(
        // `not_after` is before `not_before`.
        TEST_CURRENT_TIME,
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );
    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_negative_validity_failure() {
    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let certificate = create_test_certificate(
        // `not_after` is smaller than `not_before`, so the certificate can
        // never be valid.
        TEST_CURRENT_TIME,
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );
    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_validity_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(2),
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_public_key_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_BAD_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_purpose_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_BAD_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_clock_skew() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(5),
        TEST_CURRENT_TIME + Duration::from_millis(5),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let allowed_clock_skew = Duration::from_millis(5);
    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_allowed_clock_skew(allowed_clock_skew);

    let result = verifier.verify(
        TEST_CURRENT_TIME - Duration::from_millis(7),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_CURRENT_TIME + Duration::from_millis(7),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_CURRENT_TIME - Duration::from_millis(11),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");

    let result = verifier.verify(
        TEST_CURRENT_TIME + Duration::from_millis(11),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_validity_limit() {
    fn certificate_for_duration(valid_for: Duration) -> Certificate {
        create_test_certificate(
            TEST_CURRENT_TIME,
            TEST_CURRENT_TIME + valid_for,
            TEST_PUBLIC_KEY,
            TEST_PURPOSE_ID,
            TEST_SIGNATURE,
            None,
        )
    }

    let validity_limit = Duration::from_millis(10);
    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_max_validity_duration(validity_limit);

    let result = verifier.verify(
        TEST_CURRENT_TIME,
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate_for_duration(Duration::from_millis(9)),
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_CURRENT_TIME,
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate_for_duration(Duration::from_millis(10)),
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_CURRENT_TIME,
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate_for_duration(Duration::from_millis(11)),
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_report_certificate_success() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Ok(()),
            freshness: None
        })
    ));
}

#[test]
fn test_report_certificate_signature_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_BAD_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Err(CertificateVerificationError::SignatureVerificationError(_)),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_zero_validity_failure() {
    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let certificate = create_test_certificate(
        // `not_after` is before `not_before`.
        TEST_CURRENT_TIME,
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );
    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Err(CertificateVerificationError::ValidityPeriodInvalid { .. }),
            verification: Ok(()),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_negative_validity_failure() {
    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let certificate = create_test_certificate(
        // `not_after` is smaller than `not_before`.
        TEST_CURRENT_TIME,
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );
    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Err(CertificateVerificationError::ValidityPeriodInvalid { .. }),
            verification: Ok(()),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_validity_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(2),
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Err(CertificateVerificationError::ValidityPeriodExpired { .. }),
            verification: Ok(()),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_public_key_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_BAD_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Err(CertificateVerificationError::SubjectPublicKeyMismatch { .. }),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_purpose_failure() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_BAD_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Err(CertificateVerificationError::PurposeIdMismatch { .. }),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_clock_skew() {
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(5),
        TEST_CURRENT_TIME + Duration::from_millis(5),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        None,
    );

    let allowed_clock_skew = Duration::from_millis(5);
    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_allowed_clock_skew(allowed_clock_skew);

    let result = verifier.report(
        TEST_CURRENT_TIME - Duration::from_millis(7),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Ok(()),
            freshness: None,
        })
    ));

    let result = verifier.report(
        TEST_CURRENT_TIME + Duration::from_millis(7),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Ok(()),
            freshness: None,
        })
    ));

    let result = verifier.report(
        TEST_CURRENT_TIME - Duration::from_millis(11),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Err(CertificateVerificationError::ValidityPeriodNotYetStarted { .. }),
            verification: Ok(()),
            freshness: None,
        })
    ));

    let result = verifier.report(
        TEST_CURRENT_TIME + Duration::from_millis(11),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate,
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Err(CertificateVerificationError::ValidityPeriodExpired { .. }),
            verification: Ok(()),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_validity_limit() {
    fn certificate_for_duration(valid_for: Duration) -> Certificate {
        create_test_certificate(
            TEST_CURRENT_TIME,
            TEST_CURRENT_TIME + valid_for,
            TEST_PUBLIC_KEY,
            TEST_PURPOSE_ID,
            TEST_SIGNATURE,
            None,
        )
    }

    let validity_limit = Duration::from_millis(10);
    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_max_validity_duration(validity_limit);

    let result = verifier.report(
        TEST_CURRENT_TIME,
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate_for_duration(Duration::from_millis(9)),
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Ok(()),
            freshness: None,
        })
    ));

    let result = verifier.report(
        TEST_CURRENT_TIME,
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate_for_duration(Duration::from_millis(10)),
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Ok(()),
            freshness: None,
        })
    ));

    let result = verifier.report(
        TEST_CURRENT_TIME,
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        &certificate_for_duration(Duration::from_millis(11)),
    );
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Err(CertificateVerificationError::ValidityPeriodTooLong { .. }),
            verification: Ok(()),
            freshness: None,
        })
    ));
}

#[test]
fn test_report_certificate_freshness_unimplemented() {
    let proof_of_freshness = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 100,
        nist_pulse_output_value: vec![1, 2, 3],
    };
    let certificate = create_test_certificate(
        TEST_CURRENT_TIME - Duration::from_millis(1),
        TEST_CURRENT_TIME + Duration::from_millis(1),
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_SIGNATURE,
        Some(proof_of_freshness),
    );

    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_proof_of_freshness_verification(ProofOfFreshnessVerification::Verify);

    let result = verifier.report(TEST_CURRENT_TIME, TEST_PUBLIC_KEY, TEST_PURPOSE_ID, &certificate);
    assert!(matches!(
        result,
        Ok(CertificateVerificationReport {
            validity: Ok(()),
            verification: Ok(()),
            freshness: Some(Err(CertificateVerificationError::ProofOfFreshnessUnimplemented)),
        })
    ));
}
