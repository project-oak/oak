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

use alloc::vec::Vec;
use core::time::Duration;

use oak_proto_rust::oak::crypto::v1::{
    Certificate, CertificatePayload, SignatureInfo, SubjectPublicKeyInfo, Validity,
};
use oak_time::Instant;
use prost::Message;
use prost_types::Timestamp;

use crate::{certificate::certificate_verifier::CertificateVerifier, verifier::Verifier};

const TEST_PUBLIC_KEY: &[u8] = b"TEST_PUBLIC_KEY";
const TEST_BAD_PUBLIC_KEY: &[u8] = b"TEST_BAD_PUBLIC_KEY";
const TEST_PURPOSE_ID: &[u8] = b"TEST_PURPOSE_ID";
const TEST_BAD_PURPOSE_ID: &[u8] = b"TEST_BAD_PURPOSE_ID";
const TEST_SIGNATURE: &[u8] = b"TEST_SIGNATURE";
const TEST_BAD_SIGNATURE: &[u8] = b"TEST_BAD_SIGNATURE";
const TEST_CURRENT_TIME_MILLISECONDS: i64 = 1_234_567;

#[derive(Clone, Default)]
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
    public_key: &[u8],
    purpose_id: &[u8],
    not_before: Timestamp,
    not_after: Timestamp,
    signature: &[u8],
) -> Certificate {
    let validity = Validity { not_before: Some(not_before), not_after: Some(not_after) };
    let subject_public_key_info =
        SubjectPublicKeyInfo { public_key: public_key.to_vec(), purpose_id: purpose_id.to_vec() };
    let payload = CertificatePayload {
        validity: Some(validity),
        subject_public_key_info: Some(subject_public_key_info),
        ..Default::default()
    };
    let serialized_payload = payload.encode_to_vec();

    Certificate {
        serialized_payload,
        signature_info: Some(SignatureInfo { signature: signature.to_vec() }),
    }
}

#[test]
fn test_verify_certificate_success() {
    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 1).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS + 1).into_timestamp(),
        TEST_SIGNATURE,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());
}

#[test]
fn test_verify_certificate_signature_failure() {
    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 1).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS + 1).into_timestamp(),
        TEST_BAD_SIGNATURE,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_zero_validity_failure() {
    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        // `not_after` is equal to `not_before`.
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS).into_timestamp(),
        TEST_SIGNATURE,
    );
    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_negative_validity_failure() {
    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        // `not_after` is smaller than `not_before`.
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 1).into_timestamp(),
        TEST_SIGNATURE,
    );
    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_validity_failure() {
    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 2).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 1).into_timestamp(),
        TEST_SIGNATURE,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_public_key_failure() {
    let certificate = create_test_certificate(
        TEST_BAD_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 1).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS + 1).into_timestamp(),
        TEST_SIGNATURE,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_purpose_failure() {
    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_BAD_PURPOSE_ID,
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 1).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS + 1).into_timestamp(),
        TEST_SIGNATURE,
    );

    let verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_clock_skew() {
    let certificate = create_test_certificate(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS - 5).into_timestamp(),
        Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS + 5).into_timestamp(),
        TEST_SIGNATURE,
    );

    let allowed_clock_skew = Duration::from_millis(5);
    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_allowed_clock_skew(allowed_clock_skew);

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS - 7,
        &certificate,
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS + 7,
        &certificate,
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS - 11,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS + 11,
        &certificate,
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}

#[test]
fn test_verify_certificate_validity_limit() {
    fn certificate_from_validity(validity: i64) -> Certificate {
        create_test_certificate(
            TEST_PUBLIC_KEY,
            TEST_PURPOSE_ID,
            Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS).into_timestamp(),
            Instant::from_unix_millis_i64(TEST_CURRENT_TIME_MILLISECONDS + validity)
                .into_timestamp(),
            TEST_SIGNATURE,
        )
    }

    let validity_limit = Duration::from_millis(10);
    let mut verifier =
        CertificateVerifier::new(MockVerifier { expected_signature: TEST_SIGNATURE.to_vec() });
    verifier.set_validity_limit(validity_limit);

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate_from_validity(9),
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate_from_validity(10),
    );
    assert!(result.is_ok(), "Expected verification to succeed, but got error: {:?}", result.err());

    let result = verifier.verify(
        TEST_PUBLIC_KEY,
        TEST_PURPOSE_ID,
        TEST_CURRENT_TIME_MILLISECONDS,
        &certificate_from_validity(11),
    );
    assert!(result.is_err(), "Expected verification to fail, but got success");
}
