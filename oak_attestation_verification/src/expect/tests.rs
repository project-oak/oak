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

use std::collections::BTreeMap;

use intoto::statement::Validity;
use oak_digest::{
    hex_digest_from_contents, hex_to_raw_digest, raw_digest_from_contents, raw_to_hex_digest,
};
use oak_proto_rust::oak::{
    HexDigest,
    attestation::v1::{
        ExpectedDigests, ExpectedRegex, FirmwareAttachment, KernelAttachment, RawDigests,
        TextExpectedValue, TextReferenceValue, TransparentReleaseEndorsement, expected_digests,
        text_expected_value, text_reference_value,
    },
};
use oak_time::Instant;
use prost::Message;
use verify_endorsement::{FIRMWARE_CLAIM_TYPE, KERNEL_CLAIM_TYPE};

use crate::test_util::{self, GetValidity};

// Returns milliseconds UTC in the middle of the validity period.
fn make_valid_now_utc_millis(validity: &Validity) -> i64 {
    let middle = validity.not_before + (validity.not_after - validity.not_before) / 2;
    middle.into_unix_millis()
}

#[test]
fn test_get_expected_measurement_digest_validity() {
    // Create an endorsement of some arbitrary content.
    let measured_content = b"Just some abitrary content";
    let hex_digest = hex_digest_from_contents(measured_content);
    let endorsement = test_util::fake_endorsement(&hex_digest, vec![]);
    let statement_validity = endorsement.predicate.validity.as_ref().expect("no validity");

    // Now create the TR endorsement.
    let (signing_key, public_key) = test_util::new_random_signing_keypair();
    let (serialized_endorsement, endorsement_signature) =
        test_util::serialize_and_sign_endorsement(&endorsement, signing_key);
    let tr_endorsement = TransparentReleaseEndorsement {
        endorsement: serialized_endorsement,
        endorsement_signature: endorsement_signature.as_bytes().to_vec(),
        subject: vec![],
        ..Default::default()
    };

    // The reference_value should contain the public key corresponding the the
    // endorsement signing key.
    let reference_value = test_util::binary_reference_value_for_endorser_pk(public_key);
    let now_utc_millis = make_valid_now_utc_millis(endorsement.validity());

    let expected_digests = super::get_expected_measurement_digest(
        now_utc_millis,
        Some(&tr_endorsement),
        &reference_value,
    )
    .expect("failed to get digests");

    // Assert that the expected digests are those from the verified endorsement.

    let raw_digest = hex_to_raw_digest(&hex_digest).expect("digest conversion failed");
    assert_eq!(
        expected_digests,
        ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                digests: vec![raw_digest],
                valid: Some(statement_validity.into()),
            })),
        }
    );
}

#[test]
fn test_get_stage0_expected_values_validity() {
    // Create the firmware attachement. This is what contains the *actual* digests
    // to verify.
    let mut configs = BTreeMap::<i32, HexDigest>::new();
    let original_content = b"Just some arbitrary content";
    let measured_content = b"Just some different arbitrary content";
    let measured_digest = raw_digest_from_contents(measured_content);
    let num_cpus = 2;
    configs.insert(num_cpus, raw_to_hex_digest(&measured_digest));
    let subject =
        FirmwareAttachment { binary: Some(hex_digest_from_contents(original_content)), configs };
    let serialized_subject = subject.encode_to_vec();

    // Now create the endorsement, containing the subject. The *endorsement*
    // hash is the hash of the serialized firmware attachment.
    let subject_digests = hex_digest_from_contents(&serialized_subject);
    let (signing_key, public_key) = test_util::new_random_signing_keypair();
    let endorsement = test_util::fake_endorsement(&subject_digests, vec![FIRMWARE_CLAIM_TYPE]);
    let statement_validity = endorsement.predicate.validity.as_ref().expect("no validity");
    let (serialized_endorsement, endorsement_signature) =
        test_util::serialize_and_sign_endorsement(&endorsement, signing_key);
    let tr_endorsement = TransparentReleaseEndorsement {
        endorsement: serialized_endorsement,
        endorsement_signature: endorsement_signature.as_bytes().to_vec(),
        subject: serialized_subject,
        ..Default::default()
    };

    // Get the expected values.
    // The reference_value should contain the public key corresponding the the
    // endorsement signing key.
    let reference_value = test_util::binary_reference_value_for_endorser_pk(public_key);
    let now_utc_millis = make_valid_now_utc_millis(endorsement.validity());
    let expected_digests =
        super::get_stage0_expected_values(now_utc_millis, Some(&tr_endorsement), &reference_value)
            .expect("failed to get digests");

    // We should have the hashes from the attachment.
    assert_eq!(
        expected_digests,
        ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                digests: vec![measured_digest],
                valid: Some(statement_validity.into()),
            })),
        }
    );
}

#[test]
fn test_get_kernel_expected_values_validity() {
    // Create the kernel attachement. This is what contains the *actual* digests
    // to verify.
    let bz_image = b"Just some abitrary bzImage";
    let measured_image = b"Just some abitrary kernel image";
    let measured_setup = b"Just some abitrary kernel setup";
    let bz_image_digest = hex_digest_from_contents(bz_image);
    let image_digest = raw_digest_from_contents(measured_image);
    let setup_digest = raw_digest_from_contents(measured_setup);
    let subject = KernelAttachment {
        bz_image: Some(bz_image_digest),
        image: Some(raw_to_hex_digest(&image_digest)),
        setup_data: Some(raw_to_hex_digest(&setup_digest)),
    };
    let serialized_subject = subject.encode_to_vec();

    // Now create the endorsement, containing the subject. The *endorsement*
    // hash is the hash of the serialized kernel attachment.
    let subject_digests = hex_digest_from_contents(&serialized_subject);
    let (signing_key, public_key) = test_util::new_random_signing_keypair();
    let endorsement = test_util::fake_endorsement(&subject_digests, vec![KERNEL_CLAIM_TYPE]);
    let statement_validity = endorsement.predicate.validity.as_ref().expect("no validity");
    let (serialized_endorsement, endorsement_signature) =
        test_util::serialize_and_sign_endorsement(&endorsement, signing_key);
    let tr_endorsement = TransparentReleaseEndorsement {
        endorsement: serialized_endorsement,
        endorsement_signature: endorsement_signature.as_bytes().to_vec(),
        subject: serialized_subject,
        ..Default::default()
    };

    // Get the expected values.
    // The reference_value should contain the public key corresponding the the
    // endorsement signing key.
    let reference_value = test_util::kernel_binary_reference_value_for_endorser_pk(public_key);
    let now_utc_millis = make_valid_now_utc_millis(endorsement.validity());
    let expected_digests =
        super::get_kernel_expected_values(now_utc_millis, Some(&tr_endorsement), &reference_value)
            .expect("failed to get digests");

    // We should have the hashes from the attachment.
    assert_eq!(
        expected_digests.image,
        Some(ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                digests: vec![image_digest],
                valid: Some(statement_validity.into()),
            })),
        })
    );
    assert_eq!(
        expected_digests.setup_data,
        Some(ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                digests: vec![setup_digest],
                valid: Some(statement_validity.into()),
            })),
        })
    );
}

fn text_reference_value_for_endorser_pk(public_key: p256::PublicKey) -> TextReferenceValue {
    TextReferenceValue {
        r#type: Some(text_reference_value::Type::Endorsement(
            test_util::endorsement_reference_value(public_key),
        )),
    }
}

#[test]
fn test_get_text_expected_values_validity() {
    let original_content = b"^some regex$";
    let (signing_key, public_key) = test_util::new_random_signing_keypair();

    // Create endorsement statement and sign it.
    let hex_digest = hex_digest_from_contents(original_content);
    let endorsement = test_util::fake_endorsement(&hex_digest, vec![]);
    let (serialized_endorsement, endorsement_signature) =
        test_util::serialize_and_sign_endorsement(&endorsement, signing_key);

    let tr_endorsement = TransparentReleaseEndorsement {
        endorsement: serialized_endorsement,
        endorsement_signature: endorsement_signature.as_bytes().to_vec(),
        subject: original_content.to_vec(),
        ..Default::default()
    };

    let reference_value = text_reference_value_for_endorser_pk(public_key);
    let now_utc_millis = make_valid_now_utc_millis(endorsement.validity());

    let result =
        super::get_text_expected_values(now_utc_millis, Some(&tr_endorsement), &reference_value);
    assert!(result.is_ok(), "expected success, got: {:?}", result.err());

    let expected = result.unwrap();
    assert_eq!(
        expected,
        TextExpectedValue {
            r#type: Some(text_expected_value::Type::Regex(ExpectedRegex {
                value: "^some regex$".to_string(),
            })),
        }
    );
}

#[test]
fn test_get_text_expected_values_fails_with_tampered_subject() {
    let original_content = b"^some regex$";
    let (signing_key, public_key) = test_util::new_random_signing_keypair();

    // Create endorsement statement and sign it.
    let hex_digest = hex_digest_from_contents(original_content);
    let endorsement = test_util::fake_endorsement(&hex_digest, vec![]);
    let (serialized_endorsement, endorsement_signature) =
        test_util::serialize_and_sign_endorsement(&endorsement, signing_key);

    let tr_endorsement = TransparentReleaseEndorsement {
        endorsement: serialized_endorsement,
        endorsement_signature: endorsement_signature.as_bytes().to_vec(),
        subject: b".*".to_vec(), // Tampered!
        ..Default::default()
    };

    let reference_value = text_reference_value_for_endorser_pk(public_key);
    let now_utc_millis = make_valid_now_utc_millis(endorsement.validity());

    let result =
        super::get_text_expected_values(now_utc_millis, Some(&tr_endorsement), &reference_value);
    assert!(result.is_err(), "expected error due to tampered subject, but it succeeded");
}

#[test]
fn test_acquire_text_expected_values_validity() {
    let original_content = b"^some regex$";
    let (signing_key, public_key) = test_util::new_random_signing_keypair();

    let not_before = oak_time::make_instant!("2025-09-01T12:00:00Z");
    let not_after = oak_time::make_instant!("2025-12-01T12:00:00Z");
    let now_utc_millis = make_valid_now_utc_millis(&Validity { not_before, not_after });

    let signed_endorsement = test_util::make_signed_endorsement_for_contents(
        original_content,
        not_before,
        not_after,
        &signing_key,
        vec![],
    );

    let reference_value = text_reference_value_for_endorser_pk(public_key);

    let result = super::acquire_text_expected_values(
        now_utc_millis,
        Some(&signed_endorsement),
        &reference_value,
    );
    assert!(result.is_ok(), "expected success, got: {:?}", result.err());

    let expected = result.unwrap();
    assert_eq!(
        expected,
        TextExpectedValue {
            r#type: Some(text_expected_value::Type::Regex(ExpectedRegex {
                value: "^some regex$".to_string(),
            })),
        }
    );
}

#[test]
fn test_acquire_text_expected_values_fails_with_tampered_subject() {
    let original_content = b"^some regex$";
    let (signing_key, public_key) = test_util::new_random_signing_keypair();

    let not_before = oak_time::make_instant!("2025-09-01T12:00:00Z");
    let not_after = oak_time::make_instant!("2025-12-01T12:00:00Z");
    let now_utc_millis = make_valid_now_utc_millis(&Validity { not_before, not_after });

    let mut signed_endorsement = test_util::make_signed_endorsement_for_contents(
        original_content,
        not_before,
        not_after,
        &signing_key,
        vec![],
    );

    // Tamper the unsigned subject.
    signed_endorsement.endorsement.as_mut().unwrap().subject = b".*".to_vec();

    let reference_value = text_reference_value_for_endorser_pk(public_key);

    let result = super::acquire_text_expected_values(
        now_utc_millis,
        Some(&signed_endorsement),
        &reference_value,
    );
    assert!(result.is_err(), "expected error due to tampered subject, but it succeeded");
}
