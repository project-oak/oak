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

use oak_proto_rust::oak::{
    attestation::v1::{
        expected_digests, ExpectedDigests, FirmwareAttachment, KernelAttachment, RawDigests,
        TransparentReleaseEndorsement,
    },
    HexDigest,
};
use prost::Message;
use time::ext::NumericalDuration;

use crate::{
    endorsement::{FIRMWARE_CLAIM_TYPE, KERNEL_CLAIM_TYPE},
    test_util::{self, GetValidity},
    util::{self, UnixTimestampMillis},
};

// Same as raw_digest_from_contents, but emits hex encoded digest formats.
fn hex_digest_from_contents(contents: &[u8]) -> HexDigest {
    util::raw_to_hex_digest(&util::raw_digest_from_contents(contents))
}

#[test]
fn test_get_expected_measurement_digest_validity() {
    // Create an endorsement of some arbitrary content.
    let measured_content = b"Just some abitrary content";
    let content_digests = util::raw_digest_from_contents(measured_content);
    let endorsement = test_util::fake_endorsement(&content_digests, vec![]);
    let endorsement_validity = endorsement.predicate.validity.as_ref().expect("no validity");

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
    // Pretend it's a week into validity.
    let now_utc_millis =
        endorsement.validity().not_before.saturating_add((7).days()).unix_timestamp_millis();

    let expected_digests = super::get_expected_measurement_digest(
        now_utc_millis,
        Some(&tr_endorsement),
        &reference_value,
    )
    .expect("failed to get digests");

    // Assert that the expected digests are those from the verified endorsement.

    assert_eq!(
        expected_digests,
        ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                validity: Some(endorsement_validity.into()),
                digests: vec![content_digests],
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
    let measured_digest = util::raw_digest_from_contents(measured_content);
    let num_cpus = 2;
    configs.insert(num_cpus, util::raw_to_hex_digest(&measured_digest));
    let subject =
        FirmwareAttachment { binary: Some(hex_digest_from_contents(original_content)), configs };
    let serialized_subject = subject.encode_to_vec();

    // Now create the endorsement, containing the subject. The *endorsement*
    // hash is the hash of the serialized firmware attachment.
    let subject_digests = util::raw_digest_from_contents(&serialized_subject);
    let (signing_key, public_key) = test_util::new_random_signing_keypair();
    let endorsement = test_util::fake_endorsement(&subject_digests, vec![FIRMWARE_CLAIM_TYPE]);
    let endorsement_validity = endorsement.predicate.validity.as_ref().expect("no validity");
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
    // Pretend it's a week into the validity period.
    let now_utc_millis =
        endorsement.validity().not_before.saturating_add((7).days()).unix_timestamp_millis();
    let expected_digests =
        super::get_stage0_expected_values(now_utc_millis, Some(&tr_endorsement), &reference_value)
            .expect("failed to get digests");

    // We should have the hashes from the attachment.
    assert_eq!(
        expected_digests,
        ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                validity: Some(endorsement_validity.into()),
                digests: vec![measured_digest],
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
    let image_digest = util::raw_digest_from_contents(measured_image);
    let setup_digest = util::raw_digest_from_contents(measured_setup);
    let subject = KernelAttachment {
        bz_image: Some(bz_image_digest),
        image: Some(util::raw_to_hex_digest(&image_digest)),
        setup_data: Some(util::raw_to_hex_digest(&setup_digest)),
    };
    let serialized_subject = subject.encode_to_vec();

    // Now create the endorsement, containing the subject. The *endorsement*
    // hash is the hash of the serialized kernel attachment.
    let subject_digests = util::raw_digest_from_contents(&serialized_subject);
    let (signing_key, public_key) = test_util::new_random_signing_keypair();
    let endorsement = test_util::fake_endorsement(&subject_digests, vec![KERNEL_CLAIM_TYPE]);
    let endorsement_validity = endorsement.predicate.validity.as_ref().expect("no validity");
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
    // Pretend it's a week into the validity period.
    let now_utc_millis =
        endorsement.validity().not_before.saturating_add((7).days()).unix_timestamp_millis();
    let expected_digests =
        super::get_kernel_expected_values(now_utc_millis, Some(&tr_endorsement), &reference_value)
            .expect("failed to get digests");

    // We should have the hashes from the attachment.
    assert_eq!(
        expected_digests.image,
        Some(ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                validity: Some(endorsement_validity.into()),
                digests: vec![image_digest],
            })),
        })
    );
    assert_eq!(
        expected_digests.setup_data,
        Some(ExpectedDigests {
            r#type: Some(expected_digests::Type::Digests(RawDigests {
                validity: Some(endorsement_validity.into()),
                digests: vec![setup_digest],
            })),
        })
    );
}
