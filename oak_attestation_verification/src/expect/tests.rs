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

use oak_proto_rust::oak::{
    attestation::v1::{
        expected_digests, ExpectedDigests, RawDigests, TransparentReleaseEndorsement,
    },
    RawDigest,
};
use time::ext::NumericalDuration;

use crate::{test_util, util};

#[test]
fn test_get_expected_measurement_digest_validity() {
    // Create an endorsement of some arbitrary content.
    let measured_content = "Just some abitrary content";
    let content_digest = util::hash_sha2_256(measured_content.as_bytes());
    let endorsement = test_util::fake_endorsement(&content_digest);

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
    let now =
        endorsement.predicate.validity.as_ref().unwrap().not_before.saturating_add((7).days());
    let now_utc_millis = 1000 * now.unix_timestamp();
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
                digests: vec![RawDigest {
                    sha2_256: content_digest.to_vec(),
                    ..Default::default()
                }]
            })),
        }
    );
}
