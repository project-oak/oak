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

use digest_util::raw_to_hex_digest;
use oak_attestation_verification::verify_endorsement;
use oak_proto_rust::oak::attestation::v1::{
    SkipVerification, VerifyingKeyReferenceValue, verifying_key_reference_value,
};
use oak_time::{Duration, Instant};
use test_util::endorsement_data::EndorsementData;

#[test]
#[allow(deprecated)]
fn test_verify_endorsement_success() {
    let d = EndorsementData::load();

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_ok(), "{:?}", result);

    let details = result.unwrap();
    let digest = raw_to_hex_digest(details.subject_digest.as_ref().unwrap());
    assert!(
        digest.sha2_256 == "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc",
        "{:?}",
        details
    );

    let actual_not_before = Instant::from(details.valid.as_ref().unwrap().not_before.unwrap());
    let actual_not_after = Instant::from(details.valid.as_ref().unwrap().not_after.unwrap());
    assert!(actual_not_before.into_unix_millis() == 1_709_113_632_067, "{:?}", details);
    assert!(actual_not_after.into_unix_millis() == 1_740_649_632_067, "{:?}", details);

    assert!(details.claim_types.len() == 2, "{:?}", details);
    assert!(
        details.claim_types[0] == "https://project-oak.github.io/oak/test_claim_1",
        "{:?}",
        details
    );
    assert!(
        details.claim_types[1] == "https://project-oak.github.io/oak/test_claim_2",
        "{:?}",
        details
    );
}

#[test]
fn test_verify_endorsement_fails_too_early() {
    let d = EndorsementData::load();
    let too_early = d.valid_not_before - Duration::from_seconds(3_600);
    let result =
        verify_endorsement(too_early.into_unix_millis(), &d.signed_endorsement, &d.ref_value);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_too_late() {
    let d = EndorsementData::load();
    let too_late = d.valid_not_after + Duration::from_seconds(3_600);

    let result =
        verify_endorsement(too_late.into_unix_millis(), &d.signed_endorsement, &d.ref_value);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_at_not_before_boundary() {
    let d = EndorsementData::load();
    let details = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    )
    .unwrap();
    let not_before = Instant::from(details.valid.as_ref().unwrap().not_before.unwrap());
    let not_before_millis = not_before.into_unix_millis();

    let expected_success =
        verify_endorsement(not_before_millis, &d.signed_endorsement, &d.ref_value);
    let expected_failure =
        verify_endorsement(not_before_millis - 1, &d.signed_endorsement, &d.ref_value);

    assert!(expected_success.is_ok(), "{:?}", expected_success);
    assert!(expected_failure.is_err(), "{:?}", expected_failure);
}

#[test]
fn test_verify_endorsement_at_not_after_boundary() {
    let d = EndorsementData::load();
    let details = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    )
    .unwrap();
    let not_after = Instant::from(details.valid.as_ref().unwrap().not_after.unwrap());
    let not_after_millis = not_after.into_unix_millis();

    let expected_success =
        verify_endorsement(not_after_millis, &d.signed_endorsement, &d.ref_value);
    let expected_failure =
        verify_endorsement(not_after_millis + 1, &d.signed_endorsement, &d.ref_value);

    assert!(expected_success.is_ok(), "{:?}", expected_success);
    assert!(expected_failure.is_err(), "{:?}", expected_failure);
}

#[test]
fn test_verify_endorsement_fails_with_empty_signature() {
    let mut d = EndorsementData::load();

    d.signed_endorsement.signature.as_mut().expect("no signature").raw = "".into();

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_invalid_signature() {
    let mut d = EndorsementData::load();

    d.signed_endorsement.signature.as_mut().expect("no signature").raw[0] ^= 1;

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_wrong_signature_key_id() {
    let mut d = EndorsementData::load();

    d.signed_endorsement.signature.as_mut().expect("no signature").key_id += 1;

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_empty_endorser_key() {
    let mut d = EndorsementData::load();

    d.ref_value.endorser.as_mut().expect("").keys.remove(0);

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_invalid_endorser_key() {
    let mut d = EndorsementData::load();

    d.ref_value.endorser.as_mut().expect("").keys[0].raw[0] ^= 1;

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_wrong_endorser_key_id() {
    let mut d = EndorsementData::load();

    d.ref_value.endorser.as_mut().expect("").keys[0].key_id += 1;

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_empty_rekor_key() {
    let mut d = EndorsementData::load();

    let key_set = match d
        .ref_value
        .rekor
        .as_mut()
        .expect("no verifying key reference value")
        .r#type
        .as_mut()
        .expect("no key set")
    {
        verifying_key_reference_value::Type::Verify(ks) => ks,
        _ => panic!("wrong reference value type"),
    };

    key_set.keys.remove(0);

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_invalid_rekor_key() {
    let mut d = EndorsementData::load();

    let key_set = match d
        .ref_value
        .rekor
        .as_mut()
        .expect("no verifying key reference value")
        .r#type
        .as_mut()
        .expect("no key set")
    {
        verifying_key_reference_value::Type::Verify(ks) => ks,
        _ => panic!("wrong reference value type"),
    };

    key_set.keys[0].raw[0] ^= 1;

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

// We cannot use key ID for Rekor since Rekor doesn't provide a key ID, so
//    fn test_verify_endorsement_fails_with_wrong_rekor_key_id() {}
// doesn't exist.

#[test]
fn test_verify_endorsement_fails_with_rekor_key_but_no_log_entry() {
    let mut d = EndorsementData::load();

    d.signed_endorsement.rekor_log_entry.clear();

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_no_rekor_reference_value() {
    let mut d = EndorsementData::load();

    d.ref_value.rekor = None;

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_succeeds_with_no_log_entry_and_no_rekor_key() {
    let mut d = EndorsementData::load();

    d.ref_value.rekor = Some(VerifyingKeyReferenceValue {
        r#type: Some(
            oak_proto_rust::oak::attestation::v1::verifying_key_reference_value::Type::Skip(
                SkipVerification {},
            ),
        ),
    });
    d.signed_endorsement.rekor_log_entry.clear();

    let result = verify_endorsement(
        d.make_valid_time().into_unix_millis(),
        &d.signed_endorsement,
        &d.ref_value,
    );
    assert!(result.is_ok(), "{:?}", result);
}
