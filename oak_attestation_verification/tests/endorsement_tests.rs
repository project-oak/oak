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

use std::fs;

use oak_attestation_verification::{convert_pem_to_raw, raw_to_hex_digest, verify_endorsement};
use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{
    endorsement::Format, verifying_key_reference_value, ClaimReferenceValue, Endorsement,
    EndorsementReferenceValue, KeyType, Signature, SignedEndorsement, SkipVerification,
    VerifyingKey, VerifyingKeyReferenceValue, VerifyingKeySet,
};

const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";
const SIGNATURE_PATH: &str = "oak_attestation_verification/testdata/endorsement.json.sig";
const ENDORSER_PUBLIC_KEY_PATH: &str =
    "oak_attestation_verification/testdata/endorser_public_key.pem";
const LOG_ENTRY_PATH: &str = "oak_attestation_verification/testdata/logentry.json";
const REKOR_PUBLIC_KEY_PATH: &str = "oak_attestation_verification/testdata/rekor_public_key.pem";

// Pretend the tests run at this time: 1 March 2024, 12:00 UTC
const NOW_UTC_MILLIS: i64 = 1709294400000;

// Endorsement statement was invalid on: 28 March 2023, 10:40 UTC
const TOO_EARLY_UTC_MILLIS: i64 = 1680000000000;

// Endorsement statement was invalid on: 26 March 2025, 14:40 UTC
const TOO_LATE_UTC_MILLIS: i64 = 1743000000000;

const KEY_ID: u32 = 4711;

struct TestData {
    now_utc_millis: i64,
    signed_endorsement: SignedEndorsement,
    ref_value: EndorsementReferenceValue,
}

fn load_testdata() -> TestData {
    let endorsement = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
    let signature = fs::read(data_path(SIGNATURE_PATH)).expect("couldn't read signature");
    let log_entry = fs::read(data_path(LOG_ENTRY_PATH)).expect("couldn't read log entry");
    let endorser_public_key_pem = fs::read_to_string(data_path(ENDORSER_PUBLIC_KEY_PATH))
        .expect("couldn't read endorser public key");
    let rekor_public_key_pem = fs::read_to_string(data_path(REKOR_PUBLIC_KEY_PATH))
        .expect("couldn't read rekor public key");

    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    let endorsement = Endorsement {
        format: Format::EndorsementFormatJsonIntoto.into(),
        serialized: endorsement.clone(),
        ..Default::default()
    };
    let endorser_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: KEY_ID,
        raw: endorser_public_key.clone(),
    };
    let rekor_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: 0,
        raw: rekor_public_key.clone(),
    };

    TestData {
        now_utc_millis: NOW_UTC_MILLIS,
        signed_endorsement: SignedEndorsement {
            endorsement: Some(endorsement),
            signature: Some(Signature { key_id: KEY_ID, raw: signature.clone() }),
            rekor_log_entry: log_entry.clone(),
        },
        ref_value: EndorsementReferenceValue {
            endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
            required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
            rekor: Some(VerifyingKeyReferenceValue {
                r#type: Some(oak_proto_rust::oak::attestation::v1::verifying_key_reference_value::Type::Verify(
                    VerifyingKeySet { keys: [rekor_key].to_vec(), ..Default::default() },
                )),
            }),
            ..Default::default()
        },
    }
}

#[test]
fn test_verify_endorsement_success() {
    let testdata = load_testdata();

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_ok(), "{:?}", result);

    let details = result.unwrap();
    let d = raw_to_hex_digest(details.subject_digest.as_ref().unwrap());
    assert!(
        d.sha2_256 == "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc",
        "{:?}",
        details
    );
    assert!(details.validity.as_ref().unwrap().not_before == 1709113632000, "{:?}", details);
    assert!(details.validity.as_ref().unwrap().not_after == 1740649632000, "{:?}", details);
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
    let testdata = load_testdata();

    let result =
        verify_endorsement(TOO_EARLY_UTC_MILLIS, &testdata.signed_endorsement, &testdata.ref_value);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_too_late() {
    let testdata = load_testdata();

    let result =
        verify_endorsement(TOO_LATE_UTC_MILLIS, &testdata.signed_endorsement, &testdata.ref_value);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_empty_signature() {
    let mut testdata = load_testdata();

    testdata.signed_endorsement.signature.as_mut().expect("no signature").raw = "".into();

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_invalid_signature() {
    let mut testdata = load_testdata();

    testdata.signed_endorsement.signature.as_mut().expect("no signature").raw[0] ^= 1;

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_wrong_signature_key_id() {
    let mut testdata = load_testdata();

    testdata.signed_endorsement.signature.as_mut().expect("no signature").key_id += 1;

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_empty_endorser_key() {
    let mut testdata = load_testdata();

    testdata.ref_value.endorser.as_mut().expect("").keys.remove(0);

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_invalid_endorser_key() {
    let mut testdata = load_testdata();

    testdata.ref_value.endorser.as_mut().expect("").keys[0].raw[0] ^= 1;

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_wrong_endorser_key_id() {
    let mut testdata = load_testdata();

    testdata.ref_value.endorser.as_mut().expect("").keys[0].key_id += 1;

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_empty_rekor_key() {
    let mut testdata = load_testdata();

    let key_set = match testdata
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
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_invalid_rekor_key() {
    let mut testdata = load_testdata();

    let key_set = match testdata
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
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

// We cannot use key ID for Rekor since Rekor doesn't provide a key ID, so
//    fn test_verify_endorsement_fails_with_wrong_rekor_key_id() {}
// doesn't exist.

#[test]
fn test_verify_endorsement_fails_with_rekor_key_but_no_log_entry() {
    let mut testdata = load_testdata();

    testdata.signed_endorsement.rekor_log_entry.clear();

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_fails_with_no_rekor_reference_value() {
    let mut testdata = load_testdata();

    testdata.ref_value.rekor = None;

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_endorsement_succeeds_with_no_log_entry_and_no_rekor_key() {
    let mut testdata = load_testdata();

    testdata.ref_value.rekor = Some(VerifyingKeyReferenceValue {
        r#type: Some(
            oak_proto_rust::oak::attestation::v1::verifying_key_reference_value::Type::Skip(
                SkipVerification {},
            ),
        ),
    });
    testdata.signed_endorsement.rekor_log_entry.clear();

    let result = verify_endorsement(
        testdata.now_utc_millis,
        &testdata.signed_endorsement,
        &testdata.ref_value,
    );
    assert!(result.is_ok(), "{:?}", result);
}
