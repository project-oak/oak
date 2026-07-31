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

extern crate alloc;
extern crate std;

use alloc::{string::ToString, vec, vec::Vec};
use std::{collections::BTreeMap, fs};

use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::ClaimReferenceValue;
use oak_time::{Duration, Instant};
use test_util::EndorsementData;

use crate::statement::{
    Claim, DefaultStatement, Validity, get_hex_digest_from_statement, parse_statement,
};

const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";

// Minimum supported value for Timestamp: 0001-01-01 00:00:00.0 +00:00:00.
const MIN_VALUE_MILLIS: i64 = -62_135_596_800_000;
const MIN_VALUE_NANOS: i128 = 1_000_000 * MIN_VALUE_MILLIS as i128;

// Maximum supported value for Timestamp: 9999-12-31 23:59:59.0 +00:00:00
const MAX_VALUE_MILLIS: i64 = 253_402_300_799_000;
const MAX_VALUE_NANOS: i128 = 1_000_000 * MAX_VALUE_MILLIS as i128;

#[test]
fn test_get_hex_digest_from_statement() {
    let endorsement = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
    let statement = parse_statement(&endorsement).expect("couldn't parse statement");
    let digest =
        get_hex_digest_from_statement(&statement).expect("failed to get digest from claim");

    assert_eq!(digest.sha2_256, "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc");
}

#[test]
fn test_convert_validity_left_min() {
    let expected = Validity {
        not_before: Instant::from_unix_nanos(MIN_VALUE_NANOS),
        not_after: Instant::from_unix_nanos(0),
    };
    let proto = oak_proto_rust::oak::Validity::from(&expected);
    let actual = Validity::try_from(&proto).expect("failed to convert");
    assert_eq!(expected, actual);
}

#[test]
fn test_convert_validity_left_max() {
    let expected = Validity {
        not_before: Instant::from_unix_nanos(0),
        not_after: Instant::from_unix_nanos(MAX_VALUE_NANOS),
    };
    let proto = oak_proto_rust::oak::Validity::from(&expected);
    let actual = Validity::try_from(&proto).expect("failed to convert");
    assert_eq!(expected, actual);
}

#[test]
fn test_convert_validity_right_min() {
    let expected: oak_proto_rust::oak::Validity = oak_proto_rust::oak::Validity {
        not_before: Some(Instant::from_unix_millis(MIN_VALUE_MILLIS).into_timestamp()),
        not_after: Some(Instant::from_unix_millis(0).into_timestamp()),
    };
    let statement = Validity::try_from(&expected).expect("failed to convert");
    let actual = oak_proto_rust::oak::Validity::from(&statement);
    assert_eq!(expected, actual);
}

#[test]
fn test_convert_validity_right_max() {
    let expected: oak_proto_rust::oak::Validity = oak_proto_rust::oak::Validity {
        not_before: Some(Instant::from_unix_millis(0).into_timestamp()),
        not_after: Some(Instant::from_unix_millis(MAX_VALUE_MILLIS).into_timestamp()),
    };
    let statement = Validity::try_from(&expected).expect("failed to convert");
    let actual = oak_proto_rust::oak::Validity::from(&statement);
    assert_eq!(expected, actual);
}

#[test]
fn test_validate_endorsement_statement_success() {
    let d = EndorsementData::load_for_rekor_verification();
    let statement = parse_statement(&d.endorsement).expect("could not parse endorsement statement");

    let result = statement.validate(
        None,
        d.make_valid_time(),
        &oak_proto_rust::oak::attestation::v1::ClaimReferenceValue::default(),
    );

    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_validate_endorsement_statement_fails_too_early() {
    let d = EndorsementData::load_for_rekor_verification();
    let statement = parse_statement(&d.endorsement).expect("could not parse endorsement statement");
    let too_early = d.valid_not_before - Duration::from_seconds(24 * 3_600);

    let result = statement.validate(
        None,
        too_early,
        &oak_proto_rust::oak::attestation::v1::ClaimReferenceValue::default(),
    );

    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_validate_statement_fails_too_late() {
    let d = EndorsementData::load_for_rekor_verification();
    let statement = parse_statement(&d.endorsement).expect("could not parse endorsement statement");
    let too_late = d.valid_not_after + Duration::from_seconds(24 * 3_600);

    let result = statement.validate(None, too_late, &ClaimReferenceValue::default());

    assert!(result.is_err(), "{:?}", result);
}

fn make_test_statement_with_claims(claims: Vec<Claim>) -> (DefaultStatement, Instant) {
    let d = EndorsementData::load_for_rekor_verification();
    let mut statement =
        parse_statement(&d.endorsement).expect("could not parse endorsement statement");
    statement.predicate.claims = claims;
    (statement, d.make_valid_time())
}

#[test]
fn test_validate_claims_success_with_extra() {
    let mut annotations = BTreeMap::new();
    annotations.insert("key1".to_string(), "value1".to_string());
    annotations.insert("extra_key2".to_string(), "extra_value2".to_string());

    let req_annotations = [("key1".to_string(), "value1".to_string())].into_iter().collect();
    let required_claims = ClaimReferenceValue {
        claims: vec![oak_proto_rust::oak::attestation::v1::Claim {
            r#type: "type1".to_string(),
            annotations: req_annotations,
        }],
        ..Default::default()
    };

    let (statement, valid_time) =
        make_test_statement_with_claims(vec![Claim { r#type: "type1".to_string(), annotations }]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_validate_claims_fails_wrong_value() {
    let mut annotations = BTreeMap::new();
    // Claim provides "wrong_value" instead of "value1"
    annotations.insert("key1".to_string(), "wrong_value".to_string());

    let req_annotations = [("key1".to_string(), "value1".to_string())].into_iter().collect();
    let required_claims = ClaimReferenceValue {
        claims: vec![oak_proto_rust::oak::attestation::v1::Claim {
            r#type: "type1".to_string(),
            annotations: req_annotations,
        }],
        ..Default::default()
    };

    let (statement, valid_time) =
        make_test_statement_with_claims(vec![Claim { r#type: "type1".to_string(), annotations }]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_validate_claims_fails_no_annotations() {
    let annotations = BTreeMap::new();

    let req_annotations = [("key1".to_string(), "value1".to_string())].into_iter().collect();
    let required_claims = ClaimReferenceValue {
        claims: vec![oak_proto_rust::oak::attestation::v1::Claim {
            r#type: "type1".to_string(),
            annotations: req_annotations,
        }],
        ..Default::default()
    };

    let (statement, valid_time) =
        make_test_statement_with_claims(vec![Claim { r#type: "type1".to_string(), annotations }]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_validate_claims_multiple_claims_same_type() {
    let mut annotations1 = BTreeMap::new();
    annotations1.insert("key1".to_string(), "val1".to_string());

    let mut annotations2 = BTreeMap::new();
    annotations2.insert("key1".to_string(), "val2".to_string());

    let req_annotations = [("key1".to_string(), "val2".to_string())].into_iter().collect();
    let required_claims = ClaimReferenceValue {
        claims: vec![oak_proto_rust::oak::attestation::v1::Claim {
            r#type: "type1".to_string(),
            annotations: req_annotations,
        }],
        ..Default::default()
    };

    let (statement, valid_time) = make_test_statement_with_claims(vec![
        Claim { r#type: "type1".to_string(), annotations: annotations1 },
        Claim { r#type: "type1".to_string(), annotations: annotations2 },
    ]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_validate_claims_fails_missing_key() {
    let mut annotations = BTreeMap::new();
    annotations.insert("key1".to_string(), "value1".to_string());

    let req_annotations = [("missing_key".to_string(), "value1".to_string())].into_iter().collect();
    let required_claims = ClaimReferenceValue {
        claims: vec![oak_proto_rust::oak::attestation::v1::Claim {
            r#type: "type1".to_string(),
            annotations: req_annotations,
        }],
        ..Default::default()
    };

    let (statement, valid_time) =
        make_test_statement_with_claims(vec![Claim { r#type: "type1".to_string(), annotations }]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_validate_claims_legacy_and_new_claims_success() {
    let mut annotations = BTreeMap::new();
    annotations.insert("key1".to_string(), "value1".to_string());

    let req_annotations = [("key1".to_string(), "value1".to_string())].into_iter().collect();
    #[allow(deprecated)]
    let required_claims = ClaimReferenceValue {
        claim_types: vec!["legacy_type".to_string()],
        claims: vec![oak_proto_rust::oak::attestation::v1::Claim {
            r#type: "new_type".to_string(),
            annotations: req_annotations,
        }],
    };

    let (statement, valid_time) = make_test_statement_with_claims(vec![
        Claim { r#type: "legacy_type".to_string(), annotations: BTreeMap::new() },
        Claim { r#type: "new_type".to_string(), annotations },
    ]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_validate_claims_legacy_fallback_when_claims_empty() {
    #[allow(deprecated)]
    let required_claims =
        ClaimReferenceValue { claim_types: vec!["legacy_type".to_string()], claims: vec![] };

    let (statement, valid_time) = make_test_statement_with_claims(vec![Claim {
        r#type: "legacy_type".to_string(),
        annotations: BTreeMap::new(),
    }]);

    let result = statement.validate(None, valid_time, &required_claims);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_serde_json_claim_roundtrip() {
    // 1. Claim with empty annotations: should omit "annotations" field in JSON
    let claim_empty =
        Claim { r#type: "http://example.com/claim".to_string(), annotations: BTreeMap::new() };
    let json_empty = serde_json::to_string(&claim_empty).expect("failed to serialize empty claim");
    assert!(
        !json_empty.contains("annotations"),
        "expected 'annotations' field to be omitted when empty: {}",
        json_empty
    );
    let deserialized_empty: Claim =
        serde_json::from_str(&json_empty).expect("failed to deserialize empty claim");
    assert_eq!(claim_empty, deserialized_empty);

    // 2. Claim with non-empty annotations: should include "annotations" field in
    //    JSON
    let mut annotations = BTreeMap::new();
    annotations.insert("key1".to_string(), "val1".to_string());
    let claim_with_ann = Claim { r#type: "http://example.com/claim".to_string(), annotations };
    let json_with_ann =
        serde_json::to_string(&claim_with_ann).expect("failed to serialize claim with annotations");
    assert!(
        json_with_ann.contains("annotations"),
        "expected 'annotations' field in JSON: {}",
        json_with_ann
    );
    let deserialized_with_ann: Claim =
        serde_json::from_str(&json_with_ann).expect("failed to deserialize claim with annotations");
    assert_eq!(claim_with_ann, deserialized_with_ann);
}
