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

extern crate std;
use std::fs;

use oak_file_utils::data_path;
use oak_time::{Duration, Instant};
use test_util::EndorsementData;

use crate::statement::{Validity, get_hex_digest_from_statement, parse_statement};

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
    let d = EndorsementData::load();
    let statement = parse_statement(&d.endorsement).expect("could not parse endorsement statement");

    let result = statement.validate(None, d.make_valid_time(), &[]);

    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_validate_endorsement_statement_fails_too_early() {
    let d = EndorsementData::load();
    let statement = parse_statement(&d.endorsement).expect("could not parse endorsement statement");
    let too_early = d.valid_not_before - Duration::from_seconds(24 * 3_600);

    let result = statement.validate(None, too_early, &[]);

    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_validate_statement_fails_too_late() {
    let d = EndorsementData::load();
    let statement = parse_statement(&d.endorsement).expect("could not parse endorsement statement");
    let too_late = d.valid_not_after + Duration::from_seconds(24 * 3_600);

    let result = statement.validate(None, too_late, &[]);

    assert!(result.is_err(), "{:?}", result);
}
