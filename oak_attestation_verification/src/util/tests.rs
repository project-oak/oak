//
// Copyright 2022 The Project Oak Authors
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
#[cfg(test)]
extern crate std;

use oak_proto_rust::oak::attestation::v1::TimestampReferenceValue;
use oak_time::Instant;
use prost_types::{Duration, Timestamp};
use test_util::endorsement_data::EndorsementData;

use crate::util::{
    convert_pem_to_raw, convert_raw_to_pem, convert_raw_to_verifying_key, equal_keys,
    verify_signature_ecdsa, verify_timestamp,
};

#[test]
fn test_convert_from_raw() {
    let d = EndorsementData::load();
    let key = convert_raw_to_verifying_key(&d.rekor_public_key);
    assert!(key.is_ok());
}

#[test]
fn test_convert_inverse_left() {
    let d = EndorsementData::load();
    let pem = convert_raw_to_pem(&d.rekor_public_key);
    let actual = convert_pem_to_raw(&pem).expect("could not convert key");
    assert!(equal_keys(&d.rekor_public_key, &actual).expect("could not compare keys"), "{:?}", pem);
}

#[test]
fn test_convert_inverse_right() {
    let d = EndorsementData::load();
    let raw = convert_pem_to_raw(&d.rekor_public_key_pem).expect("could not convert key");
    let actual = convert_raw_to_pem(&raw);
    assert!(
        actual.eq(&d.rekor_public_key_pem),
        "expected: {:?} actual: {:?}",
        &d.rekor_public_key_pem,
        actual
    );
}

#[test]
fn test_verify_signature_ecdsa() {
    let d = EndorsementData::load();
    let result = verify_signature_ecdsa(&d.signature, &d.endorsement, &d.endorser_public_key);
    assert!(result.is_ok());
}

#[test]
fn test_verify_timestamp_absolute_and_relative_success() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_599_999_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        not_before_relative: Some(Duration { seconds: -2_000_000, nanos: 0 }),
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_absolute_success() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_599_999_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_relative_success() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_599_999_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -2_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_empty_ref_value_success() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_599_999_000_000);
    let reference_value = TimestampReferenceValue::default();
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_absolute_failure() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_400_000_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_err());
}

#[test]
fn test_verify_timestamp_relative_failure() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_500_000_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -1_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_err());
}

#[test]
fn test_verify_timestamp_edge_case_absolute_success() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_500_000_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_edge_case_absolute_failure() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_500_000_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 1 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_err());
}

#[test]
fn test_verify_timestamp_edge_case_relative_success() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_599_000_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -1_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_edge_case_relative_failure() {
    let current_time = Instant::from_unix_millis(1_600_000_000_000);
    let timestamp = Instant::from_unix_millis(1_599_000_000_000);
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -1_000_000, nanos: 1 }),
        ..Default::default()
    };
    assert!(verify_timestamp(current_time, timestamp, &reference_value).is_err());
}
