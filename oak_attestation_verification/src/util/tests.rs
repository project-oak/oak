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

use alloc::borrow::ToOwned;

use oak_proto_rust::oak::{attestation::v1::TimestampReferenceValue, HexDigest};
use prost_types::{Duration, Timestamp};
use test_util::endorsement_data::EndorsementData;
use time::OffsetDateTime;

use crate::util::{
    convert_pem_to_raw, convert_raw_to_pem, convert_raw_to_verifying_key, equal_keys,
    get_hex_digest_match, verify_signature_ecdsa, verify_timestamp, MatchResult,
};

const HASH1: &str = "e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7";
const HASH2: &str = "5649a7882a83a8c1c333db046fd0a60e9bacedb3caab3c91578a7e21b1da89e3";
const HASH3: &str = "536c56245ccee62530dd5febd49821ba4a6161c0";
const HASH4: &str = "fc5ed8a3ba1da6717da6031760a2deb45c52b836";

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
fn test_both_empty_undecidable() {
    let empty = HexDigest { ..Default::default() };
    let result = get_hex_digest_match(&empty, &empty);
    assert!(result == MatchResult::Undecidable);
}

#[test]
fn test_one_empty_undecidable() {
    let a = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let empty = HexDigest { ..Default::default() };
    let result = get_hex_digest_match(&a, &empty);
    assert!(result == MatchResult::Undecidable);
}

#[test]
fn test_same() {
    let a = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let b = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let result = get_hex_digest_match(&a, &b);
    assert!(result == MatchResult::Same);
}

#[test]
fn test_different() {
    let a = HexDigest { sha2_256: HASH1.to_owned(), ..Default::default() };
    let b = HexDigest { sha2_256: HASH2.to_owned(), ..Default::default() };
    let result = get_hex_digest_match(&a, &b);
    assert!(result == MatchResult::Different);
}

#[test]
fn test_contradictory() {
    let a = HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let b = HexDigest { sha1: HASH4.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
    let result = get_hex_digest_match(&a, &b);
    assert!(result == MatchResult::Contradictory);
}

#[test]
fn test_verify_timestamp_valid_both_absolute_and_relative() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp = OffsetDateTime::from_unix_timestamp(1_599_999_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        not_before_relative: Some(Duration { seconds: -2_000_000, nanos: 0 }),
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_valid_only_absolute() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp = OffsetDateTime::from_unix_timestamp(1_599_999_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_valid_only_relative() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp = OffsetDateTime::from_unix_timestamp(1_599_999_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -2_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_valid_no_restrictions() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp = OffsetDateTime::from_unix_timestamp(1_599_999_000).unwrap();
    let reference_value = TimestampReferenceValue::default();
    assert!(verify_timestamp(now_utc_millis, &timestamp, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_invalid_absolute() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp = OffsetDateTime::from_unix_timestamp(1_400_000_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp, &reference_value).is_err());
}

#[test]
fn test_verify_timestamp_invalid_relative() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp = OffsetDateTime::from_unix_timestamp(1_500_000_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -1_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp, &reference_value).is_err());
}

#[test]
fn test_verify_timestamp_edge_case_absolute() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp_valid_abs = OffsetDateTime::from_unix_timestamp(1_500_000_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_absolute: Some(Timestamp { seconds: 1_500_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp_valid_abs, &reference_value).is_ok());
}

#[test]
fn test_verify_timestamp_edge_case_relative() {
    let now_utc_millis = 1_600_000_000_000;
    let timestamp_valid_rel = OffsetDateTime::from_unix_timestamp(1_599_000_000).unwrap();
    let reference_value = TimestampReferenceValue {
        not_before_relative: Some(Duration { seconds: -1_000_000, nanos: 0 }),
        ..Default::default()
    };
    assert!(verify_timestamp(now_utc_millis, &timestamp_valid_rel, &reference_value).is_ok());
}
