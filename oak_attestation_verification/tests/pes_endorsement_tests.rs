//
// Copyright 2026 The Project Oak Authors
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

use oak_attestation_verification::{ContainerPolicy, verify_pes_endorsement};
use oak_attestation_verification_types::policy::Policy;
use oak_digest::raw_to_hex_digest;
use oak_proto_rust::oak::{
    RawDigest, Variant,
    attestation::v1::{
        BinaryReferenceValue, Claim, ClaimReferenceValue, ContainerEndorsement, ContainerLayerData,
        ContainerLayerReferenceValues, Event, SkipVerification, binary_reference_value,
    },
};
use oak_time::{Duration, Instant};
use prost_types::Any;
use test_util::endorsement_data::EndorsementData;

#[test]
fn test_verify_pes_endorsement_success() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let ref_value = d.pes_ref_value();

    let result = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_ok(), "{:?}", result);

    let details = result.unwrap();
    let digest = raw_to_hex_digest(details.subject_digest.as_ref().unwrap());
    assert!(
        digest.sha2_256 == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "{:?}",
        details
    );

    let actual_not_before = Instant::from(details.valid.as_ref().unwrap().not_before.unwrap());
    let actual_not_after = Instant::from(details.valid.as_ref().unwrap().not_after.unwrap());
    assert!(actual_not_before.into_unix_millis() == 1_772_704_800_000, "{:?}", details);
    assert!(actual_not_after.into_unix_millis() == 1_788_256_800_000, "{:?}", details);

    assert!(details.claim_types.len() == 3, "{:?}", details);
    assert!(
        details.claim_types[0]
            == "https://github.com/private-compute-infra-toolkit/public-endorsement-service/blob/main/docs/claims/publisher.md",
        "{:?}",
        details
    );
    assert!(
        details.claim_types[1]
            == "https://github.com/private-compute-infra-toolkit/public-endorsement-service/blob/main/docs/claims/workload.md",
        "{:?}",
        details
    );
    assert!(
        details.claim_types[2]
            == "https://github.com/project-oak/oak/blob/main/docs/tr/claim/85483.md",
        "{:?}",
        details
    );
}

#[test]
fn test_verify_pes_endorsement_fails_too_early() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let ref_value = d.pes_ref_value();

    let too_early = d.valid_not_before - Duration::from_seconds(3_600);
    let result = verify_pes_endorsement(
        too_early.into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_pes_endorsement_fails_too_late() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let ref_value = d.pes_ref_value();

    let too_late = d.valid_not_after + Duration::from_seconds(3_600);
    let result = verify_pes_endorsement(
        too_late.into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_pes_endorsement_at_not_before_boundary() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let ref_value = d.pes_ref_value();

    let details = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    )
    .unwrap();
    let not_before = Instant::from(details.valid.as_ref().unwrap().not_before.unwrap());
    let not_before_millis = not_before.into_unix_millis();

    let expected_success =
        verify_pes_endorsement(not_before_millis, endorsement, pes_confirmation, &ref_value);
    let expected_failure =
        verify_pes_endorsement(not_before_millis - 1, endorsement, pes_confirmation, &ref_value);

    assert!(expected_success.is_ok(), "{:?}", expected_success);
    assert!(expected_failure.is_err(), "{:?}", expected_failure);
}

#[test]
fn test_verify_pes_endorsement_at_not_after_boundary() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let ref_value = d.pes_ref_value();

    let details = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    )
    .unwrap();
    let not_after = Instant::from(details.valid.as_ref().unwrap().not_after.unwrap());
    let not_after_millis = not_after.into_unix_millis();

    let expected_success =
        verify_pes_endorsement(not_after_millis, endorsement, pes_confirmation, &ref_value);
    let expected_failure =
        verify_pes_endorsement(not_after_millis + 1, endorsement, pes_confirmation, &ref_value);

    assert!(expected_success.is_ok(), "{:?}", expected_success);
    assert!(expected_failure.is_err(), "{:?}", expected_failure);
}

#[test]
fn test_verify_pes_endorsement_fails_with_empty_pes_key() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let mut ref_value = d.pes_ref_value();

    ref_value.key_set.as_mut().unwrap().keys.clear();

    let result = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_pes_endorsement_fails_with_invalid_pes_key() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let mut ref_value = d.pes_ref_value();

    ref_value.key_set.as_mut().unwrap().keys[0].raw[0] ^= 1;

    let result = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_pes_endorsement_fails_with_corrupted_pes_confirmation() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let mut pes_confirmation = d.signed_endorsement.pes_confirmation.clone();
    pes_confirmation[0] ^= 1;
    let ref_value = d.pes_ref_value();

    let result = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        &pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_pes_endorsement_fails_with_wrong_publisher_id() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let mut ref_value = d.pes_ref_value();
    ref_value.publisher_id = "wrong-publisher@google.com".to_string();

    let result = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
}

#[test]
fn test_verify_pes_endorsement_fails_when_additional_required_claims_has_publisher_id() {
    let d = EndorsementData::load_for_pes_verification();
    let endorsement = d.signed_endorsement.endorsement.as_ref().unwrap();
    let pes_confirmation = d.signed_endorsement.pes_confirmation.as_slice();
    let mut ref_value = d.pes_ref_value();

    let req_claims = ClaimReferenceValue {
        claims: vec![Claim {
            r#type: "https://github.com/private-compute-infra-toolkit/public-endorsement-service/blob/main/docs/claims/publisher.md".to_string(),
            annotations: Default::default(),
        }],
        ..Default::default()
    };
    ref_value.additional_required_claims = Some(req_claims);

    let result = verify_pes_endorsement(
        d.make_valid_time().into_unix_millis(),
        endorsement,
        pes_confirmation,
        &ref_value,
    );
    assert!(result.is_err(), "{:?}", result);
    assert!(
        result.unwrap_err().to_string().contains("invalid argument"),
        "expected error to contain invalid argument"
    );
}

#[test]
fn test_container_policy_verify_with_pes_endorsement() {
    let d = EndorsementData::load_for_pes_verification();
    let ref_value = d.pes_ref_value();

    let layer_ref_values = ContainerLayerReferenceValues {
        binary: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::PesEndorsement(ref_value)),
        }),
        configuration: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
        }),
    };

    let policy = ContainerPolicy::new(&layer_ref_values);

    let event_data = ContainerLayerData {
        bundle: Some(RawDigest {
            sha2_256: hex::decode(
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            )
            .unwrap(),
            ..Default::default()
        }),
        config: Some(RawDigest::default()),
        ..Default::default()
    };
    let event = Event {
        tag: "container_layer".to_string(),
        event: Some(Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ContainerLayerData".to_string(),
            value: prost::Message::encode_to_vec(&event_data),
        }),
    };
    let event_bytes = prost::Message::encode_to_vec(&event);

    let container_endorsement =
        ContainerEndorsement { binary: Some(d.signed_endorsement.clone()), configuration: None };
    let variant = Variant::from(container_endorsement);

    let result = policy.verify(d.make_valid_time(), &event_bytes, &variant);
    assert!(result.is_ok(), "{:?}", result);
}
