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

use std::{fs, sync::Arc};

use oak_attestation_verification::{
    create_amd_verifier,
    verifier::{verify_dice_chain_and_extract_evidence, SoftwareRootedDiceAttestationVerifier},
    AmdSevSnpDiceAttestationVerifier, AmdSevSnpPolicy, FirmwarePolicy,
};
use oak_attestation_verification_types::{policy::EventPolicy, verifier::AttestationVerifier};
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results, binary_reference_value, endorsements, AmdSevSnpEndorsement,
        AttestationResults, Endorsements, Evidence, ReferenceValues, SkipVerification,
    },
    Variant,
};
use oak_time::{clock::FixedClock, Instant};
use prost::Message;
use test_util::{
    create_reference_values_for_extracted_evidence, get_cb_reference_values, AttestationData,
};

use crate::attestation_results::Status;

const CB_EVIDENCE_SR_PATH: &str =
    "oak_attestation_verification/testdata/cb_evidence_software_rooted.binarypb";

// A random time value used to parametrize test cases.
const TEST_TIME: Instant = Instant::from_unix_millis(1_000_000);

// Helper which asserts success of the verification call.
fn assert_success(result: anyhow::Result<AttestationResults>) {
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());

    let proto = result.as_ref().unwrap();
    if proto.status() != Status::Success {
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(proto.status() == Status::Success);
}

// Helper which asserts failure of the verification call.
fn assert_failure(result: anyhow::Result<AttestationResults>) {
    if result.is_ok() {
        let proto = result.as_ref().unwrap();
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(result.is_err());
}

// Shorthand that produces digest-based reference values from evidence.
fn make_reference_values(evidence: &Evidence) -> ReferenceValues {
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(evidence).expect("invalid DICE evidence");
    create_reference_values_for_extracted_evidence(extracted_evidence)
}

fn load_cb_evidence_software_rooted() -> Evidence {
    let serialized = fs::read(data_path(CB_EVIDENCE_SR_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

#[test]
fn cb_software_rooted_dice_verify_succeeds() {
    let clock = FixedClock::at_instant(TEST_TIME);
    let evidence = load_cb_evidence_software_rooted();
    let endorsements = Endorsements::default();

    let verifier = SoftwareRootedDiceAttestationVerifier::new(Arc::new(clock));

    let result = verifier.verify(&evidence, &endorsements);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn cb_dice_verify_succeeds() {
    let d = AttestationData::load_cb();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let ref_values = get_cb_reference_values(&d.reference_values);
    let platform_endorsement = AmdSevSnpEndorsement {
        tee_certificate: match d.endorsements.r#type.as_ref() {
            Some(endorsements::Type::Cb(e)) => {
                e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
            }
            _ => vec![],
        },
    };
    let empty_variant: Variant = Variant::default();
    let endorsements = Endorsements {
        platform: Some(platform_endorsement.into()),
        initial: Some(empty_variant),
        ..Default::default()
    };

    let platform_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
    let platform_policy = AmdSevSnpPolicy::new(platform_reference_values);

    let firmware_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap().stage0.as_ref().unwrap();
    // TODO: b/375137648 - Use real reference once new endorsements are available.
    let mut skip_firmware_reference_values = firmware_reference_values.clone();
    skip_firmware_reference_values.r#type =
        Some(binary_reference_value::Type::Skip(SkipVerification {}));
    let firmware_policy = FirmwarePolicy::new(&skip_firmware_reference_values);

    let event_policies: Vec<Box<dyn EventPolicy>> = vec![];

    let verifier = AmdSevSnpDiceAttestationVerifier::new(
        platform_policy,
        Box::new(firmware_policy),
        event_policies,
        Arc::new(clock),
    );

    let result = verifier.verify(&d.evidence, &endorsements);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

fn verify_amd(
    timestamp: Instant,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<AttestationResults> {
    let clock = FixedClock::at_instant(timestamp);
    let v = create_amd_verifier(clock, reference_values).expect("no verifier");
    v.verify(evidence, endorsements)
}

macro_rules! verify_amd_success {
    ($($name:tt)*) => {
        mod verify_amd_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    assert_success(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_amd_success! {
    load_milan_oc_release
    load_milan_oc_staging
    // Requires event-based endorsements for both. Enable once we have them.
    // load_genoa_oc
    // load_turin_oc
    load_milan_rk_release
    load_milan_rk_staging
}

macro_rules! verify_amd_success_explicit_reference_values {
    ($($name:tt)*) => {
        mod verify_amd_success_explicit_reference_values {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    let reference_values = make_reference_values(&d.evidence);
                    assert_success(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &reference_values));
                }
            )*
        }
    }
}

verify_amd_success_explicit_reference_values! {
    load_milan_oc_release
    load_milan_oc_staging
    // Requires event-based endorsements for both. Enable once we have them.
    // load_genoa_oc
    // load_turin_oc
    load_milan_rk_release
    load_milan_rk_staging
}

macro_rules! verify_amd_manipulated_root_public_key_failure {
    ($($name:tt)*) => {
        mod verify_amd_manipulated_root_public_key_failure {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();
                    d.evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
                    assert_failure(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_amd_manipulated_root_public_key_failure! {
    load_milan_oc_release
    load_milan_oc_staging
    // Requires event-based endorsements for both. Enable once we have them.
    // load_genoa_oc
    // load_turin_oc
    load_milan_rk_release
    load_milan_rk_staging
}
