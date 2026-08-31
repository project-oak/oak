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
#![feature(test)]

extern crate test;

use std::sync::Arc;

use oak_attestation_verification::{
    AmdSevSnpDiceAttestationVerifier, AmdSevSnpPolicy, FirmwarePolicy, create_amd_verifier,
    verifier::{EventLogType, to_attestation_results, verify, verify_dice_chain},
    verify_endorsement,
};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::attestation::v1::{attestation_results::Status, reference_values};
use oak_time::clock::FixedClock;
use test::Bencher;
use test_util::{AttestationData, EndorsementData};

#[bench]
fn bench_verify_endorsement(b: &mut Bencher) {
    let d = EndorsementData::load_for_rekor_verification();

    b.iter(|| {
        let result = verify_endorsement(
            d.make_valid_time().into_unix_millis(),
            &d.signed_endorsement,
            &d.ref_value,
        );
        assert!(result.is_ok(), "{:?}", result);
    });
}

#[bench]
fn bench_verify_attestation_oc_legacy(b: &mut Bencher) {
    let d = AttestationData::load_milan_oc_release();

    b.iter(|| {
        let result = verify(
            d.make_valid_time().into_unix_millis(),
            &d.evidence,
            &d.endorsements,
            &d.reference_values,
        );
        let p = to_attestation_results(&result);

        assert!(result.is_ok(), "{:?}", result);
        assert!(p.status() == Status::Success);
    })
}

#[bench]
fn bench_verify_attestation_rk_legacy(b: &mut Bencher) {
    let d = AttestationData::load_milan_rk_release();

    b.iter(|| {
        let result = verify(
            d.make_valid_time().into_unix_millis(),
            &d.evidence,
            &d.endorsements,
            &d.reference_values,
        );
        let p = to_attestation_results(&result);

        assert!(result.is_ok(), "{:?}", result);
        assert!(p.status() == Status::Success);
    })
}

#[bench]
fn bench_verify_attestation_oc(b: &mut Bencher) {
    let d = AttestationData::load_milan_oc_release();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let verifier =
        create_amd_verifier(clock, &d.reference_values).expect("failed to create verifier");

    b.iter(|| {
        let result = verifier.verify(&d.evidence, &d.endorsements);
        assert!(result.is_ok(), "{:?}", result);
    })
}

#[bench]
fn bench_verify_attestation_rk(b: &mut Bencher) {
    let d = AttestationData::load_milan_rk_release();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let verifier =
        create_amd_verifier(clock, &d.reference_values).expect("failed to create verifier");

    b.iter(|| {
        let result = verifier.verify(&d.evidence, &d.endorsements);
        assert!(result.is_ok(), "{:?}", result);
    })
}

// The three benchmarks below decompose `bench_verify_attestation_oc`, which
// times all four steps of `AmdSevSnpDiceAttestationVerifier::verify` at once.
// Subtracting adjacent measurements separates them:
//
//   event log policies  = oc - oc_platform_and_firmware
//   platform + firmware = oc_platform_and_firmware - dice_chain_oc

/// The DICE chain walk alone: one signature verification per layer certificate.
#[bench]
fn bench_verify_dice_chain_oc(b: &mut Bencher) {
    let d = AttestationData::load_milan_oc_release();

    b.iter(|| {
        let result = verify_dice_chain(&d.evidence, EventLogType::OriginalEventLog);
        assert!(result.is_ok(), "{:?}", result);
    })
}

/// Platform policy (the P-384 SEV-SNP report and VCEK chain), the DICE chain
/// and the firmware policy, but no event log policies.
#[bench]
fn bench_verify_attestation_oc_platform_and_firmware(b: &mut Bencher) {
    let d = AttestationData::load_milan_oc_release();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let verifier = create_platform_and_firmware_only_verifier(&d, clock);

    b.iter(|| {
        let result = verifier.verify(&d.evidence, &d.endorsements);
        assert!(result.is_ok(), "{:?}", result);
    })
}

/// Same, for the Restricted Kernel stack.
#[bench]
fn bench_verify_attestation_rk_platform_and_firmware(b: &mut Bencher) {
    let d = AttestationData::load_milan_rk_release();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let verifier = create_platform_and_firmware_only_verifier(&d, clock);

    b.iter(|| {
        let result = verifier.verify(&d.evidence, &d.endorsements);
        assert!(result.is_ok(), "{:?}", result);
    })
}

/// As `create_amd_verifier`, minus the event policies. Kept in the test because
/// a verifier that checks no events should not be constructible by accident.
fn create_platform_and_firmware_only_verifier<T: oak_time::clock::Clock + 'static>(
    d: &AttestationData,
    clock: T,
) -> AmdSevSnpDiceAttestationVerifier {
    let root_rvs = match d.reference_values.r#type.as_ref().expect("no reference values") {
        reference_values::Type::OakContainers(rvs) => {
            rvs.root_layer.as_ref().expect("no root layer reference values")
        }
        reference_values::Type::OakRestrictedKernel(rvs) => {
            rvs.root_layer.as_ref().expect("no root layer reference values")
        }
        _ => panic!("unsupported reference values"),
    };
    let amd = root_rvs.amd_sev.as_ref().expect("no AMD SEV-SNP reference values");
    AmdSevSnpDiceAttestationVerifier::new(
        AmdSevSnpPolicy::new(amd),
        Box::new(FirmwarePolicy::new(amd.stage0.as_ref().expect("no stage0 reference value"))),
        vec![],
        Arc::new(clock),
    )
}
