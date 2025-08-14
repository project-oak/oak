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

use oak_attestation_verification::{
    create_amd_verifier,
    verifier::{to_attestation_results, verify},
    verify_endorsement,
};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::attestation::v1::attestation_results::Status;
use oak_time::clock::FixedClock;
use test::Bencher;
use test_util::{AttestationData, EndorsementData};

#[bench]
fn bench_verify_endorsement(b: &mut Bencher) {
    let d = EndorsementData::load();

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
