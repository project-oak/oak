//
// Copyright 2023 The Project Oak Authors
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

use prost::Message;
use std::fs;

use oak_attestation_verification::{
    proto::oak::attestation::v1::{
        attestation_results::Status, Endorsements, Evidence, OakContainersEndorsements,
        OakContainersReferenceValues, ReferenceValues, RootLayerReferenceValues,
    },
    verifier::verify,
};

const EVIDENCE_PATH: &str = "testdata/evidence.binarypb";

// Creates a valid evidence instance.
fn create_evidence() -> Evidence {
    let serialized = fs::read(EVIDENCE_PATH).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates valid endorsements for an Oak Containers chain.
fn create_endorsements() -> Endorsements {
    let ends = OakContainersEndorsements {
        root_layer: None,
        kernel_layer: None,
        system_layer: None,
        container_layer: None,
    };
    Endorsements {
        r#type: Some(oak_attestation_verification::proto::oak::attestation::v1::endorsements::Type::OakContainers(ends)),
    }
}

// Creates valid reference values for an Oak Containers chain.
fn create_reference_values() -> ReferenceValues {
    let root_layer = RootLayerReferenceValues {
        amd_sev: None,
        intel_tdx: None,
    };

    let vs = OakContainersReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: None,
        system_layer: None,
        container_layer: None,
    };
    ReferenceValues {
        r#type: Some(oak_attestation_verification::proto::oak::attestation::v1::reference_values::Type::OakContainers(vs)),
    }
}

#[test]
fn verify_succeeds() {
    let evidence = create_evidence();
    let endorsements = create_endorsements();
    let reference_values = create_reference_values();

    let r = verify(&evidence, &endorsements, &reference_values);

    assert!(r.status() == Status::Success);
}

#[test]
fn verify_fails_with_manipulated_root_public_key() {
    let mut evidence = create_evidence();
    evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
    let endorsements = create_endorsements();
    let reference_values = create_reference_values();

    let r = verify(&evidence, &endorsements, &reference_values);

    println!("======================================");
    println!("code={} reason={}", r.status as i32, r.reason);
    println!("======================================");
    assert!(r.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_empty_args() {
    let evidence = Evidence::default();
    let endorsements = Endorsements::default();
    let reference_values = ReferenceValues::default();

    let r = verify(&evidence, &endorsements, &reference_values);

    assert!(r.status() == Status::GenericFailure);
}
