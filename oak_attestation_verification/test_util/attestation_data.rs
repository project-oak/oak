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

// Provides convenient access to attestation verification test data.

use std::fs;

use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence, ReferenceValues};
use oak_time::Instant;
use prost::Message;
use time::macros::utc_datetime;

const OC_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/oc_evidence_20241205.binarypb";
const OC_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/oc_endorsements_20241205.binarypb";
const OC_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/oc_reference_values_20241205.binarypb";

const RK_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/rk_evidence_20241205.binarypb";
const RK_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/rk_endorsements_20241205.binarypb";
const RK_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/rk_reference_values_20241205.binarypb";

const CB_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/cb_evidence.binarypb";
const CB_ENDORSEMENTS_PATH: &str = "oak_attestation_verification/testdata/cb_endorsements.binarypb";
const CB_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/cb_reference_values.binarypb";

// AMD Genoa attestation with Oak Containers, with legacy endorsements.
const GENOA_OC_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_evidence.binarypb";
const GENOA_OC_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_endorsements.binarypb";
const GENOA_OC_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_reference_values.binarypb";

pub struct AttestationData {
    pub valid_not_before: Instant,
    pub valid_not_after: Instant,
    pub evidence: Evidence,
    pub endorsements: Endorsements,
    pub reference_values: ReferenceValues,
}

impl AttestationData {
    /// Loads a current attestation example for Oak Containers.
    pub fn load_oc() -> AttestationData {
        AttestationData {
            valid_not_before: Instant::from(utc_datetime!(2025-05-27 06:06:03.987000)),
            valid_not_after: Instant::from(utc_datetime!(2025-08-25 06:06:03.471000)),
            evidence: load_evidence(OC_EVIDENCE_PATH),
            endorsements: load_endorsements(OC_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(OC_REFERENCE_VALUES_PATH),
        }
    }

    pub fn load_oc_legacy_genoa() -> AttestationData {
        AttestationData {
            // Validity is not used since there are no endorsements.
            valid_not_before: Instant::from(utc_datetime!(2024-01-01 00:00:00.000000)),
            valid_not_after: Instant::from(utc_datetime!(2024-12-31 23:00:00.000000)),
            evidence: load_evidence(GENOA_OC_EVIDENCE_PATH),
            endorsements: load_endorsements(GENOA_OC_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(GENOA_OC_REFERENCE_VALUES_PATH),
        }
    }

    /// Loads a current attestation example for Oak Restricted Kernel.
    pub fn load_rk() -> AttestationData {
        AttestationData {
            valid_not_before: Instant::from(utc_datetime!(2025-06-17 06:05:52.482000)),
            valid_not_after: Instant::from(utc_datetime!(2025-09-15 06:05:52.151000)),
            evidence: load_evidence(RK_EVIDENCE_PATH),
            endorsements: load_endorsements(RK_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(RK_REFERENCE_VALUES_PATH),
        }
    }

    /// Loads a current attestation example for CB.
    pub fn load_cb() -> AttestationData {
        AttestationData {
            // Not clear what the correct validity dates are (at least not obvious
            // from the text form). Probably irrelevant.
            valid_not_before: Instant::from(utc_datetime!(2025-01-01 00:00:00.000000)),
            valid_not_after: Instant::from(utc_datetime!(2025-12-31 00:00:00.000000)),
            evidence: load_evidence(CB_EVIDENCE_PATH),
            endorsements: load_endorsements(CB_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(CB_REFERENCE_VALUES_PATH),
        }
    }

    pub fn make_valid_time(&self) -> Instant {
        self.valid_not_before + (self.valid_not_after - self.valid_not_before) / 2
    }
}

fn load_evidence(path: &str) -> Evidence {
    let serialized = fs::read(data_path(path)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

fn load_endorsements(path: &str) -> Endorsements {
    let serialized = fs::read(data_path(path)).expect("could not read endorsements");
    Endorsements::decode(serialized.as_slice()).expect("could not decode endorsements")
}

fn load_reference_values(path: &str) -> ReferenceValues {
    let serialized = fs::read(data_path(path)).expect("could not read reference values");
    ReferenceValues::decode(serialized.as_slice()).expect("could not decode reference values")
}
