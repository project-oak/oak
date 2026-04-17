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

use anyhow::Context;
use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence, ReferenceValues, endorsements};
use oak_time::{Instant, make_instant};
use prost::Message;

use crate::factory::{create_oc_reference_values, create_rk_reference_values};

const CB_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/cb_evidence.binarypb";
const CB_ENDORSEMENTS_PATH: &str = "oak_attestation_verification/testdata/cb_endorsements.binarypb";
const CB_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/cb_reference_values.binarypb";

// AMD Milan attestation with Oak Containers, release mode.
const MILAN_OC_RELEASE_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/milan_oc_release_evidence.binarypb";
const MILAN_OC_RELEASE_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/milan_oc_release_endorsements.binarypb";

// AMD Milan attestation with Oak Containers, staging mode.
const MILAN_OC_STAGING_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/milan_oc_staging_evidence.binarypb";
const MILAN_OC_STAGING_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/milan_oc_staging_endorsements.binarypb";
const MILAN_OC_STAGING_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/milan_oc_staging_reference_values.binarypb";

// AMD Milan attestation with Restricted Kernel, release mode.
const MILAN_RK_RELEASE_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/milan_rk_release_evidence.binarypb";
const MILAN_RK_RELEASE_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/milan_rk_release_endorsements.binarypb";

// AMD Milan attestation with Restricted Kernel, staging mode.
const MILAN_RK_STAGING_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/milan_rk_staging_evidence.binarypb";
const MILAN_RK_STAGING_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/milan_rk_staging_endorsements.binarypb";
const MILAN_RK_STAGING_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/milan_rk_staging_reference_values.binarypb";

// AMD Genoa attestation with Oak Containers, with legacy endorsements.
const GENOA_OC_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_evidence.binarypb";
const GENOA_OC_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_endorsements.binarypb";
const GENOA_OC_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_reference_values.binarypb";

// AMD Turin attestation with Oak Containers.
const TURIN_OC_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/turin_oc_evidence.binarypb";
const TURIN_OC_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/turin_oc_endorsements.binarypb";
const TURIN_OC_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/turin_oc_reference_values.binarypb";

// Fake evidence observed when running e.g. on desktops.
const FAKE_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/fake_evidence.binarypb";
const FAKE_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/fake_endorsements.binarypb";
const FAKE_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/fake_reference_values.binarypb";

// Intel TDX attestation with Oak Containers.
const TDX_OC_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/tdx_oc_evidence.binarypb";
const TDX_OC_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/tdx_oc_endorsements.binarypb";
const TDX_OC_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/tdx_oc_reference_values.binarypb";

pub struct AttestationData {
    pub valid_not_before: Instant,
    pub valid_not_after: Instant,
    pub evidence: Evidence,
    pub endorsements: Endorsements,
    pub reference_values: ReferenceValues,
}

impl AttestationData {
    // Loads an attestation example involving an AMD Milan CPU running Oak
    // Containers in release mode.
    pub fn load_milan_oc_release() -> AttestationData {
        AttestationData {
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(MILAN_OC_RELEASE_EVIDENCE_PATH),
            endorsements: load_endorsements(MILAN_OC_RELEASE_ENDORSEMENTS_PATH),
            reference_values: create_oc_reference_values(),
        }
    }

    // Loads an attestation example involving an AMD Milan CPU running Oak
    // Containers in staging mode.
    pub fn load_milan_oc_staging() -> AttestationData {
        AttestationData {
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(MILAN_OC_STAGING_EVIDENCE_PATH),
            endorsements: load_endorsements(MILAN_OC_STAGING_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(MILAN_OC_STAGING_REFERENCE_VALUES_PATH),
        }
    }

    // Loads an attestation example involving an AMD Milan CPU running
    // Restricted Kernel in release mode.
    pub fn load_milan_rk_release() -> AttestationData {
        AttestationData {
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(MILAN_RK_RELEASE_EVIDENCE_PATH),
            endorsements: load_endorsements(MILAN_RK_RELEASE_ENDORSEMENTS_PATH),
            reference_values: create_rk_reference_values(),
        }
    }

    // Loads an attestation example involving an AMD Milan CPU running
    // Restricted Kernel in staging mode.
    pub fn load_milan_rk_staging() -> AttestationData {
        AttestationData {
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(MILAN_RK_STAGING_EVIDENCE_PATH),
            endorsements: load_endorsements(MILAN_RK_STAGING_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(MILAN_RK_STAGING_REFERENCE_VALUES_PATH),
        }
    }

    // Loads an attestation example involving an AMD Genoa CPU running Oak
    // Containers.
    pub fn load_genoa_oc() -> AttestationData {
        AttestationData {
            // Validity is used to check VCEK certificate.
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(GENOA_OC_EVIDENCE_PATH),
            endorsements: load_endorsements(GENOA_OC_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(GENOA_OC_REFERENCE_VALUES_PATH),
        }
    }

    // Loads an attestation example involving an AMD Turin CPU running Oak
    // Containers.
    pub fn load_turin_oc() -> AttestationData {
        AttestationData {
            // Validity is used to check VCEK certificate.
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(TURIN_OC_EVIDENCE_PATH),
            endorsements: load_endorsements(TURIN_OC_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(TURIN_OC_REFERENCE_VALUES_PATH),
        }
    }

    /// Loads an attestation example for CB.
    pub fn load_cb() -> AttestationData {
        AttestationData {
            // Validity is used to check VCEK certificate.
            valid_not_before: make_instant!("2025-07-29T00:00:00.000000Z"),
            valid_not_after: make_instant!("2025-10-27T00:00:00.000000Z"),
            evidence: load_evidence(CB_EVIDENCE_PATH),
            endorsements: load_endorsements(CB_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(CB_REFERENCE_VALUES_PATH),
        }
    }

    // Loads an attestation example observed on "insecure" hardware.
    pub fn load_fake() -> AttestationData {
        AttestationData {
            // Validity period is inferred from endorsements.
            valid_not_before: make_instant!("2025-08-03T02:23:14.000000Z"),
            valid_not_after: make_instant!("2025-11-01T02:23:13.000000Z"),
            evidence: load_evidence(FAKE_EVIDENCE_PATH),
            endorsements: load_endorsements(FAKE_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(FAKE_REFERENCE_VALUES_PATH),
        }
    }

    // Loads an attestation example involving Oak Containers on Intel TDX.
    pub fn load_tdx_oc() -> AttestationData {
        AttestationData {
            // Validity is used to check VCEK certificate.
            valid_not_before: make_instant!("2025-08-03T02:23:14.000000Z"),
            valid_not_after: make_instant!("2025-11-01T02:23:13.000000Z"),
            evidence: load_evidence(TDX_OC_EVIDENCE_PATH),
            endorsements: load_endorsements(TDX_OC_ENDORSEMENTS_PATH),
            reference_values: load_reference_values(TDX_OC_REFERENCE_VALUES_PATH),
        }
    }

    pub fn make_valid_time(&self) -> Instant {
        self.valid_not_before + (self.valid_not_after - self.valid_not_before) / 2
    }

    pub fn make_valid_millis(&self) -> i64 {
        self.make_valid_time().into_unix_millis()
    }

    pub fn get_tee_certificate(&self) -> anyhow::Result<Vec<u8>> {
        let tee_certificate: &[u8] = match self.endorsements.r#type.as_ref() {
            Some(endorsements::Type::OakRestrictedKernel(endorsements)) => endorsements
                .root_layer
                .as_ref()
                .context("no root layer endorsements")?
                .tee_certificate
                .as_ref(),
            Some(endorsements::Type::OakContainers(endorsements)) => endorsements
                .root_layer
                .as_ref()
                .context("no root layer endorsements")?
                .tee_certificate
                .as_ref(),
            Some(endorsements::Type::Cb(endorsements)) => endorsements
                .root_layer
                .as_ref()
                .context("no root layer endorsements")?
                .tee_certificate
                .as_ref(),
            None => anyhow::bail!("empty endorsements"),
        };

        Ok(tee_certificate.to_vec())
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
