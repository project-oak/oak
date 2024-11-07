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

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::attestation::v1::{
    AmdSevReferenceValues, AmdSevSnpEndorsement, EventAttestationResults,
};
use oak_sev_snp_attestation_report::AttestationReport;

use crate::{
    expect::get_amd_sev_snp_expected_values,
    platform::{
        convert_amd_sev_snp_attestation_report, verify_amd_sev_attestation_report_values,
        verify_amd_sev_snp_attestation_report_validity,
    },
};

pub struct AmdSevSnpPolicy {
    reference_values: AmdSevReferenceValues,
}

impl AmdSevSnpPolicy {
    pub fn new(reference_values: &AmdSevReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<AttestationReport, AmdSevSnpEndorsement> for AmdSevSnpPolicy {
    fn verify(
        &self,
        attestation_report: &AttestationReport,
        platform_endorsement: &AmdSevSnpEndorsement,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        // Ensure the Attestation report is properly signed by the platform and the
        // corresponding certificate is signed by AMD.
        verify_amd_sev_snp_attestation_report_validity(
            attestation_report,
            &platform_endorsement.tee_certificate,
            milliseconds_since_epoch,
        )
        .context("couldn't verify AMD SEV-SNP attestation validity")?;

        // Verify attestation report values.
        let extracted_attestation_report =
            convert_amd_sev_snp_attestation_report(attestation_report)?;
        let expected_values = get_amd_sev_snp_expected_values(&self.reference_values)
            .context("couldn't extract AMD SEV-SNP expected values from the endorsement")?;
        verify_amd_sev_attestation_report_values(&extracted_attestation_report, &expected_values)
            .context("couldn't verify attestation report fields")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults {})
    }
}
