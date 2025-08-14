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
use oak_proto_rust::oak::{
    attestation::v1::{
        AmdSevReferenceValues, AmdSevSnpEndorsement, EventAttestationResults,
        RootLayerReferenceValues,
    },
    Variant,
};
use oak_sev_snp_attestation_report::AttestationReport;
use oak_time::Instant;
use x509_cert::{der::Decode, Certificate};

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

    // TODO: b/398859203 - Remove this function once old reference values have been
    // updated.
    pub fn from_root_layer_reference_values(
        root_layer: &RootLayerReferenceValues,
    ) -> anyhow::Result<Self> {
        let platform_reference_values = root_layer
            .amd_sev
            .as_ref()
            .context("AMD SEV-SNP attestation report wasn't provided")?;
        Ok(Self::new(platform_reference_values))
    }
}

impl Policy<AttestationReport> for AmdSevSnpPolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &AttestationReport,
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let endorsement: AmdSevSnpEndorsement =
            endorsement.try_into().map_err(anyhow::Error::msg)?;
        let vcek_cert = Certificate::from_der(&endorsement.tee_certificate)
            .map_err(|err| anyhow::anyhow!("couldn't parse VCEK certificate: {:?}", err))?;

        // Ensure the Attestation report is properly signed by the platform and the
        // corresponding certificate is signed by AMD.
        verify_amd_sev_snp_attestation_report_validity(verification_time, evidence, &vcek_cert)
            .context("couldn't verify AMD SEV-SNP attestation validity")?;

        // Verify attestation report values.
        let report = convert_amd_sev_snp_attestation_report(evidence)?;
        let expected_values = get_amd_sev_snp_expected_values(&self.reference_values)
            .context("couldn't extract AMD SEV-SNP expected values from the endorsement")?;
        verify_amd_sev_attestation_report_values(&report, &expected_values)
            .context("couldn't verify attestation report fields")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use oak_proto_rust::oak::attestation::v1::endorsements;
    use test_util::{extract_attestation_report, get_oc_reference_values, AttestationData};

    use super::*;

    #[test]
    fn verify_oc_succeeds() {
        let d = AttestationData::load_milan_oc_release();
        let attestation_report = extract_attestation_report(&d.evidence).unwrap();
        let endorsement = AmdSevSnpEndorsement {
            tee_certificate: match d.endorsements.r#type.as_ref() {
                Some(endorsements::Type::OakContainers(e)) => {
                    e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
                }
                _ => panic!("bad endorsement type"),
            },
        };
        let ref_values = get_oc_reference_values(&d.reference_values);
        let platform_ref_values = ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
        let policy = AmdSevSnpPolicy::new(platform_ref_values);

        let result = policy.verify(d.make_valid_time(), attestation_report, &endorsement.into());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }
}
