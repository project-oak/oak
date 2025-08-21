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
use oak_dice::evidence::TeePlatform;
use oak_proto_rust::oak::{
    attestation::v1::{
        AmdSevReferenceValues, AmdSevSnpEndorsement, EventAttestationResults, RootLayerEvidence,
    },
    Variant,
};
use oak_sev_snp_attestation_report::AttestationReport;
use oak_time::Instant;
use zerocopy::FromBytes;

use crate::{
    expect::get_amd_sev_snp_expected_values,
    platform::{
        convert_amd_sev_snp_attestation_report, verify_amd_sev_attestation_report_values,
        verify_root_attestation_signature,
    },
    results::set_initial_measurement,
};

pub struct AmdSevSnpPolicy {
    reference_values: AmdSevReferenceValues,
}

impl AmdSevSnpPolicy {
    pub fn new(reference_values: &AmdSevReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

// Policy which verifies the AMD SEV-SNP hardware root.
//
// On success, returns the (unverified) initial measurement which will be
// verified by the firmware policy.
impl Policy<RootLayerEvidence> for AmdSevSnpPolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &RootLayerEvidence,
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        if evidence.platform != TeePlatform::AmdSevSnp as i32 {
            anyhow::bail!("unsupported TEE platform value");
        }

        let endorsement: AmdSevSnpEndorsement =
            endorsement.try_into().map_err(anyhow::Error::msg)?;
        verify_root_attestation_signature(
            verification_time.into_unix_millis(),
            evidence,
            &endorsement.tee_certificate,
        )?;

        // Verify attestation report values.
        let report = AttestationReport::ref_from_bytes(&evidence.remote_attestation_report)
            .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))?;
        let amd_report = convert_amd_sev_snp_attestation_report(report)?;
        let expected_values = get_amd_sev_snp_expected_values(&self.reference_values)
            .context("couldn't extract AMD SEV-SNP expected values from the endorsement")?;
        verify_amd_sev_attestation_report_values(&amd_report, &expected_values)
            .context("couldn't verify attestation report fields")?;

        let mut results = EventAttestationResults { ..Default::default() };
        set_initial_measurement(&mut results, &report.data.measurement);
        Ok(results)
    }
}

pub struct InsecurePolicy {}

impl InsecurePolicy {
    pub fn new() -> Self {
        Self {}
    }
}

// Policy which verifies an insecure hardware root.
impl Policy<RootLayerEvidence> for InsecurePolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &RootLayerEvidence,
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        // No check for TEE platform value - also secure setups can be
        // verified with the insecure policy.
        let endorsement: AmdSevSnpEndorsement =
            endorsement.try_into().map_err(anyhow::Error::msg)?;
        verify_root_attestation_signature(
            verification_time.into_unix_millis(),
            evidence,
            &endorsement.tee_certificate,
        )?;

        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use oak_proto_rust::oak::attestation::v1::endorsements;
    use test_util::{get_oc_reference_values, AttestationData};

    use super::*;

    #[test]
    fn verify_oc_succeeds() {
        let d = AttestationData::load_milan_oc_release();
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

        let result = policy.verify(
            d.make_valid_time(),
            d.evidence.root_layer.as_ref().unwrap(),
            &endorsement.into(),
        );

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }
}
