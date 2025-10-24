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

use alloc::vec;

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_dice::evidence::TeePlatform;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, tcb_version_reference_value, tdx_tcb_svn_reference_value,
        AmdSevReferenceValues, AmdSevSnpEndorsement, BinaryReferenceValue, Digests,
        EventAttestationResults, IntelTdxReferenceValues, RootLayerEvidence, TcbVersion,
        TcbVersionReferenceValue, TdxTcbSvnReferenceValue,
    },
    RawDigest, Variant,
};
use oak_sev_snp_attestation_report::{AmdProduct, AttestationReport};
use oak_tdx_quote::{TdAttributes, TdxQuoteWrapper};
use oak_time::Instant;
use zerocopy::FromBytes;

use crate::{
    expect::{get_amd_sev_snp_expected_values, get_intel_tdx_expected_values},
    intel,
    platform::{
        convert_amd_sev_snp_attestation_report, convert_intel_tdx_attestation_quote,
        new_tdx_tcb_svn, verify_amd_sev_attestation_report_values,
        verify_intel_tdx_attestation_quote, verify_root_attestation_signature,
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

    /// Returns AmdSevReferenceValues and firmware reference values
    /// (BinaryReferenceValue) that accept only the version in the evidence.
    ///
    /// The evidence should contain the same information that would be passed to
    /// `verify`.
    pub fn evidence_to_reference_values(
        evidence: &RootLayerEvidence,
    ) -> anyhow::Result<(AmdSevReferenceValues, BinaryReferenceValue)> {
        if evidence.platform != TeePlatform::AmdSevSnp as i32 {
            anyhow::bail!("unsupported TEE platform value");
        }
        let report = AttestationReport::ref_from_bytes(&evidence.remote_attestation_report)
            .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))?;

        #[allow(deprecated)]
        let mut rv = AmdSevReferenceValues {
            min_tcb_version: None,
            milan: None,
            genoa: None,
            turin: None,
            allow_debug: report
                .has_debug_flag()
                .map_err(|err| anyhow::anyhow!("failed to get debug flag: {}", err))?,
            check_vcek_cert_expiry: false,
            stage0: None,
        };
        let tcb_version = report.data.get_reported_tcb_version();
        let product = match report.data.get_product() {
            AmdProduct::Milan => &mut rv.milan,
            AmdProduct::Genoa => &mut rv.genoa,
            AmdProduct::Turin => &mut rv.turin,
            _ => anyhow::bail!("unsupported AMD product value"),
        };
        *product = Some(TcbVersionReferenceValue {
            // Note that while we use `Minimum` here, if the reference values are
            // used for mutation attestation of both ends of a connection, >= on
            // both sides is effectively ==.
            r#type: Some(tcb_version_reference_value::Type::Minimum(TcbVersion {
                boot_loader: tcb_version.boot_loader as u32,
                tee: tcb_version.tee as u32,
                snp: tcb_version.snp as u32,
                microcode: tcb_version.microcode as u32,
                fmc: tcb_version.fmc as u32,
            })),
        });

        let firmware_rv = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![RawDigest {
                    sha2_384: report.data.measurement.to_vec(),
                    ..Default::default()
                }],
            })),
        };
        Ok((rv, firmware_rv))
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
            verification_time,
            self.reference_values.check_vcek_cert_expiry,
            evidence,
            &endorsement.tee_certificate,
        )?;

        // Verify attestation report values.
        let report = AttestationReport::ref_from_bytes(&evidence.remote_attestation_report)
            .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))?;
        let amd_report = convert_amd_sev_snp_attestation_report(report)?;
        let expected_values = get_amd_sev_snp_expected_values(&self.reference_values)
            .context("getting AMD SEV-SNP expected values")?;
        verify_amd_sev_attestation_report_values(&amd_report, &expected_values)
            .context("verifying AMD SEV-SNP attestation report values")?;

        let mut results = EventAttestationResults { ..Default::default() };
        set_initial_measurement(&mut results, &report.data.measurement);
        Ok(results)
    }
}

pub struct IntelTdxPolicy {
    reference_values: IntelTdxReferenceValues,
}

impl IntelTdxPolicy {
    pub fn new(reference_values: &IntelTdxReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }

    /// Returns IntelTdxReferenceValues and firmware reference values
    /// (BinaryReferenceValue) that accept only the version in the evidence.
    ///
    /// The evidence should contain the same information that would be passed to
    /// `verify`.
    pub fn evidence_to_reference_values(
        evidence: &RootLayerEvidence,
    ) -> anyhow::Result<(IntelTdxReferenceValues, BinaryReferenceValue)> {
        if evidence.platform != TeePlatform::IntelTdx as i32 {
            anyhow::bail!("unsupported TEE platform value");
        }

        let wrapper = TdxQuoteWrapper::new(evidence.remote_attestation_report.as_slice());

        let quote = wrapper
            .parse_quote()
            .map_err(|err| anyhow::anyhow!("invalid Intel TDX attestation quote: {}", err))?;

        let allow_debug = quote.body.td_attributes.contains(TdAttributes::DEBUG);

        let tee_tcb_svn = Some(TdxTcbSvnReferenceValue {
            r#type: Some(tdx_tcb_svn_reference_value::Type::Minimum(new_tdx_tcb_svn(
                quote.body.tee_tcb_svn,
            ))),
        });

        let rv = IntelTdxReferenceValues { tee_tcb_svn, allow_debug, stage0: None };

        let firmware_rv = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![RawDigest {
                    sha2_384: quote.body.mr_td.to_vec(),
                    ..Default::default()
                }],
            })),
        };
        Ok((rv, firmware_rv))
    }
}

// Policy which verifies the AMD SEV-SNP hardware root.
//
// On success, returns the (unverified) initial measurement which will be
// verified by the firmware policy.
impl Policy<RootLayerEvidence> for IntelTdxPolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &RootLayerEvidence,
        _endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        if evidence.platform != TeePlatform::IntelTdx as i32 {
            anyhow::bail!("unsupported TEE platform value");
        }
        let wrapper = TdxQuoteWrapper::new(evidence.remote_attestation_report.as_slice());

        // Verify validity of the quote.
        intel::verify_intel_tdx_quote_validity(verification_time, &wrapper)
            .context("verifying TDX quote validity")?;

        let quote = wrapper
            .parse_quote()
            .map_err(|err| anyhow::anyhow!("invalid Intel TDX attestation quote: {}", err))?;

        // Verify attestation quote values.
        let quote_values = convert_intel_tdx_attestation_quote(&quote);
        let expected_values = get_intel_tdx_expected_values(&self.reference_values)
            .context("getting Intel TDX expected values")?;
        verify_intel_tdx_attestation_quote(&quote_values, &expected_values)
            .context("verifying Intel TDX attestation quote values")?;

        let mut results = EventAttestationResults { ..Default::default() };
        set_initial_measurement(&mut results, quote.body.mr_td.as_slice());
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
            verification_time,
            false,
            evidence,
            &endorsement.tee_certificate,
        )?;

        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use core::default::Default;

    use oak_attestation_verification_results::get_initial_measurement;
    use oak_proto_rust::oak::attestation::v1::endorsements;
    use test_util::{get_oc_reference_values, AttestationData};

    use super::*;
    use crate::FirmwarePolicy;

    #[test]
    fn verify_milan_oc_succeeds() {
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

    #[test]
    fn milan_oc_evidence_to_reference_values_succeeds() {
        let d = AttestationData::load_milan_oc_release();
        let event = d.evidence.root_layer.as_ref().unwrap();
        let endorsement = AmdSevSnpEndorsement {
            tee_certificate: match d.endorsements.r#type.as_ref() {
                Some(endorsements::Type::OakContainers(e)) => {
                    e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
                }
                _ => panic!("bad endorsement type"),
            },
        };

        let (rv, firmware_rv) = AmdSevSnpPolicy::evidence_to_reference_values(event)
            .expect("evidence_to_reference_values failed");
        #[allow(deprecated)]
        {
            assert!(
                matches!(
                    rv,
                    AmdSevReferenceValues {
                        min_tcb_version: None,
                        milan: Some(TcbVersionReferenceValue {
                            r#type: Some(tcb_version_reference_value::Type::Minimum(..))
                        }),
                        genoa: None,
                        turin: None,
                        allow_debug: false,
                        check_vcek_cert_expiry: false,
                        stage0: None,
                        ..
                    }
                ),
                "reference values missing fields: {:?}",
                rv
            );
        }
        assert!(
            matches!(
                firmware_rv,
                BinaryReferenceValue { r#type: Some(binary_reference_value::Type::Digests(..)) }
            ),
            "firmware reference values missing fields: {:?}",
            firmware_rv
        );

        let result =
            AmdSevSnpPolicy::new(&rv).verify(d.make_valid_time(), event, &endorsement.into());
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());

        let measurement = get_initial_measurement(result.as_ref().unwrap()).unwrap();
        let result = FirmwarePolicy::new(&firmware_rv).verify(
            d.make_valid_time(),
            measurement,
            &Variant::default(),
        );
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn verify_tdx_oc_succeeds() {
        let d = AttestationData::load_tdx_oc();
        let endorsement = Variant::default();
        let ref_values = get_oc_reference_values(&d.reference_values);
        let platform_ref_values =
            ref_values.root_layer.as_ref().unwrap().intel_tdx.as_ref().unwrap();
        let policy = IntelTdxPolicy::new(platform_ref_values);

        let result = policy.verify(
            d.make_valid_time(),
            d.evidence.root_layer.as_ref().unwrap(),
            &endorsement,
        );

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn tdx_oc_evidence_to_reference_values_succeeds() {
        let d = AttestationData::load_tdx_oc();
        let event = d.evidence.root_layer.as_ref().unwrap();
        let endorsement = Variant::default();

        let (rv, firmware_rv) = IntelTdxPolicy::evidence_to_reference_values(event)
            .expect("evidence_to_reference_values failed");
        assert!(
            matches!(
                rv,
                IntelTdxReferenceValues {
                    tee_tcb_svn: Some(TdxTcbSvnReferenceValue {
                        r#type: Some(tdx_tcb_svn_reference_value::Type::Minimum(..))
                    }),
                    allow_debug: false,
                    stage0: None,
                }
            ),
            "reference values missing fields: {:?}",
            rv
        );
        assert!(
            matches!(
                firmware_rv,
                BinaryReferenceValue { r#type: Some(binary_reference_value::Type::Digests(..)) }
            ),
            "firmware reference values missing fields: {:?}",
            firmware_rv
        );

        let result = IntelTdxPolicy::new(&rv).verify(d.make_valid_time(), event, &endorsement);
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());

        let measurement = get_initial_measurement(result.as_ref().unwrap()).unwrap();
        let result = FirmwarePolicy::new(&firmware_rv).verify(
            d.make_valid_time(),
            measurement,
            &Variant::default(),
        );
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }
}
