//
// Copyright 2026 The Project Oak Authors
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
    RawDigest, Variant,
    attestation::v1::{
        CbLayer1TransparentEndorsement, CbLayer1TransparentEvent,
        CbLayer1TransparentReferenceValues, CbLayer2TransparentEndorsement,
        CbLayer2TransparentEvent, CbLayer2TransparentReferenceValues, EventAttestationResults,
        KernelEndorsement, KernelLayerReferenceValues, MpmAttachment,
        Stage0TransparentMeasurements,
    },
};
use oak_time::Instant;
use prost::Message;

use crate::{
    compare::{
        compare_kernel_layer_measurement_digests, compare_measurement_digest, compare_text_value,
    },
    expect::{
        acquire_expected_digests, acquire_kernel_event_expected_values, acquire_mpm_expected_values,
    },
    extract::stage0_transparent_measurements_to_kernel_layer_data,
    util::decode_event_proto,
};

/// Event policy for transparent stage 0.
///
/// Decodes [`Stage0TransparentMeasurements`] from the evidence, converts to
/// [`KernelLayerData`], and compares against the kernel layer expected values
/// derived from the reference values and endorsements.
pub struct TransparentStage0Policy {
    reference_values: KernelLayerReferenceValues,
}

impl TransparentStage0Policy {
    pub fn new(reference_values: &KernelLayerReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for TransparentStage0Policy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = stage0_transparent_measurements_to_kernel_layer_data(decode_event_proto::<
            Stage0TransparentMeasurements,
        >(
            "type.googleapis.com/oak.attestation.v1.Stage0TransparentMeasurements",
            evidence,
        )?);
        let endorsement: Option<KernelEndorsement> =
            endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_kernel_event_expected_values(
            verification_time.into_unix_millis(),
            endorsement.as_ref(),
            &self.reference_values,
        )
        .context("acquiring kernel event expected values")?;

        compare_kernel_layer_measurement_digests(&event, &expected_values)
            .context("comparing kernel event digests")?;

        Ok(EventAttestationResults { ..Default::default() })
    }
}

/// Event policy for transparent layer 1.
///
/// Decodes [`CbLayer1TransparentEvent`] from the evidence and compares the
/// `runtime_agent_binary`, `userspace`, and `runtime_agent` measurements
/// against the reference values and endorsements.
pub struct TransparentLayer1Policy {
    reference_values: CbLayer1TransparentReferenceValues,
}

impl TransparentLayer1Policy {
    pub fn new(reference_values: &CbLayer1TransparentReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for TransparentLayer1Policy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<CbLayer1TransparentEvent>(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            evidence,
        )?;
        let endorsement: Option<CbLayer1TransparentEndorsement> =
            endorsement.try_into().map_err(anyhow::Error::msg)?;

        // Verify runtime agent binary measurement
        let runtime_agent_binary_ref_value = self
            .reference_values
            .runtime_agent_binary
            .as_ref()
            .context("no runtime agent binary reference value")?;
        let runtime_agent_binary_measurement = RawDigest {
            sha2_256: event.runtime_agent_binary_measurement.clone(),
            ..Default::default()
        };
        let expected = acquire_expected_digests(
            verification_time.into_unix_millis(),
            endorsement.as_ref().and_then(|e| e.runtime_agent_binary.as_ref()),
            runtime_agent_binary_ref_value,
        )
        .context("acquiring runtime agent binary expected values")?;
        compare_measurement_digest(&runtime_agent_binary_measurement, &expected)
            .context("comparing runtime agent binary measurement")?;

        // Verify userspace measurement
        let userspace_ref_value =
            self.reference_values.userspace.as_ref().context("no userspace reference value")?;
        let userspace_measurement =
            RawDigest { sha2_256: event.userspace_measurement.clone(), ..Default::default() };
        let expected = acquire_expected_digests(
            verification_time.into_unix_millis(),
            endorsement.as_ref().and_then(|e| e.userspace.as_ref()),
            userspace_ref_value,
        )
        .context("acquiring userspace expected values")?;
        compare_measurement_digest(&userspace_measurement, &expected)
            .context("comparing userspace measurement")?;

        Ok(EventAttestationResults { ..Default::default() })
    }
}

/// Event policy for transparent layer 2.
///
/// Decodes [`CbLayer2TransparentEvent`] from the evidence, and verifies that
/// each package's serialized [`MpmAttachment`] digest matches a corresponding
/// entry in the `binary_mpms` reference values and endorsements. If
/// `binary_mpms` is not specified, the policy falls back to the deprecated
/// singular `binary_mpm` field in both the reference values and endorsements;
/// `binary_mpms` takes precedence when present.
///
/// NOTE: The ordering of the `binary_mpms` must match the ordering of the
/// packages in the [`CbLayer2TransparentEvent`].
pub struct TransparentLayer2Policy {
    reference_values: CbLayer2TransparentReferenceValues,
}

impl TransparentLayer2Policy {
    pub fn new(reference_values: &CbLayer2TransparentReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for TransparentLayer2Policy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<CbLayer2TransparentEvent>(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            evidence,
        )?;
        let endorsement: Option<CbLayer2TransparentEndorsement> =
            endorsement.try_into().map_err(anyhow::Error::msg)?;

        anyhow::ensure!(!event.packages.is_empty(), "no packages in layer 2 event");

        let endorsement = endorsement.unwrap_or_default();

        // If binary_mpms is not specified in the reference values, fall back to the
        // singular binary_mpm field in both the reference values and the endorsement.
        #[allow(deprecated)]
        let (ref_values, binary_mpms) = if self.reference_values.binary_mpms.is_empty() {
            let ref_values = self
                .reference_values
                .binary_mpm
                .as_ref()
                .map(|rv| alloc::vec![rv.clone()])
                .unwrap_or_default();
            let binary_mpms = endorsement.binary_mpm.map(|e| alloc::vec![e]).unwrap_or_default();
            (ref_values, binary_mpms)
        } else {
            (self.reference_values.binary_mpms.clone(), endorsement.binary_mpms)
        };

        anyhow::ensure!(
            binary_mpms.len() == event.packages.len(),
            "number of endorsements ({}) does not match number of packages ({})",
            binary_mpms.len(),
            event.packages.len()
        );

        for (i, package) in event.packages.iter().enumerate() {
            // The ordering of the endorsements must match the order of the packages in the
            // attestation evidence.
            let matching_endorsement = &binary_mpms[i];

            if let Some(ref e) = matching_endorsement.endorsement {
                let mpm_attachment = MpmAttachment::decode(e.subject.as_slice())
                    .context("couldn't parse signed endorsement subject as an MpmAttachment")?;
                anyhow::ensure!(
                    mpm_attachment.package_version == package.mpm_version_id,
                    "Endorsement at index {} (version {}) does not match measurement {}",
                    i,
                    mpm_attachment.package_version,
                    package.mpm_version_id
                );
            }

            // Iterate over reference values to validate the evidence.
            let mut verified = false;
            for ref_val in &ref_values {
                if let Ok(expected) = acquire_mpm_expected_values(
                    verification_time.into_unix_millis(),
                    Some(matching_endorsement),
                    ref_val,
                ) && compare_text_value(&package.mpm_version_id, &expected).is_ok()
                {
                    verified = true;
                    break;
                }
            }
            anyhow::ensure!(verified, "package {} could not be verified", package.mpm_version_id);
        }

        // Attestation results are left empty.
        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use oak_digest::{Sha256, raw_to_hex_digest};
    use oak_proto_rust::oak::attestation::v1::{Event, MpmAttachment, MpmPackage};
    use oak_time::make_instant;
    use prost::Message;
    use prost_types::Any;
    use verify_endorsement::MPM_CLAIM_TYPE;

    use super::*;
    use crate::test_util;

    const TEST_TIME: Instant = Instant::from_unix_millis(1_000_000);

    /// Helper to encode a proto as a serialized [`Event`], the format expected
    /// by [`decode_event_proto`].
    fn encode_event_proto<M: Message>(type_url: &str, msg: &M) -> Vec<u8> {
        let event = Event {
            tag: String::new(),
            event: Some(Any { type_url: type_url.to_string(), value: msg.encode_to_vec() }),
        };
        event.encode_to_vec()
    }

    #[test]
    fn transparent_stage0_verify_skip_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            BinaryReferenceValue, KernelBinaryReferenceValue, SkipVerification, TextReferenceValue,
            binary_reference_value::Type as BrvType,
            kernel_binary_reference_value::Type as KbrvType, text_reference_value::Type as TrvType,
        };

        let skip_brv = BinaryReferenceValue { r#type: Some(BrvType::Skip(SkipVerification {})) };
        let skip_kbrv =
            KernelBinaryReferenceValue { r#type: Some(KbrvType::Skip(SkipVerification {})) };
        let skip_trv = TextReferenceValue { r#type: Some(TrvType::Skip(SkipVerification {})) };

        let measurements = Stage0TransparentMeasurements {
            setup_data_digest: vec![0u8; 32],
            kernel_measurement: vec![0u8; 32],
            ram_disk_digest: vec![0u8; 32],
            memory_map_digest: vec![0u8; 32],
            acpi_digest: vec![0u8; 32],
            kernel_cmdline_digest: vec![0u8; 32],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.Stage0TransparentMeasurements",
            &measurements,
        );
        let reference_values = KernelLayerReferenceValues {
            kernel: Some(skip_kbrv),
            kernel_cmd_line_text: Some(skip_trv),
            init_ram_fs: Some(skip_brv.clone()),
            memory_map: Some(skip_brv.clone()),
            acpi: Some(skip_brv),
        };
        let policy = TransparentStage0Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, &evidence, &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn transparent_layer1_verify_skip_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            BinaryReferenceValue, SkipVerification, binary_reference_value::Type as BrvType,
        };

        let skip_ref = BinaryReferenceValue { r#type: Some(BrvType::Skip(SkipVerification {})) };
        let event = CbLayer1TransparentEvent {
            runtime_agent_binary_measurement: vec![0u8; 32],
            userspace_measurement: vec![0u8; 32],
            ..Default::default()
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            &event,
        );
        let reference_values = CbLayer1TransparentReferenceValues {
            runtime_agent_binary: Some(skip_ref.clone()),
            userspace: Some(skip_ref),
            ..Default::default()
        };
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, &evidence, &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_verify_multiple_packages_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, SkipVerification, mpm_reference_value::Type as MrvType,
        };

        let skip_ref = MpmReferenceValue { r#type: Some(MrvType::Skip(SkipVerification {})) };
        let event = CbLayer2TransparentEvent {
            packages: vec![
                MpmPackage { mpm_version_id: "other/2.0".into() },
                MpmPackage { mpm_version_id: "test/1.0".into() },
            ],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let (signing_key, _) = test_util::new_random_signing_keypair();

        use oak_proto_rust::oak::attestation::v1::MpmAttachment;
        use prost::Message;
        use verify_endorsement::MPM_CLAIM_TYPE;

        let mpm_attachment_1 =
            MpmAttachment { package_name: "other".into(), package_version: "other/2.0".into() };
        let end1 = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment_1.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );
        let mpm_attachment_2 =
            MpmAttachment { package_name: "test".into(), package_version: "test/1.0".into() };
        let end2 = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment_2.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );
        let layer2_end =
            CbLayer2TransparentEndorsement { binary_mpm: None, binary_mpms: vec![end1, end2] };
        let endorsement_variant: Variant = layer2_end.into();

        let reference_values = CbLayer2TransparentReferenceValues {
            binary_mpm: None,
            binary_mpms: vec![skip_ref.clone(), skip_ref],
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_verify_no_packages_fails() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, SkipVerification, mpm_reference_value::Type as MrvType,
        };

        let skip_ref = MpmReferenceValue { r#type: Some(MrvType::Skip(SkipVerification {})) };
        let event = CbLayer2TransparentEvent { packages: vec![] };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );
        let reference_values =
            CbLayer2TransparentReferenceValues { binary_mpm: Some(skip_ref), binary_mpms: vec![] };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, &evidence, &Variant::default());

        assert!(result.is_err());
    }

    #[test]
    fn transparent_stage0_verify_with_signed_endorsement_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            KernelAttachment, SkipVerification, TextReferenceValue,
            text_reference_value::Type as TrvType,
        };
        use verify_endorsement::KERNEL_CLAIM_TYPE;

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, public_key) = test_util::new_random_signing_keypair();

        let kernel_measurement = Sha256::from([1u8; 32]);
        let setup_data_digest = Sha256::from([2u8; 32]);
        let ram_disk_digest = Sha256::from([3u8; 32]);
        let memory_map_digest = Sha256::from([4u8; 32]);
        let acpi_digest = Sha256::from([5u8; 32]);

        let measurements = Stage0TransparentMeasurements {
            kernel_measurement: Vec::from(kernel_measurement),
            setup_data_digest: Vec::from(setup_data_digest),
            ram_disk_digest: Vec::from(ram_disk_digest),
            memory_map_digest: Vec::from(memory_map_digest),
            acpi_digest: Vec::from(acpi_digest),
            kernel_cmdline_digest: vec![0u8; 32],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.Stage0TransparentMeasurements",
            &measurements,
        );

        let kernel_attachment = KernelAttachment {
            image: Some(raw_to_hex_digest(&RawDigest {
                sha2_256: Vec::from(kernel_measurement),
                ..Default::default()
            })),
            setup_data: Some(raw_to_hex_digest(&RawDigest {
                sha2_256: Vec::from(setup_data_digest),
                ..Default::default()
            })),
            ..Default::default()
        };
        let kernel_signed = test_util::make_signed_endorsement_for_contents(
            &kernel_attachment.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![KERNEL_CLAIM_TYPE],
        );

        let init_ram_fs_signed = test_util::make_signed_endorsement_for_digest(
            &RawDigest { sha2_256: Vec::from(ram_disk_digest), ..Default::default() },
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let memory_map_signed = test_util::make_signed_endorsement_for_digest(
            &RawDigest { sha2_256: Vec::from(memory_map_digest), ..Default::default() },
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let acpi_signed = test_util::make_signed_endorsement_for_digest(
            &RawDigest { sha2_256: Vec::from(acpi_digest), ..Default::default() },
            not_before,
            not_after,
            &signing_key,
            vec![],
        );

        let kernel_endorsement = KernelEndorsement {
            kernel: Some(kernel_signed),
            init_ram_fs: Some(init_ram_fs_signed),
            memory_map: Some(memory_map_signed),
            acpi: Some(acpi_signed),
            ..Default::default()
        };
        let endorsement_variant: Variant = kernel_endorsement.into();

        // kernel_cmd_line_text is Skip because transparent measurements provide a
        // digest, not the raw command line.
        let skip_trv = TextReferenceValue { r#type: Some(TrvType::Skip(SkipVerification {})) };
        let reference_values = KernelLayerReferenceValues {
            kernel: Some(test_util::kernel_binary_reference_value_for_endorser_pk(public_key)),
            kernel_cmd_line_text: Some(skip_trv),
            init_ram_fs: Some(test_util::binary_reference_value_for_endorser_pk(public_key)),
            memory_map: Some(test_util::binary_reference_value_for_endorser_pk(public_key)),
            acpi: Some(test_util::binary_reference_value_for_endorser_pk(public_key)),
        };
        let policy = TransparentStage0Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn transparent_layer1_verify_with_signed_endorsement_succeeds() {
        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, public_key) = test_util::new_random_signing_keypair();

        let runtime_agent_binary_measurement = Sha256::from([11u8; 32]);
        let userspace_measurement = Sha256::from([12u8; 32]);

        let event = CbLayer1TransparentEvent {
            runtime_agent_binary_measurement: Vec::from(runtime_agent_binary_measurement),
            userspace_measurement: Vec::from(userspace_measurement),
            ..Default::default()
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            &event,
        );

        let runtime_agent_binary_signed = test_util::make_signed_endorsement_for_digest(
            &RawDigest {
                sha2_256: Vec::from(runtime_agent_binary_measurement),
                ..Default::default()
            },
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let userspace_signed = test_util::make_signed_endorsement_for_digest(
            &RawDigest { sha2_256: Vec::from(userspace_measurement), ..Default::default() },
            not_before,
            not_after,
            &signing_key,
            vec![],
        );

        let layer1_endorsement = CbLayer1TransparentEndorsement {
            runtime_agent_binary: Some(runtime_agent_binary_signed),
            userspace: Some(userspace_signed),
            ..Default::default()
        };
        let endorsement_variant: Variant = layer1_endorsement.into();

        let ref_value = test_util::binary_reference_value_for_endorser_pk(public_key);
        let reference_values = CbLayer1TransparentReferenceValues {
            runtime_agent_binary: Some(ref_value.clone()),
            userspace: Some(ref_value),
            ..Default::default()
        };
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn transparent_layer1_verify_with_empty_endorsement_fails() {
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (_signing_key, public_key) = test_util::new_random_signing_keypair();

        let event = CbLayer1TransparentEvent {
            runtime_agent_binary_measurement: vec![11u8; 32],
            userspace_measurement: vec![12u8; 32],
            ..Default::default()
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            &event,
        );

        let ref_value = test_util::binary_reference_value_for_endorser_pk(public_key);
        let reference_values = CbLayer1TransparentReferenceValues {
            runtime_agent_binary: Some(ref_value.clone()),
            userspace: Some(ref_value),
            ..Default::default()
        };
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &Variant::default());

        assert!(result.is_err());
    }

    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_verify_with_signed_endorsement_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, mpm_reference_value::Type as MrvType,
        };

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, public_key) = test_util::new_random_signing_keypair();

        let mpm_attachment =
            MpmAttachment { package_name: "test_pkg".into(), package_version: "test/1.0".into() };
        let binary_mpm_signed = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );

        let event = CbLayer2TransparentEvent {
            packages: vec![
                MpmPackage { mpm_version_id: "test/1.0".into() },
                MpmPackage { mpm_version_id: "test/1.0".into() },
            ],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );

        let layer2_endorsement = CbLayer2TransparentEndorsement {
            binary_mpm: None,
            binary_mpms: vec![binary_mpm_signed.clone(), binary_mpm_signed],
        };
        let endorsement_variant: Variant = layer2_endorsement.into();

        let endorsement_rv = test_util::endorsement_reference_value(public_key);
        let reference_values = CbLayer2TransparentReferenceValues {
            binary_mpm: None,
            binary_mpms: vec![
                MpmReferenceValue { r#type: Some(MrvType::Endorsement(endorsement_rv.clone())) },
                MpmReferenceValue { r#type: Some(MrvType::Endorsement(endorsement_rv)) },
            ],
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_verify_signed_endorsement_not_present_fails() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, mpm_reference_value::Type as MrvType,
        };

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, public_key) = test_util::new_random_signing_keypair();

        let mpm_attachment = MpmAttachment {
            package_name: "test_pkg".into(),
            package_version: "endorsed/2.0".into(),
        };
        let binary_mpm_signed = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );

        let layer2_endorsement = CbLayer2TransparentEndorsement {
            binary_mpm: Some(binary_mpm_signed),
            binary_mpms: vec![],
        };
        let endorsement_variant: Variant = layer2_endorsement.into();

        let event = CbLayer2TransparentEvent {
            packages: vec![MpmPackage { mpm_version_id: "not_endorsed/1.0".into() }],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );

        let endorsement_rv = test_util::endorsement_reference_value(public_key);
        let reference_values = CbLayer2TransparentReferenceValues {
            binary_mpm: Some(MpmReferenceValue {
                r#type: Some(MrvType::Endorsement(endorsement_rv)),
            }),
            binary_mpms: vec![],
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_err());
    }

    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_verify_partial_match_fails() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, mpm_reference_value::Type as MrvType,
        };

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, public_key) = test_util::new_random_signing_keypair();

        let mpm_attachment =
            MpmAttachment { package_name: "test_pkg".into(), package_version: "test/1.0".into() };
        let binary_mpm_signed = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );

        // One package matches the endorsement, but the other does not.
        let event = CbLayer2TransparentEvent {
            packages: vec![
                MpmPackage { mpm_version_id: "test/1.0".into() },
                MpmPackage { mpm_version_id: "unendorsed/2.0".into() },
            ],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );

        let layer2_endorsement = CbLayer2TransparentEndorsement {
            binary_mpm: None,
            // The second endorsement is duplicate, so it won't match "unendorsed/2.0"
            binary_mpms: vec![binary_mpm_signed.clone(), binary_mpm_signed],
        };
        let endorsement_variant: Variant = layer2_endorsement.into();

        let endorsement_rv = test_util::endorsement_reference_value(public_key);
        let reference_values = CbLayer2TransparentReferenceValues {
            binary_mpm: None,
            binary_mpms: vec![
                MpmReferenceValue { r#type: Some(MrvType::Endorsement(endorsement_rv.clone())) },
                MpmReferenceValue { r#type: Some(MrvType::Endorsement(endorsement_rv)) },
            ],
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_err());
    }

    /// When `binary_mpms` is set in the reference values, it takes precedence
    /// over `binary_mpm` for both the reference values and the endorsement.
    /// Here the `binary_mpm` ref value requires an endorsement from a key that
    /// is not provided, so it would fail on its own; the `binary_mpms` skip ref
    /// value succeeds.
    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_binary_mpms_takes_precedence_over_binary_mpm_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, SkipVerification, mpm_reference_value::Type as MrvType,
        };

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, _unused_key) = test_util::new_random_signing_keypair();
        let (_other_key, other_public_key) = test_util::new_random_signing_keypair();

        let mpm_attachment =
            MpmAttachment { package_name: "test_pkg".into(), package_version: "test/1.0".into() };
        let binary_mpm_signed = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );

        let event = CbLayer2TransparentEvent {
            packages: vec![MpmPackage { mpm_version_id: "test/1.0".into() }],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );

        // binary_mpms is set in the endorsement; binary_mpm is also set but will
        // be ignored because binary_mpms takes precedence.
        let layer2_endorsement = CbLayer2TransparentEndorsement {
            binary_mpm: Some(binary_mpm_signed.clone()),
            binary_mpms: vec![binary_mpm_signed],
        };
        let endorsement_variant: Variant = layer2_endorsement.into();

        // binary_mpms ref value uses Skip (always passes); binary_mpm ref value
        // requires endorsement from other_public_key which is not provided—it
        // would fail if it were consulted.
        let reference_values = CbLayer2TransparentReferenceValues {
            binary_mpm: Some(MpmReferenceValue {
                r#type: Some(MrvType::Endorsement(test_util::endorsement_reference_value(
                    other_public_key,
                ))),
            }),
            binary_mpms: vec![MpmReferenceValue {
                r#type: Some(MrvType::Skip(SkipVerification {})),
            }],
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    /// When `binary_mpms` is set in the reference values, the endorsement's
    /// `binary_mpm` field is ignored—only `binary_mpms` in the endorsement is
    /// consulted. Here `endorsement.binary_mpms` is empty while
    /// `endorsement.binary_mpm` is populated, causing a count mismatch.
    #[test]
    #[allow(deprecated)]
    fn transparent_layer2_binary_mpms_in_ref_ignores_endorsement_binary_mpm_fails() {
        use oak_proto_rust::oak::attestation::v1::{
            MpmReferenceValue, SkipVerification, mpm_reference_value::Type as MrvType,
        };

        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, _) = test_util::new_random_signing_keypair();

        let mpm_attachment =
            MpmAttachment { package_name: "test_pkg".into(), package_version: "test/1.0".into() };
        let binary_mpm_signed = test_util::make_signed_endorsement_for_contents(
            &mpm_attachment.encode_to_vec(),
            not_before,
            not_after,
            &signing_key,
            vec![MPM_CLAIM_TYPE],
        );

        let event = CbLayer2TransparentEvent {
            packages: vec![MpmPackage { mpm_version_id: "test/1.0".into() }],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            &event,
        );

        // binary_mpm is populated but binary_mpms is empty—the policy must not
        // fall back to binary_mpm because ref_values.binary_mpms is set.
        let layer2_endorsement = CbLayer2TransparentEndorsement {
            binary_mpm: Some(binary_mpm_signed),
            binary_mpms: vec![],
        };
        let endorsement_variant: Variant = layer2_endorsement.into();

        // ref_values.binary_mpms has one entry, so the binary_mpms path is taken.
        // The endorsement's binary_mpms is empty → count mismatch → error.
        let reference_values = CbLayer2TransparentReferenceValues {
            binary_mpm: None,
            binary_mpms: vec![MpmReferenceValue {
                r#type: Some(MrvType::Skip(SkipVerification {})),
            }],
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_err());
    }
}
