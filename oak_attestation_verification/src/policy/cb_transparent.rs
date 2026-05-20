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
        KernelEndorsement, KernelLayerReferenceValues, Stage0TransparentMeasurements,
    },
};
use oak_time::Instant;

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
    // TODO: b/474580576 - stop verifying runtime_agent once we migrate to
    // runtime_agent_binary and userspace measurements.
    #[allow(deprecated)]
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

        // Verify runtime agent measurement
        let runtime_agent_ref_value = self
            .reference_values
            .runtime_agent
            .as_ref()
            .context("no runtime agent reference value")?;
        let runtime_agent_measurement =
            RawDigest { sha2_256: event.runtime_agent_measurement.clone(), ..Default::default() };
        let expected = acquire_expected_digests(
            verification_time.into_unix_millis(),
            endorsement.as_ref().and_then(|e| e.runtime_agent.as_ref()),
            runtime_agent_ref_value,
        )
        .context("acquiring runtime agent expected values")?;
        compare_measurement_digest(&runtime_agent_measurement, &expected)
            .context("comparing runtime agent measurement")?;

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
/// at least one package's serialized [`MpmAttachment`] digest matches the
/// `binary_mpm` reference values and endorsements.
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

        // Acquire the expected text value from the binary_mpm reference value.
        let binary_mpm_ref_value =
            self.reference_values.binary_mpm.as_ref().context("no binary mpm reference value")?;
        let expected = acquire_mpm_expected_values(
            verification_time.into_unix_millis(),
            endorsement.as_ref().and_then(|e| e.binary_mpm.as_ref()),
            binary_mpm_ref_value,
        )
        .context("acquiring binary mpm expected values")?;

        // Iterate through all packages and succeed if at least one matches.
        let matched = event
            .packages
            .iter()
            .any(|package| compare_text_value(&package.mpm_version_id, &expected).is_ok());
        anyhow::ensure!(matched, "no package matched the binary mpm expected value");

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
    #[allow(deprecated)]
    fn transparent_layer1_verify_skip_succeeds() {
        use oak_proto_rust::oak::attestation::v1::{
            BinaryReferenceValue, SkipVerification, binary_reference_value::Type as BrvType,
        };

        let skip_ref = BinaryReferenceValue { r#type: Some(BrvType::Skip(SkipVerification {})) };
        let event = CbLayer1TransparentEvent {
            runtime_agent_binary_measurement: vec![0u8; 32],
            runtime_agent_measurement: vec![0u8; 32],
            userspace_measurement: vec![0u8; 32],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            &event,
        );
        let reference_values = CbLayer1TransparentReferenceValues {
            runtime_agent_binary: Some(skip_ref.clone()),
            userspace: Some(skip_ref.clone()),
            runtime_agent: Some(skip_ref),
        };
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, &evidence, &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
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
        let reference_values = CbLayer2TransparentReferenceValues { binary_mpm: Some(skip_ref) };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, &evidence, &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
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
        let reference_values = CbLayer2TransparentReferenceValues { binary_mpm: Some(skip_ref) };
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
            &Vec::from(ram_disk_digest),
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let memory_map_signed = test_util::make_signed_endorsement_for_digest(
            &Vec::from(memory_map_digest),
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let acpi_signed = test_util::make_signed_endorsement_for_digest(
            &Vec::from(acpi_digest),
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
    #[allow(deprecated)]
    fn transparent_layer1_verify_with_signed_endorsement_succeeds() {
        let not_before = make_instant!("2025-09-01T00:00:00Z");
        let not_after = make_instant!("2025-12-01T00:00:00Z");
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (signing_key, public_key) = test_util::new_random_signing_keypair();

        let runtime_agent_measurement = Sha256::from([10u8; 32]);
        let runtime_agent_binary_measurement = Sha256::from([11u8; 32]);
        let userspace_measurement = Sha256::from([12u8; 32]);

        let event = CbLayer1TransparentEvent {
            runtime_agent_measurement: Vec::from(runtime_agent_measurement),
            runtime_agent_binary_measurement: Vec::from(runtime_agent_binary_measurement),
            userspace_measurement: Vec::from(userspace_measurement),
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            &event,
        );

        let runtime_agent_signed = test_util::make_signed_endorsement_for_digest(
            &Vec::from(runtime_agent_measurement),
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let runtime_agent_binary_signed = test_util::make_signed_endorsement_for_digest(
            &Vec::from(runtime_agent_binary_measurement),
            not_before,
            not_after,
            &signing_key,
            vec![],
        );
        let userspace_signed = test_util::make_signed_endorsement_for_digest(
            &Vec::from(userspace_measurement),
            not_before,
            not_after,
            &signing_key,
            vec![],
        );

        let layer1_endorsement = CbLayer1TransparentEndorsement {
            runtime_agent: Some(runtime_agent_signed),
            runtime_agent_binary: Some(runtime_agent_binary_signed),
            userspace: Some(userspace_signed),
        };
        let endorsement_variant: Variant = layer1_endorsement.into();

        let ref_value = test_util::binary_reference_value_for_endorser_pk(public_key);
        let reference_values = CbLayer1TransparentReferenceValues {
            runtime_agent: Some(ref_value.clone()),
            runtime_agent_binary: Some(ref_value.clone()),
            userspace: Some(ref_value),
        };
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    #[allow(deprecated)]
    fn transparent_layer1_verify_with_empty_endorsement_fails() {
        let verify_time = make_instant!("2025-10-15T00:00:00Z");
        let (_signing_key, public_key) = test_util::new_random_signing_keypair();

        let event = CbLayer1TransparentEvent {
            runtime_agent_measurement: vec![10u8; 32],
            runtime_agent_binary_measurement: vec![11u8; 32],
            userspace_measurement: vec![12u8; 32],
        };
        let evidence = encode_event_proto(
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            &event,
        );

        let ref_value = test_util::binary_reference_value_for_endorser_pk(public_key);
        let reference_values = CbLayer1TransparentReferenceValues {
            runtime_agent: Some(ref_value.clone()),
            runtime_agent_binary: Some(ref_value.clone()),
            userspace: Some(ref_value),
        };
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &Variant::default());

        assert!(result.is_err());
    }

    #[test]
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

        let layer2_endorsement =
            CbLayer2TransparentEndorsement { binary_mpm: Some(binary_mpm_signed) };
        let endorsement_variant: Variant = layer2_endorsement.into();

        let event = CbLayer2TransparentEvent {
            packages: vec![
                MpmPackage { mpm_version_id: "test/1.0".into() },
                MpmPackage { mpm_version_id: "other/2.0".into() },
            ],
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
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
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

        let layer2_endorsement =
            CbLayer2TransparentEndorsement { binary_mpm: Some(binary_mpm_signed) };
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
        };
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(verify_time, &evidence, &endorsement_variant);

        assert!(result.is_err());
    }
}
