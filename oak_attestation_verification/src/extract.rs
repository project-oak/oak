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

use alloc::{format, string::String, vec, vec::Vec};

use anyhow::Context;
use coset::{CborSerializable, CoseKey, RegisteredLabelWithPrivate, cbor::Value, cwt::ClaimsSet};
use oak_dice::cert::{
    ACPI_MEASUREMENT_ID, APPLICATION_KEY_ID, CONTAINER_IMAGE_LAYER_ID,
    ENCLAVE_APPLICATION_LAYER_ID, EVENT_ID, FINAL_LAYER_CONFIG_MEASUREMENT_ID,
    INITRD_MEASUREMENT_ID, KERNEL_COMMANDLINE_ID, KERNEL_LAYER_ID, KERNEL_MEASUREMENT_ID,
    LAYER_2_CODE_MEASUREMENT_ID, LAYER_3_CODE_MEASUREMENT_ID, MEMORY_MAP_MEASUREMENT_ID,
    SETUP_DATA_MEASUREMENT_ID, SHA2_256_ID, SYSTEM_IMAGE_LAYER_ID, TRANSPARENT_EVENT_ID,
    cose_key_to_hpke_public_key, cose_key_to_verifying_key, get_public_key_from_claims_set,
};
use oak_proto_rust::oak::{
    RawDigest,
    attestation::v1::{
        ApplicationKeys, ApplicationLayerData, CbData, ContainerLayerData, Event, EventData,
        Evidence, ExtractedEvidence, FakeAttestationReport, KernelLayerData, OakContainersData,
        OakRestrictedKernelData, OrchestratorMeasurements, RootLayerData, RootLayerEvidence,
        Stage0Measurements, Stage1Measurements, SystemLayerData, TeePlatform,
        extracted_evidence::EvidenceValues, root_layer_data::Report,
    },
};
use oak_sev_snp_attestation_report::AttestationReport;
use prost::Message;
use sha2::Digest;
use zerocopy::FromBytes;

use crate::{platform::convert_amd_sev_snp_attestation_report, verifier::EventLogType};

pub(crate) struct ApplicationKeyValues {
    pub(crate) encryption_public_key: Vec<u8>,
    pub(crate) signing_public_key: Vec<u8>,
}

/// Extracts attestation-related values without verificaiton.
///
/// Extracts measurements, public keys, and other attestation-related values
/// from the evidence without verifying it. For most usecases, this function
/// should not be used. Instead use the [`verify`] function, which verifies the
/// attestation and only returns evidence upon successful verification. Hence
/// marked as dangerous.
pub fn extract_evidence(evidence: &Evidence) -> anyhow::Result<ExtractedEvidence> {
    let evidence_values =
        Some(extract_evidence_values(evidence).context("extracting evidence values")?);
    let ApplicationKeyValues { encryption_public_key, signing_public_key } =
        extract_application_key_values(
            evidence.application_keys.as_ref().context("no application keys")?,
        )
        .context("extracting application key values")?;

    Ok(ExtractedEvidence { evidence_values, encryption_public_key, signing_public_key })
}

/// Extracts the measurements and other attestation-related values from the
/// evidence.
pub(crate) fn extract_evidence_values(evidence: &Evidence) -> anyhow::Result<EvidenceValues> {
    let root_layer =
        Some(extract_root_values(evidence.root_layer.as_ref().context("no root layer evidence")?)?);

    if let Some(event_log) = &evidence.event_log
        && !event_log.encoded_events.is_empty()
    {
        let decoded_events: Vec<Event> = event_log
            .encoded_events
            .iter()
            .enumerate()
            .map(|(index, encoded_event)| {
                Event::decode(encoded_event.as_slice()).map_err(|e| {
                    anyhow::anyhow!("Failed to decode event with index {}: {}", index, e)
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        #[derive(Debug, PartialEq)]
        enum EvidenceType {
            OakContainers,
            // Evidence from an older build of Oak Containers that uses deprecated event protos
            // in stage1 and the orchestrator.
            LegacyOakContainers,
            OakRestrictedKernel,
            CB,
        }

        let evidence_type = {
            if decoded_events.len() == 3
                && decoded_events[0].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.Stage0Measurements")
                && decoded_events[1].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.SystemLayerData")
                && decoded_events[2].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.ContainerLayerData")
            {
                EvidenceType::OakContainers
            } else if decoded_events.len() == 3
                && decoded_events[0].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.Stage0Measurements")
                && decoded_events[1].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.Stage1Measurements")
                && decoded_events[2].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.OrchestratorMeasurements")
            {
                EvidenceType::LegacyOakContainers
            } else if decoded_events.len() == 2
                && decoded_events[0].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.Stage0Measurements")
                && decoded_events[1].event.as_ref().map(|e| e.type_url.as_str())
                    == Some("type.googleapis.com/oak.attestation.v1.ApplicationLayerData")
            {
                EvidenceType::OakRestrictedKernel
            // CB evidence has three layers or more; if it does not extracting
            // the evidence will fail.
            } else if decoded_events.len() >= 3 {
                EvidenceType::CB
            } else {
                anyhow::bail!("events indicate an unexpected evidence type");
            }
        };

        match evidence_type {
            EvidenceType::OakContainers => {
                let kernel_layer = decoded_events[0]
                    .event
                    .as_ref()
                    .and_then(|e| Stage0Measurements::decode(e.value.as_slice()).ok())
                    .map(stage0_measurements_to_kernel_layer_data)
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode oak containers kernel layer data")
                    })?;
                let system_layer = decoded_events[1]
                    .event
                    .as_ref()
                    .and_then(|e| SystemLayerData::decode(e.value.as_slice()).ok())
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode oak containers system layer data")
                    })?;
                let container_layer = decoded_events[2]
                    .event
                    .as_ref()
                    .and_then(|e| ContainerLayerData::decode(e.value.as_slice()).ok())
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode oak containers container layer data")
                    })?;

                Ok(EvidenceValues::OakContainers(OakContainersData {
                    root_layer,
                    kernel_layer: Some(kernel_layer),
                    system_layer: Some(system_layer),
                    container_layer: Some(container_layer),
                }))
            }
            EvidenceType::LegacyOakContainers => {
                let kernel_layer = decoded_events[0]
                    .event
                    .as_ref()
                    .and_then(|e| Stage0Measurements::decode(e.value.as_slice()).ok())
                    .map(stage0_measurements_to_kernel_layer_data)
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode oak containers kernel layer data")
                    })?;
                let system_layer = decoded_events[1]
                    .event
                    .as_ref()
                    .and_then(|e| Stage1Measurements::decode(e.value.as_slice()).ok())
                    .map(stage1_measurements_to_system_layer_data)
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode legacy oak containers system layer data")
                    })?;
                let container_layer = decoded_events[2]
                    .event
                    .as_ref()
                    .and_then(|e| OrchestratorMeasurements::decode(e.value.as_slice()).ok())
                    .map(oak_containers_orchestrator_measurements_to_container_layer_data)
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "Failed to decode legacy oak containers container layer data"
                        )
                    })?;
                Ok(EvidenceValues::OakContainers(OakContainersData {
                    root_layer,
                    kernel_layer: Some(kernel_layer),
                    system_layer: Some(system_layer),
                    container_layer: Some(container_layer),
                }))
            }
            EvidenceType::OakRestrictedKernel => {
                let kernel_layer = decoded_events[0]
                    .event
                    .as_ref()
                    .and_then(|e| Stage0Measurements::decode(e.value.as_slice()).ok())
                    .map(stage0_measurements_to_kernel_layer_data)
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode oak restricted kernel layer data")
                    })?;
                let application_layer = decoded_events[1]
                    .event
                    .as_ref()
                    .and_then(|e| ApplicationLayerData::decode(e.value.as_slice()).ok())
                    .ok_or_else(|| {
                        anyhow::anyhow!("Failed to decode oak restricted application layer data")
                    })?;

                Ok(EvidenceValues::OakRestrictedKernel(OakRestrictedKernelData {
                    root_layer,
                    kernel_layer: Some(kernel_layer),
                    application_layer: Some(application_layer),
                }))
            }
            EvidenceType::CB => {
                let mut layers = Vec::new();
                for event in &event_log.encoded_events {
                    layers.push(EventData {
                        event: Some(RawDigest {
                            sha2_256: sha2::Sha256::digest(event).to_vec(),
                            ..Default::default()
                        }),
                    });
                }
                #[allow(deprecated)]
                Ok(EvidenceValues::Cb(CbData { root_layer, layers }))
            }
        }
    }
    // There's no eventlog, proceed to extract evidence using the existing logic.
    else {
        let final_layer_claims = &claims_set_from_serialized_cert(
            &evidence
                .application_keys
                .as_ref()
                .context("no application keys")?
                .encryption_public_key_certificate,
        )
        .context("parsing final DICE layer certificate")?;

        // Determine the type of evidence from the claims in the certificate for the
        // final.
        if let Ok(container_layer_data) = extract_container_layer_data(final_layer_claims) {
            match &evidence.layers[..] {
                [kernel_layer, system_layer] => {
                    let kernel_layer = Some(
                        extract_kernel_values(
                            &claims_set_from_serialized_cert(&kernel_layer.eca_certificate)
                                .context("parsing claims from kernel cert")?,
                        )
                        .context("extracting kernel values")?,
                    );
                    let system_layer = Some(
                        extract_system_layer_data(
                            &claims_set_from_serialized_cert(&system_layer.eca_certificate)
                                .context("parsing claims from system cert")?,
                        )
                        .context("extracting system layer data")?,
                    );

                    let container_layer = Some(container_layer_data);
                    Ok(EvidenceValues::OakContainers(OakContainersData {
                        root_layer,
                        kernel_layer,
                        system_layer,
                        container_layer,
                    }))
                }
                _ => Err(anyhow::anyhow!("incorrect number of DICE layers for Oak Containers")),
            }
        } else if let Ok(application_layer_data) =
            extract_application_layer_data(final_layer_claims)
        {
            match &evidence.layers[..] {
                [kernel_layer] => {
                    let kernel_layer = Some(
                        extract_kernel_values(
                            &claims_set_from_serialized_cert(&kernel_layer.eca_certificate)
                                .context("parsing claims from kernel cert")?,
                        )
                        .context("extracting kernel values")?,
                    );

                    let application_layer = Some(application_layer_data);
                    Ok(EvidenceValues::OakRestrictedKernel(OakRestrictedKernelData {
                        root_layer,
                        kernel_layer,
                        application_layer,
                    }))
                }
                _ => Err(anyhow::anyhow!("incorrect number of DICE layers for Oak Containers")),
            }
        } else {
            let layers = &evidence.layers;
            {
                let layer_results: Result<Vec<Option<EventData>>, anyhow::Error> = layers
                    .iter()
                    .map(|layer| {
                        let extracted_data = extract_event_data(
                            &claims_set_from_serialized_cert(&layer.eca_certificate)
                                .context("parsing claims from CB layer cert")?,
                            &EventIdType::EventDigest,
                        )
                        .context("extracting event data")?;
                        Ok(Some(extracted_data))
                    })
                    .collect();
                let layer_values: Vec<EventData> = layer_results?.into_iter().flatten().collect();
                #[allow(deprecated)]
                Ok(EvidenceValues::Cb(CbData { root_layer, layers: layer_values }))
            }
        }
    }
}

/// Extracts values from the attestation report.
fn extract_root_values(root_layer: &RootLayerEvidence) -> anyhow::Result<RootLayerData> {
    match root_layer.platform() {
        TeePlatform::Unspecified => Err(anyhow::anyhow!("unspecified TEE platform")),
        TeePlatform::AmdSevSnp => {
            let report = AttestationReport::ref_from_bytes(&root_layer.remote_attestation_report)
                .map_err(|err| {
                anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err)
            })?;
            report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

            let converted_attestation_report = convert_amd_sev_snp_attestation_report(report)?;
            Ok(RootLayerData { report: Some(Report::SevSnp(converted_attestation_report)) })
        }
        TeePlatform::IntelTdx => Err(anyhow::anyhow!("not supported")),
        TeePlatform::None => {
            // We use an unsigned, mostly empty AMD SEV-SNP attestation report as a fake
            // when not running in a TEE.
            let report =
                AttestationReport::ref_from_bytes(&root_layer.remote_attestation_report)
                    .map_err(|err| anyhow::anyhow!("invalid fake attestation report: {}", err))?;
            report.validate().map_err(|msg| anyhow::anyhow!(msg))?;

            let report_data = report.data.report_data.as_ref().to_vec();

            Ok(RootLayerData { report: Some(Report::Fake(FakeAttestationReport { report_data })) })
        }
    }
}

/// Extracts application key values. There are two possible cases where
/// in the first case application keys are defined as cose key and another case
/// application keys are part of payload.
pub(crate) fn extract_application_key_values(
    application_keys: &ApplicationKeys,
) -> anyhow::Result<ApplicationKeyValues> {
    let application_key_values = || -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encryption_claims = claims_set_from_serialized_cert(
            &application_keys.encryption_public_key_certificate[..],
        )
        .context("getting encryption claims")?;
        let encryption_cose_key = get_public_key_from_claims_set(&encryption_claims)
            .map_err(|msg| anyhow::anyhow!(msg))
            .context("getting encryption COSE key")?;
        let encryption_public_key = cose_key_to_hpke_public_key(&encryption_cose_key)
            .map_err(|msg| anyhow::anyhow!(msg))
            .context("converting encryption COSE key")?;

        let signing_claims =
            claims_set_from_serialized_cert(&application_keys.signing_public_key_certificate[..])
                .context("getting signing claims")?;
        let signing_cose_key: CoseKey = get_public_key_from_claims_set(&signing_claims)
            .map_err(|msg| anyhow::anyhow!(msg))
            .context("getting signing COSE key")?;
        let signing_verifying_key: ecdsa::VerifyingKey<p256::NistP256> =
            cose_key_to_verifying_key(&signing_cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("getting signing verifying key")?;
        let signing_public_key = signing_verifying_key.to_sec1_bytes().to_vec();

        Ok((encryption_public_key, signing_public_key))
    };
    let (encryption_public_key, signing_public_key) = match application_key_values() {
        Ok(values) => values,
        Err(_) => {
            let encryption_cert = coset::CoseSign1::from_slice(
                &application_keys.encryption_public_key_certificate,
            )
            .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
            let encryption_payload = encryption_cert
                .payload
                .ok_or_else(|| anyhow::anyhow!("no encryption cert payload"))?;
            let encryption_claims = ClaimsSet::from_slice(&encryption_payload)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption claims set"))?;
            let encryption_public_key =
                extract_bytes_from_claims_set(&encryption_claims, APPLICATION_KEY_ID)
                    .context("extracting bytes from claims")?;

            let signing_cert =
                coset::CoseSign1::from_slice(&application_keys.signing_public_key_certificate)
                    .map_err(|_cose_err| {
                        anyhow::anyhow!("could not parse encryption certificate")
                    })?;
            let signing_payload =
                signing_cert.payload.ok_or_else(|| anyhow::anyhow!("no signing cert payload"))?;
            let signing_claims = ClaimsSet::from_slice(&signing_payload)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse signing claims set"))?;
            let signing_public_key =
                extract_bytes_from_claims_set(&signing_claims, APPLICATION_KEY_ID)
                    .context("extracting bytes from claims")?;

            (encryption_public_key, signing_public_key)
        }
    };
    Ok(ApplicationKeyValues { encryption_public_key, signing_public_key })
}

pub(crate) enum EventIdType {
    // Events recorded under EVENT_ID in the claims map.
    EventDigest,
    // Transparent events recorded under TRANSPARENT_EVENT_ID in the claims map.
    TransparentEventDigest,
}

impl From<EventLogType> for EventIdType {
    fn from(event_log_type: EventLogType) -> Self {
        match event_log_type {
            EventLogType::OriginalEventLog => EventIdType::EventDigest,
            EventLogType::TransparentEventLog => EventIdType::TransparentEventDigest,
        }
    }
}

/// Extracts the measurement values for the event data.
pub(crate) fn extract_event_data(
    claims: &ClaimsSet,
    event_id_type: &EventIdType,
) -> anyhow::Result<EventData> {
    let label_id = match event_id_type {
        EventIdType::EventDigest => EVENT_ID,
        EventIdType::TransparentEventDigest => TRANSPARENT_EVENT_ID,
    };
    let values = extract_value_from_claims_set(claims, label_id)
        .context("extracting event data from claims")?;
    let event = Some(value_to_raw_digest(values)?);
    Ok(EventData { event })
}

/// Extracts the measurement values for the kernel layer.
fn extract_kernel_values(claims: &ClaimsSet) -> anyhow::Result<KernelLayerData> {
    let values =
        extract_layer_data(claims, KERNEL_LAYER_ID).context("extracting kernel layer data")?;
    let kernel_image = Some(value_to_raw_digest(extract_value(values, KERNEL_MEASUREMENT_ID)?)?);
    let kernel_setup_data =
        Some(value_to_raw_digest(extract_value(values, SETUP_DATA_MEASUREMENT_ID)?)?);
    let kernel_raw_cmd_line = extract_value(values, KERNEL_COMMANDLINE_ID)
        .ok()
        .map(|v| String::from(v.as_text().expect("kernel_raw_cmd_line found but is not a string")));
    let init_ram_fs = Some(value_to_raw_digest(extract_value(values, INITRD_MEASUREMENT_ID)?)?);
    let memory_map = Some(value_to_raw_digest(extract_value(values, MEMORY_MAP_MEASUREMENT_ID)?)?);
    let acpi = Some(value_to_raw_digest(extract_value(values, ACPI_MEASUREMENT_ID)?)?);
    Ok(KernelLayerData {
        kernel_image,
        kernel_setup_data,
        kernel_raw_cmd_line,
        init_ram_fs,
        memory_map,
        acpi,
    })
}

/// Extracts the measurement values for the system image layer.
fn extract_system_layer_data(claims: &ClaimsSet) -> anyhow::Result<SystemLayerData> {
    let values = extract_layer_data(claims, SYSTEM_IMAGE_LAYER_ID)
        .context("extracting system layer data")?;
    let system_image =
        Some(value_to_raw_digest(extract_value(values, LAYER_2_CODE_MEASUREMENT_ID)?)?);
    Ok(SystemLayerData { system_image })
}

/// Extracts the measurement values for the system image layer.
fn extract_container_layer_data(claims: &ClaimsSet) -> anyhow::Result<ContainerLayerData> {
    let values = extract_layer_data(claims, CONTAINER_IMAGE_LAYER_ID)
        .context("extracting container layer data")?;
    let bundle = Some(value_to_raw_digest(extract_value(values, LAYER_3_CODE_MEASUREMENT_ID)?)?);
    let config =
        Some(value_to_raw_digest(extract_value(values, FINAL_LAYER_CONFIG_MEASUREMENT_ID)?)?);
    Ok(ContainerLayerData {
        bundle,
        config,
        // TODO: b/384476430 - Extract public keys from the event.
        hybrid_encryption_public_key: vec![],
        signing_public_key: vec![],
        session_binding_public_key: vec![],
    })
}

/// Extracts the measurement values for the enclave application layer.
fn extract_application_layer_data(claims: &ClaimsSet) -> anyhow::Result<ApplicationLayerData> {
    let values = extract_layer_data(claims, ENCLAVE_APPLICATION_LAYER_ID)
        .context("extracting application layer data")?;
    let binary = Some(value_to_raw_digest(extract_value(values, LAYER_2_CODE_MEASUREMENT_ID)?)?);
    let config =
        Some(value_to_raw_digest(extract_value(values, FINAL_LAYER_CONFIG_MEASUREMENT_ID)?)?);
    Ok(ApplicationLayerData { binary, config })
}

/// Extracts the claim that contains the values for the specified layer.
fn extract_layer_data(claims: &ClaimsSet, layer_id: i64) -> anyhow::Result<&Vec<(Value, Value)>> {
    let target = RegisteredLabelWithPrivate::PrivateUse(layer_id);
    claims
        .rest
        .iter()
        .find_map(|(label, value)| {
            if let Value::Map(map) = value
                && label == &target
            {
                Some(map)
            } else {
                None
            }
        })
        .context("couldn't find layer values")
}

/// Extracts bytes for the label from claim.
fn extract_bytes_from_claims_set(claims: &ClaimsSet, label_id: i64) -> anyhow::Result<Vec<u8>> {
    match extract_value_from_claims_set(claims, label_id)? {
        Value::Bytes(bytes) => Ok(bytes.to_vec()),
        _ => Err(anyhow::anyhow!("value was not of type Bytes")),
    }
}

/// Extracts a value for the label from claim.
fn extract_value_from_claims_set(claims: &ClaimsSet, label_id: i64) -> anyhow::Result<&Value> {
    let target_label = RegisteredLabelWithPrivate::PrivateUse(label_id);
    claims
        .rest
        .iter()
        .find_map(|(label, value)| if label == &target_label { Some(value) } else { None })
        .context(format!("couldn't find value {label_id}"))
}

/// Extracts a value for the label from the layer's mapping between labels and
/// values.
fn extract_value(values: &[(Value, Value)], label_id: i64) -> anyhow::Result<&Value> {
    let target_key = Value::Integer(label_id.into());
    values
        .iter()
        .find_map(|(key, value)| if key == &target_key { Some(value) } else { None })
        .context(format!("couldn't find measurement {label_id}"))
}

/// Extracts the individual digests from a value that represents a set of
/// digests.
fn value_to_raw_digest(value: &Value) -> anyhow::Result<RawDigest> {
    if let Value::Map(map) = value {
        let mut result = RawDigest::default();
        for (key, digest) in map.iter() {
            if let Value::Bytes(bytes) = digest {
                if key == &Value::Integer(SHA2_256_ID.into()) {
                    result.sha2_256 = bytes.to_vec();
                } else {
                    anyhow::bail!("digest is not a byte array");
                }
            } else {
                anyhow::bail!("digest is not a byte array");
            }
        }
        Ok(result)
    } else {
        Err(anyhow::anyhow!("value is not a map of digests"))
    }
}

/// Translates [`Stage0Measurements`] to [`KernelLayerData`]. Both hold the same
/// data, just in slightly different proto messages.
pub(crate) fn stage0_measurements_to_kernel_layer_data(
    measurements: Stage0Measurements,
) -> KernelLayerData {
    KernelLayerData {
        kernel_image: Some(RawDigest {
            sha2_256: measurements.kernel_measurement,
            ..Default::default()
        }),
        kernel_setup_data: Some(RawDigest {
            sha2_256: measurements.setup_data_digest,
            ..Default::default()
        }),
        kernel_raw_cmd_line: Some(measurements.kernel_cmdline),
        init_ram_fs: Some(RawDigest {
            sha2_256: measurements.ram_disk_digest,
            ..Default::default()
        }),
        memory_map: Some(RawDigest {
            sha2_256: measurements.memory_map_digest,
            ..Default::default()
        }),
        acpi: Some(RawDigest { sha2_256: measurements.acpi_digest, ..Default::default() }),
    }
}

/// Translates [`Stage1Measurements`] to [`SystemLayerData`]. Both hold the same
/// data, just in slightly different proto messages.
///
/// [`Stage1Measurements`] is deprecated and only present for compatibility
/// with older binaries that have been previously imported into Google3 and may
/// still use them.
#[allow(deprecated)]
fn stage1_measurements_to_system_layer_data(measurements: Stage1Measurements) -> SystemLayerData {
    SystemLayerData { system_image: measurements.system_image }
}

/// Translates [`OrchestratorMeasurements`] to
/// [`ContainerLayerData`]. Both hold the same data, just in slightly
/// different proto messages.
///
/// [`OrchestratorMeasurements`] is deprecated and only present for
/// compatibility  with older binaries that have been previously imported into
/// Google3 and may still use them.
#[allow(deprecated)]
fn oak_containers_orchestrator_measurements_to_container_layer_data(
    measurements: OrchestratorMeasurements,
) -> ContainerLayerData {
    ContainerLayerData {
        bundle: measurements.container_image,
        config: measurements.config,
        // TODO: b/384476430 - Extract public keys from the event.
        hybrid_encryption_public_key: vec![],
        signing_public_key: vec![],
        session_binding_public_key: vec![],
    }
}

/// Parses the CBOR map from a serialized certificate.
pub(crate) fn claims_set_from_serialized_cert(slice: &[u8]) -> anyhow::Result<ClaimsSet> {
    let cert = coset::CoseSign1::from_slice(slice)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
    let payload = cert.payload.ok_or_else(|| anyhow::anyhow!("no signing cert payload"))?;
    ClaimsSet::from_slice(&payload)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))
}
