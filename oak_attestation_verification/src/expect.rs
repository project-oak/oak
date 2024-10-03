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

use alloc::{string::String, vec::Vec};

use anyhow::Context;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, endorsements, expected_digests, expected_values,
        kernel_binary_reference_value, reference_values, text_expected_value, text_reference_value,
        AmdSevExpectedValues, ApplicationLayerEndorsements, ApplicationLayerExpectedValues,
        ApplicationLayerReferenceValues, BinaryReferenceValue, CbEndorsements, CbExpectedValues,
        CbReferenceValues, ContainerLayerEndorsements, ContainerLayerExpectedValues,
        ContainerLayerReferenceValues, EndorsementReferenceValue, Endorsements,
        EventExpectedValues, EventReferenceValues, ExpectedDigests, ExpectedRegex,
        ExpectedStringLiterals, ExpectedValues, FirmwareAttachment, InsecureExpectedValues,
        IntelTdxExpectedValues, KernelAttachment, KernelBinaryReferenceValue, KernelExpectedValues,
        KernelLayerEndorsements, KernelLayerExpectedValues, KernelLayerReferenceValues,
        OakContainersEndorsements, OakContainersExpectedValues, OakContainersReferenceValues,
        OakRestrictedKernelEndorsements, OakRestrictedKernelExpectedValues,
        OakRestrictedKernelReferenceValues, RawDigests, ReferenceValues, RootLayerEndorsements,
        RootLayerExpectedValues, RootLayerReferenceValues, SystemLayerEndorsements,
        SystemLayerExpectedValues, SystemLayerReferenceValues, TextExpectedValue,
        TextReferenceValue, TransparentReleaseEndorsement, VerificationSkipped,
    },
    RawDigest,
};
use prost::Message;

use crate::{
    endorsement::{
        get_digest, is_firmware_type, is_kernel_type, parse_statement, verify_binary_endorsement,
    },
    util::{hex_to_raw_digest, is_hex_digest_match, raw_digest_from_contents, raw_to_hex_digest},
};

// Create the set of [ExpectedValues] for the provided [endorsements] and
// [reference_values]. These can be cached by the client for as long as the
// validity time provided.
pub fn get_expected_values(
    now_utc_millis: i64,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<ExpectedValues> {
    match (endorsements.r#type.as_ref(), reference_values.r#type.as_ref()) {
        (
            Some(endorsements::Type::OakRestrictedKernel(ends)),
            Some(reference_values::Type::OakRestrictedKernel(rvs)),
        ) => {
            let expected = get_oak_restricted_kernel_expected_values(now_utc_millis, ends, rvs)
                .context("getting RK expected values")?;
            Ok(ExpectedValues {
                r#type: Some(expected_values::Type::OakRestrictedKernel(expected)),
            })
        }
        (
            Some(endorsements::Type::OakContainers(ends)),
            Some(reference_values::Type::OakContainers(rvs)),
        ) => {
            let expected = get_oak_containers_expected_values(now_utc_millis, ends, rvs)
                .context("getting containers expected values")?;
            Ok(ExpectedValues { r#type: Some(expected_values::Type::OakContainers(expected)) })
        }
        (Some(endorsements::Type::Cb(ends)), Some(reference_values::Type::Cb(rvs))) => {
            let expected = get_cb_expected_values(now_utc_millis, ends, rvs)
                .context("getting CB expected values")?;
            Ok(ExpectedValues { r#type: Some(expected_values::Type::Cb(expected)) })
        }
        // Evidence, endorsements and reference values must exist and reflect the same chain type.
        (None, _) => anyhow::bail!("Endorsements are empty"),
        (_, None) => anyhow::bail!("Reference values are empty"),
        (Some(_), Some(_)) => {
            anyhow::bail!(
                "Getting expected values: mismatch between evidence, endorsements and reference values"
            )
        }
    }
}

pub(crate) fn get_oak_restricted_kernel_expected_values(
    now_utc_millis: i64,
    endorsements: &OakRestrictedKernelEndorsements,
    reference_values: &OakRestrictedKernelReferenceValues,
) -> anyhow::Result<OakRestrictedKernelExpectedValues> {
    Ok(OakRestrictedKernelExpectedValues {
        root_layer: Some(get_root_layer_expected_values(
            now_utc_millis,
            endorsements.root_layer.as_ref(),
            reference_values.root_layer.as_ref().context("no root layer reference values")?,
        )?),
        kernel_layer: Some(get_kernel_layer_expected_values(
            now_utc_millis,
            endorsements.kernel_layer.as_ref(),
            reference_values.kernel_layer.as_ref().context("no kernel layer reference values")?,
        )?),
        application_layer: Some(get_application_layer_expected_values(
            now_utc_millis,
            endorsements.application_layer.as_ref(),
            reference_values
                .application_layer
                .as_ref()
                .context("no application layer reference values")?,
        )?),
    })
}

pub(crate) fn get_oak_containers_expected_values(
    now_utc_millis: i64,
    endorsements: &OakContainersEndorsements,
    reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<OakContainersExpectedValues> {
    Ok(OakContainersExpectedValues {
        root_layer: Some(
            get_root_layer_expected_values(
                now_utc_millis,
                endorsements.root_layer.as_ref(),
                reference_values.root_layer.as_ref().context("no root layer reference values")?,
            )
            .context("getting root layer values")?,
        ),
        kernel_layer: Some(
            get_kernel_layer_expected_values(
                now_utc_millis,
                endorsements.kernel_layer.as_ref(),
                reference_values
                    .kernel_layer
                    .as_ref()
                    .context("no kernel layer reference values")?,
            )
            .context("getting kernel layer values")?,
        ),
        system_layer: Some(
            get_system_layer_expected_values(
                now_utc_millis,
                endorsements.system_layer.as_ref(),
                reference_values
                    .system_layer
                    .as_ref()
                    .context("no application layer reference values")?,
            )
            .context("getting system layer values")?,
        ),
        container_layer: Some(
            get_container_layer_expected_values(
                now_utc_millis,
                endorsements.container_layer.as_ref(),
                reference_values
                    .container_layer
                    .as_ref()
                    .context("no kernel layer reference values")?,
            )
            .context("getting container layer values")?,
        ),
    })
}

pub(crate) fn get_cb_expected_values(
    now_utc_millis: i64,
    endorsements: &CbEndorsements,
    reference_values: &CbReferenceValues,
) -> anyhow::Result<CbExpectedValues> {
    Ok(CbExpectedValues {
        root_layer: Some(
            get_root_layer_expected_values(
                now_utc_millis,
                endorsements.root_layer.as_ref(),
                reference_values.root_layer.as_ref().context("no root layer reference values")?,
            )
            .context("getting root layer values")?,
        ),
        kernel_layer: Some(
            get_event_expected_values(
                now_utc_millis,
                reference_values
                    .kernel_layer
                    .as_ref()
                    .context("no kernel layer reference values")?,
            )
            .context("getting kernel layer values")?,
        ),
        system_layer: Some(
            get_event_expected_values(
                now_utc_millis,
                reference_values
                    .system_layer
                    .as_ref()
                    .context("no system layer reference values")?,
            )
            .context("getting system layer values")?,
        ),
        application_layer: Some(
            get_event_expected_values(
                now_utc_millis,
                reference_values
                    .application_layer
                    .as_ref()
                    .context("no application layer reference values")?,
            )
            .context("getting application layer values")?,
        ),
    })
}

pub(crate) fn get_root_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&RootLayerEndorsements>,
    reference_values: &RootLayerReferenceValues,
) -> anyhow::Result<RootLayerExpectedValues> {
    // Propagate each of the existing reference value for a TEE platform to the
    // corresponding expected value.

    let amd_sev = if let Some(amd_sev_values) = reference_values.amd_sev.as_ref() {
        let stage0_expected = get_stage0_expected_values(
            now_utc_millis,
            endorsements.and_then(|value| value.stage0.as_ref()),
            amd_sev_values.stage0.as_ref().context("stage0 binary reference values not found")?,
        )
        .context("getting stage0 expected values")?;
        Some(AmdSevExpectedValues {
            stage0_expected: Some(stage0_expected),
            min_tcb_version: amd_sev_values.min_tcb_version.clone(),
            allow_debug: amd_sev_values.allow_debug,
        })
    } else {
        None
    };

    let intel_tdx = reference_values.intel_tdx.as_ref().map(|_| IntelTdxExpectedValues {});
    let insecure = reference_values.insecure.as_ref().map(|_| InsecureExpectedValues {});

    Ok(RootLayerExpectedValues { amd_sev, intel_tdx, insecure })
}

pub(crate) fn get_kernel_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&KernelLayerEndorsements>,
    reference_values: &KernelLayerReferenceValues,
) -> anyhow::Result<KernelLayerExpectedValues> {
    Ok(KernelLayerExpectedValues {
        kernel: Some(
            get_kernel_expected_values(
                now_utc_millis,
                endorsements.and_then(|value| value.kernel.as_ref()),
                reference_values.kernel.as_ref().context("no kernel reference value")?,
            )
            .context("failed to get kernel expected values")?,
        ),

        // TODO: b/331252282 - Remove temporary workaround for cmd line.
        kernel_cmd_line_text: Some(
            get_text_expected_values(
                now_utc_millis,
                reference_values
                    .kernel_cmd_line_text
                    .as_ref()
                    .context("no kernel command line text reference values")?,
                endorsements.and_then(|value| value.kernel_cmd_line.as_ref()),
            )
            .context("failed to get kernel cmd line expected value")?,
        ),

        init_ram_fs: Some(
            get_expected_measurement_digest(
                now_utc_millis,
                endorsements.and_then(|value| value.init_ram_fs.as_ref()),
                reference_values
                    .init_ram_fs
                    .as_ref()
                    .context("no initial RAM disk reference value")?,
            )
            .context("failed to get initramfs expected value")?,
        ),

        memory_map: Some(
            get_expected_measurement_digest(
                now_utc_millis,
                endorsements.and_then(|value| value.memory_map.as_ref()),
                reference_values.memory_map.as_ref().context("no memory map reference value")?,
            )
            .context("failed to get memory map expected value")?,
        ),

        acpi: Some(
            get_expected_measurement_digest(
                now_utc_millis,
                endorsements.and_then(|value| value.acpi.as_ref()),
                reference_values.acpi.as_ref().context("no ACPI reference value")?,
            )
            .context("failed to get ACPI table expected value")?,
        ),
    })
}

pub(crate) fn get_event_expected_values(
    now_utc_millis: i64,
    reference_values: &EventReferenceValues,
) -> anyhow::Result<EventExpectedValues> {
    let event = Some(get_expected_measurement_digest(
        now_utc_millis,
        None,
        reference_values.event.as_ref().context("event reference value")?,
    )?);
    Ok(EventExpectedValues { event })
}

pub(crate) fn get_system_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&SystemLayerEndorsements>,
    reference_values: &SystemLayerReferenceValues,
) -> anyhow::Result<SystemLayerExpectedValues> {
    let system_image = Some(get_expected_measurement_digest(
        now_utc_millis,
        endorsements.and_then(|value| value.system_image.as_ref()),
        reference_values.system_image.as_ref().context("container bundle reference value")?,
    )?);
    Ok(SystemLayerExpectedValues { system_image })
}

pub(crate) fn get_application_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&ApplicationLayerEndorsements>,
    reference_values: &ApplicationLayerReferenceValues,
) -> anyhow::Result<ApplicationLayerExpectedValues> {
    let binary = Some(get_expected_measurement_digest(
        now_utc_millis,
        endorsements.and_then(|value| value.binary.as_ref()),
        reference_values.binary.as_ref().context("container bundle reference value")?,
    )?);
    let configuration = Some(get_expected_measurement_digest(
        now_utc_millis,
        endorsements.and_then(|value| value.configuration.as_ref()),
        reference_values.configuration.as_ref().context("container bundle reference value")?,
    )?);
    Ok(ApplicationLayerExpectedValues { binary, configuration })
}

pub(crate) fn get_container_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&ContainerLayerEndorsements>,
    reference_values: &ContainerLayerReferenceValues,
) -> anyhow::Result<ContainerLayerExpectedValues> {
    let bundle = Some(get_expected_measurement_digest(
        now_utc_millis,
        endorsements.and_then(|value| value.binary.as_ref()),
        reference_values.binary.as_ref().context("container bundle reference value")?,
    )?);
    let config = Some(get_expected_measurement_digest(
        now_utc_millis,
        endorsements.and_then(|value| value.binary.as_ref()),
        reference_values.configuration.as_ref().context("container config reference value")?,
    )?);
    Ok(ContainerLayerExpectedValues { bundle, config })
}

// Generate the expected measurement digest values for the provided endorsement
// and reference_value. The resulting values can be cached by the client to
// avoid re-computation later.
pub(crate) fn get_expected_measurement_digest(
    now_utc_millis: i64,
    endorsement: Option<&TransparentReleaseEndorsement>,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<ExpectedDigests> {
    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Skip(_)) => Ok(ExpectedDigests {
            r#type: Some(expected_digests::Type::Skipped(VerificationSkipped {})),
        }),
        Some(binary_reference_value::Type::Endorsement(public_keys)) => {
            let endorsement =
                endorsement.context("matching endorsement not found for reference value")?;
            verify_binary_endorsement(
                now_utc_millis,
                &endorsement.endorsement,
                &endorsement.endorsement_signature,
                &endorsement.rekor_log_entry,
                &public_keys.endorser_public_key,
                &public_keys.rekor_public_key,
            )
            .context("verifying binary endorsement")?;
            Ok(into_expected_digests(&[hex_to_raw_digest(&get_digest(&parse_statement(
                &endorsement.endorsement,
            )?)?)?]))
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(into_expected_digests(&expected_digests.digests))
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

// Extract the stage0 data from the provided Endorsement
// It will only be returned if the endorsement was verified.
fn get_verified_stage0_attachment(
    now_utc_millis: i64,
    endorsement: &TransparentReleaseEndorsement,
    public_keys: &EndorsementReferenceValue,
) -> anyhow::Result<FirmwareAttachment> {
    verify_binary_endorsement(
        now_utc_millis,
        &endorsement.endorsement,
        &endorsement.endorsement_signature,
        &endorsement.rekor_log_entry,
        &public_keys.endorser_public_key,
        &public_keys.rekor_public_key,
    )
    .context("verifying binary endorsement")?;
    // Parse endorsement statement and verify attachment digest.
    let parsed_statement =
        parse_statement(&endorsement.endorsement).context("parsing endorsement statement")?;
    if !is_firmware_type(&parsed_statement) {
        anyhow::bail!("expected endorsement for firmware-type binary");
    }
    let expected_digest = get_digest(&parsed_statement).context("getting expected digest")?;
    let actual_digest = raw_to_hex_digest(&raw_digest_from_contents(&endorsement.subject));
    is_hex_digest_match(&actual_digest, &expected_digest).context("comparing digests")?;
    FirmwareAttachment::decode(&*endorsement.subject)
        .map_err(|_| anyhow::anyhow!("couldn't parse stage0 attachment"))
}

// Get the expected values from the provided TransparentReleaseEndorsement.
// The endorsement is expected to contain a subject that can be deserialized as
// a FirmwareAttachment.
// The subject itself will be verified, and then the expected digests (each
// corresponding to a number of vCPU, any of them a valid match for the digest
// in the evidence).
fn get_stage0_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&TransparentReleaseEndorsement>,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<ExpectedDigests> {
    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Skip(_)) => Ok(ExpectedDigests {
            r#type: Some(expected_digests::Type::Skipped(VerificationSkipped {})),
        }),
        Some(binary_reference_value::Type::Endorsement(public_keys)) => {
            let firmware_attachment = get_verified_stage0_attachment(
                now_utc_millis,
                endorsement.context("matching endorsement not found for reference value")?,
                public_keys,
            )
            .context("getting verified stage0 attachment")?;

            Ok(into_expected_digests(
                firmware_attachment
                    .configs
                    .values()
                    .map(|digest| hex_to_raw_digest(digest).unwrap())
                    .collect::<Vec<RawDigest>>()
                    .as_slice(),
            ))
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(into_expected_digests(expected_digests.digests.as_slice()))
        }

        None => Err(anyhow::anyhow!("empty stage0 reference value")),
    }
}

// Extract the KernelAttachment data from the provided Endorsement
// It will only be returned if the endorsement was verified.
fn get_verified_kernel_attachment(
    now_utc_millis: i64,
    endorsement: &TransparentReleaseEndorsement,
    public_keys: &EndorsementReferenceValue,
) -> anyhow::Result<KernelAttachment> {
    verify_binary_endorsement(
        now_utc_millis,
        &endorsement.endorsement,
        &endorsement.endorsement_signature,
        &endorsement.rekor_log_entry,
        &public_keys.endorser_public_key,
        &public_keys.rekor_public_key,
    )
    .context("verifying binary endorsement")?;
    // Parse endorsement statement and verify attachment digest.
    let parsed_statement =
        parse_statement(&endorsement.endorsement).context("parsing endorsement statement")?;
    if !is_kernel_type(&parsed_statement) {
        anyhow::bail!("expected endorsement for kernel-type binary");
    }
    let expected_digest = get_digest(&parsed_statement).context("getting expected digest")?;
    let actual_digest = raw_to_hex_digest(&raw_digest_from_contents(&endorsement.subject));
    is_hex_digest_match(&actual_digest, &expected_digest).context("comparing expected digest")?;
    KernelAttachment::decode(&*endorsement.subject)
        .map_err(|_| anyhow::anyhow!("couldn't parse kernel attachment"))
}

// Get the expected values from the provided TransportReleaseEndorsement.
// The endorsement is expected to contain a subject that can be deserialized as
// a KernelAttachment.
// The subject itself will be verified, and then the image and setup_data
// expected values will be returned.
// Subsequent callers can provide just the cached image and setup_data digests.
fn get_kernel_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&TransparentReleaseEndorsement>,
    reference_value: &KernelBinaryReferenceValue,
) -> anyhow::Result<KernelExpectedValues> {
    match reference_value.r#type.as_ref() {
        Some(kernel_binary_reference_value::Type::Skip(_)) => Ok(KernelExpectedValues {
            image: Some(ExpectedDigests {
                r#type: Some(expected_digests::Type::Skipped(VerificationSkipped {})),
            }),
            setup_data: Some(ExpectedDigests {
                r#type: Some(expected_digests::Type::Skipped(VerificationSkipped {})),
            }),
        }),
        Some(kernel_binary_reference_value::Type::Endorsement(public_keys)) => {
            let kernel_attachment = get_verified_kernel_attachment(
                now_utc_millis,
                endorsement.context("matching endorsement not found for reference value")?,
                public_keys,
            )
            .context("getting verified kernel attachment")?;
            let expected_image = kernel_attachment
                .image
                .ok_or_else(|| anyhow::anyhow!("no image digest in kernel attachment"))?;
            let expected_setup_data = kernel_attachment
                .setup_data
                .ok_or_else(|| anyhow::anyhow!("no setup data digest in kernel attachment"))?;

            Ok(KernelExpectedValues {
                image: Some(into_expected_digests(&[hex_to_raw_digest(&expected_image)?])),
                setup_data: Some(into_expected_digests(&[hex_to_raw_digest(
                    &expected_setup_data,
                )?])),
            })
        }
        Some(kernel_binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(KernelExpectedValues {
                image: Some(into_expected_digests(
                    &expected_digests
                        .image
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("no image digests provided"))?
                        .digests,
                )),
                setup_data: Some(into_expected_digests(
                    &expected_digests
                        .setup_data
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("no setup_data digests provided"))?
                        .digests,
                )),
            })
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

pub(crate) fn get_text_expected_values(
    now_utc_millis: i64,
    value: &TextReferenceValue,
    endorsement: Option<&TransparentReleaseEndorsement>,
) -> anyhow::Result<TextExpectedValue> {
    match value.r#type.as_ref() {
        Some(text_reference_value::Type::Skip(_)) => Ok(TextExpectedValue {
            r#type: Some(text_expected_value::Type::Skipped(VerificationSkipped {})),
        }),
        Some(text_reference_value::Type::Endorsement(public_keys)) => {
            let endorsement =
                endorsement.context("matching endorsement not found for text reference value")?;
            verify_binary_endorsement(
                now_utc_millis,
                &endorsement.endorsement,
                &endorsement.endorsement_signature,
                &endorsement.rekor_log_entry,
                &public_keys.endorser_public_key,
                &public_keys.rekor_public_key,
            )
            .context("verifying binary endorsement")?;
            // Compare the actual command line against the one inlined in the endorsement.
            let regex = String::from_utf8(endorsement.subject.clone())
                .expect("endorsement subject is not utf8");
            Ok(TextExpectedValue {
                r#type: Some(text_expected_value::Type::Regex(ExpectedRegex { value: regex })),
            })
        }
        Some(text_reference_value::Type::Regex(regex)) => Ok(TextExpectedValue {
            r#type: Some(text_expected_value::Type::Regex(ExpectedRegex {
                value: regex.value.clone(),
            })),
        }),
        Some(text_reference_value::Type::StringLiterals(string_literals)) => {
            Ok(TextExpectedValue {
                r#type: Some(text_expected_value::Type::StringLiterals(ExpectedStringLiterals {
                    value: string_literals.value.clone(),
                })),
            })
        }
        None => Err(anyhow::anyhow!("missing skip or value in the text reference value")),
    }
}

fn into_expected_digests(source: &[RawDigest]) -> ExpectedDigests {
    ExpectedDigests {
        r#type: Some(expected_digests::Type::Digests(RawDigests { digests: source.to_vec() })),
    }
}

#[cfg(test)]
mod tests;
