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
// Names of functions related to legacy attestation verification start with
// `get_`, while names of functions related to policy-based attestation
// verification start with `acquire_`.

use alloc::{string::String, vec::Vec};

use anyhow::{Context, Error};
use digest_util::{
    hex_to_raw_digest, is_hex_digest_match, raw_digest_from_contents, raw_to_hex_digest,
};
use intoto::statement::{
    get_hex_digest_from_statement, parse_statement, DefaultStatement, Validity,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, endorsement::Format, endorsements, expected_digests,
        expected_values, kernel_binary_reference_value, reference_values,
        tcb_version_expected_value, tcb_version_reference_value, text_expected_value,
        text_reference_value, AmdSevExpectedValues, AmdSevReferenceValues, ApplicationEndorsement,
        ApplicationLayerEndorsements, ApplicationLayerExpectedValues,
        ApplicationLayerReferenceValues, BinaryReferenceValue, CbEndorsements, CbExpectedValues,
        CbReferenceValues, ContainerEndorsement, ContainerLayerEndorsements,
        ContainerLayerExpectedValues, ContainerLayerReferenceValues, Endorsement,
        EndorsementReferenceValue, Endorsements, EventExpectedValues, EventReferenceValues,
        ExpectedDigests, ExpectedRegex, ExpectedStringLiterals, ExpectedValues, FirmwareAttachment,
        FirmwareEndorsement, InsecureExpectedValues, IntelTdxExpectedValues, KernelAttachment,
        KernelBinaryReferenceValue, KernelEndorsement, KernelExpectedValues,
        KernelLayerEndorsements, KernelLayerExpectedValues, KernelLayerReferenceValues,
        OakContainersEndorsements, OakContainersExpectedValues, OakContainersReferenceValues,
        OakRestrictedKernelEndorsements, OakRestrictedKernelExpectedValues,
        OakRestrictedKernelReferenceValues, RawDigests, ReferenceValues, RootLayerEndorsements,
        RootLayerExpectedValues, RootLayerReferenceValues, Signature, SignedEndorsement,
        SystemEndorsement, SystemLayerEndorsements, SystemLayerExpectedValues,
        SystemLayerReferenceValues, TcbVersionExpectedValue, TcbVersionReferenceValue,
        TextExpectedValue, TextReferenceValue, TransparentReleaseEndorsement, VerificationSkipped,
    },
    RawDigest,
};
use prost::Message;
use verify_endorsement::{is_firmware_type, is_kernel_type, verify_endorsement};

use crate::endorsement::verify_binary_endorsement;

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
            anyhow::bail!("Getting expected values: mismatch between evidence, endorsements and reference values")
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
    let root_layer_expected = reference_values
        .root_layer
        .as_ref()
        .map(|root_ref| {
            get_root_layer_expected_values(
                now_utc_millis,
                endorsements.root_layer.as_ref(),
                root_ref,
            )
            .context("getting root layer values")
        })
        .transpose()?;

    let layer_expected = reference_values
        .layers
        .iter()
        .map(|layer_ref| {
            acquire_event_expected_values(now_utc_millis, layer_ref).context("getting layer values")
        })
        .collect::<anyhow::Result<Vec<EventExpectedValues>>>()?;

    Ok(CbExpectedValues { root_layer: root_layer_expected, layers: layer_expected })
}

// Transcribes TcbVersionReferenceValue to analogous TcbVersionExpectedValue.
fn tcb_version_rv_to_ev(
    ref_value: Option<TcbVersionReferenceValue>,
) -> Option<TcbVersionExpectedValue> {
    if let Some(rv) = ref_value.as_ref() {
        match rv.r#type.as_ref() {
            Some(tcb_version_reference_value::Type::Skip(_)) => Some(TcbVersionExpectedValue {
                r#type: Some(tcb_version_expected_value::Type::Skipped(VerificationSkipped {})),
            }),
            Some(tcb_version_reference_value::Type::Minimum(m)) => Some(TcbVersionExpectedValue {
                r#type: Some(tcb_version_expected_value::Type::Minimum(*m)),
            }),
            None => Some(TcbVersionExpectedValue { ..Default::default() }),
        }
    } else {
        None
    }
}

pub(crate) fn get_root_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&RootLayerEndorsements>,
    reference_values: &RootLayerReferenceValues,
) -> anyhow::Result<RootLayerExpectedValues> {
    // Propagate each of the existing reference value for a TEE platform to the
    // corresponding expected value.
    #[allow(deprecated)]
    let amd_sev = if let Some(rvs) = reference_values.amd_sev.as_ref() {
        let stage0_expected = get_stage0_expected_values(
            now_utc_millis,
            endorsements.and_then(|value| value.stage0.as_ref()),
            rvs.stage0.as_ref().context("stage0 binary reference values not found")?,
        )
        .context("getting stage0 values")?;

        Some(AmdSevExpectedValues {
            stage0_expected: Some(stage0_expected),
            min_tcb_version: rvs.min_tcb_version,
            milan: tcb_version_rv_to_ev(rvs.milan),
            genoa: tcb_version_rv_to_ev(rvs.genoa),
            turin: tcb_version_rv_to_ev(rvs.turin),
            allow_debug: rvs.allow_debug,
        })
    } else {
        None
    };

    let intel_tdx = reference_values.intel_tdx.as_ref().map(|_| IntelTdxExpectedValues {});
    let insecure = reference_values.insecure.as_ref().map(|_| InsecureExpectedValues {});

    Ok(RootLayerExpectedValues { amd_sev, intel_tdx, insecure })
}

// Only used in policy-based verification.
#[allow(deprecated)]
pub(crate) fn get_amd_sev_snp_expected_values(
    reference_values: &AmdSevReferenceValues,
) -> anyhow::Result<AmdSevExpectedValues> {
    Ok(AmdSevExpectedValues {
        // TODO: b/376513946 - Remove Stage0 from AMD SEV-SNP expected values
        // since it will be verified by the firmware policy.
        stage0_expected: None,
        min_tcb_version: reference_values.min_tcb_version,
        milan: tcb_version_rv_to_ev(reference_values.milan),
        genoa: tcb_version_rv_to_ev(reference_values.genoa),
        turin: tcb_version_rv_to_ev(reference_values.turin),
        allow_debug: reference_values.allow_debug,
    })
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
            .context("getting kernel values")?,
        ),

        // TODO: b/331252282 - Remove temporary workaround for cmd line.
        kernel_cmd_line_text: Some(
            get_text_expected_values(
                now_utc_millis,
                endorsements.and_then(|value| value.kernel_cmd_line.as_ref()),
                reference_values
                    .kernel_cmd_line_text
                    .as_ref()
                    .context("no kernel command line text reference values")?,
            )
            .context("getting kernel command line values")?,
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
            .context("getting initramfs values")?,
        ),

        memory_map: Some(
            get_expected_measurement_digest(
                now_utc_millis,
                endorsements.and_then(|value| value.memory_map.as_ref()),
                reference_values.memory_map.as_ref().context("no memory map reference value")?,
            )
            .context("getting memory map values")?,
        ),

        acpi: Some(
            get_expected_measurement_digest(
                now_utc_millis,
                endorsements.and_then(|value| value.acpi.as_ref()),
                reference_values.acpi.as_ref().context("no ACPI reference value")?,
            )
            .context("getting acpi values")?,
        ),
    })
}

pub(crate) fn acquire_kernel_event_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&KernelEndorsement>,
    reference_values: &KernelLayerReferenceValues,
) -> anyhow::Result<KernelLayerExpectedValues> {
    Ok(KernelLayerExpectedValues {
        kernel: Some(
            acquire_kernel_expected_values(
                now_utc_millis,
                endorsement.and_then(|value| value.kernel.as_ref()),
                reference_values.kernel.as_ref().context("no kernel reference value")?,
            )
            .context("getting kernel values")?,
        ),

        // TODO: b/331252282 - Remove temporary workaround for cmd line.
        kernel_cmd_line_text: Some(
            acquire_text_expected_values(
                now_utc_millis,
                endorsement.and_then(|value| value.kernel_cmd_line.as_ref()),
                reference_values
                    .kernel_cmd_line_text
                    .as_ref()
                    .context("no kernel command line text reference values")?,
            )
            .context("getting kernel command line values")?,
        ),

        init_ram_fs: Some(
            acquire_expected_digests(
                now_utc_millis,
                endorsement.and_then(|value| value.init_ram_fs.as_ref()),
                reference_values
                    .init_ram_fs
                    .as_ref()
                    .context("no initial RAM disk reference value")?,
            )
            .context("getting initramfs values")?,
        ),

        memory_map: Some(
            acquire_expected_digests(
                now_utc_millis,
                endorsement.and_then(|value| value.memory_map.as_ref()),
                reference_values.memory_map.as_ref().context("no memory map reference value")?,
            )
            .context("getting memory map values")?,
        ),

        acpi: Some(
            acquire_expected_digests(
                now_utc_millis,
                endorsement.and_then(|value| value.acpi.as_ref()),
                reference_values.acpi.as_ref().context("no ACPI reference value")?,
            )
            .context("getting acpi values")?,
        ),
    })
}

pub(crate) fn acquire_event_expected_values(
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
    let system_image = Some(
        get_expected_measurement_digest(
            now_utc_millis,
            endorsements.and_then(|value| value.system_image.as_ref()),
            reference_values.system_image.as_ref().context("system image reference value")?,
        )
        .context("getting system image values")?,
    );
    Ok(SystemLayerExpectedValues { system_image })
}

pub(crate) fn acquire_system_event_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&SystemEndorsement>,
    reference_values: &SystemLayerReferenceValues,
) -> anyhow::Result<SystemLayerExpectedValues> {
    let system_image = Some(
        acquire_expected_digests(
            now_utc_millis,
            endorsement.and_then(|value| value.system_image.as_ref()),
            reference_values.system_image.as_ref().context("system image reference value")?,
        )
        .context("getting system image values")?,
    );
    Ok(SystemLayerExpectedValues { system_image })
}

pub(crate) fn get_application_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&ApplicationLayerEndorsements>,
    reference_values: &ApplicationLayerReferenceValues,
) -> anyhow::Result<ApplicationLayerExpectedValues> {
    let binary = Some(
        get_expected_measurement_digest(
            now_utc_millis,
            endorsements.and_then(|value| value.binary.as_ref()),
            reference_values.binary.as_ref().context("container binary reference value")?,
        )
        .context("getting application binary values")?,
    );
    let configuration = Some(
        get_expected_measurement_digest(
            now_utc_millis,
            endorsements.and_then(|value| value.configuration.as_ref()),
            reference_values.configuration.as_ref().context("container config reference value")?,
        )
        .context("getting application config values")?,
    );
    Ok(ApplicationLayerExpectedValues { binary, configuration })
}

pub(crate) fn acquire_application_event_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&ApplicationEndorsement>,
    reference_values: &ApplicationLayerReferenceValues,
) -> anyhow::Result<ApplicationLayerExpectedValues> {
    let binary = Some(
        acquire_expected_digests(
            now_utc_millis,
            endorsement.and_then(|value| value.binary.as_ref()),
            reference_values.binary.as_ref().context("application binary reference value")?,
        )
        .context("getting application binary values")?,
    );
    let configuration = Some(
        acquire_expected_digests(
            now_utc_millis,
            endorsement.and_then(|value| value.configuration.as_ref()),
            reference_values
                .configuration
                .as_ref()
                .context("application config reference value")?,
        )
        .context("getting application config values")?,
    );
    Ok(ApplicationLayerExpectedValues { binary, configuration })
}

pub(crate) fn get_container_layer_expected_values(
    now_utc_millis: i64,
    endorsements: Option<&ContainerLayerEndorsements>,
    reference_values: &ContainerLayerReferenceValues,
) -> anyhow::Result<ContainerLayerExpectedValues> {
    let bundle = Some(
        get_expected_measurement_digest(
            now_utc_millis,
            endorsements.and_then(|value| value.binary.as_ref()),
            reference_values.binary.as_ref().context("container binary reference value")?,
        )
        .context("getting container binary values")?,
    );
    let config = Some(
        get_expected_measurement_digest(
            now_utc_millis,
            endorsements.and_then(|value| value.configuration.as_ref()),
            reference_values.configuration.as_ref().context("container config reference value")?,
        )
        .context("getting container config values")?,
    );
    Ok(ContainerLayerExpectedValues { bundle, config })
}

pub(crate) fn acquire_container_event_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&ContainerEndorsement>,
    reference_values: &ContainerLayerReferenceValues,
) -> anyhow::Result<ContainerLayerExpectedValues> {
    let bundle = Some(
        acquire_expected_digests(
            now_utc_millis,
            endorsement.and_then(|value| value.binary.as_ref()),
            reference_values.binary.as_ref().context("container binary reference value")?,
        )
        .context("getting container binary values")?,
    );
    let config = Some(
        acquire_expected_digests(
            now_utc_millis,
            endorsement.and_then(|value| value.configuration.as_ref()),
            reference_values.configuration.as_ref().context("container config reference value")?,
        )
        .context("getting container config values")?,
    );
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
        Some(binary_reference_value::Type::Endorsement(ref_value)) => {
            let endorsement =
                endorsement.context("matching endorsement not found for reference value")?;
            verify_endorsement_wrapper(
                now_utc_millis,
                &endorsement.endorsement,
                &endorsement.endorsement_signature,
                &endorsement.rekor_log_entry,
                ref_value,
            )
            .context("verifying generic endorsement")?;
            let endorsement_statement = parse_statement(&endorsement.endorsement)
                .context("parsing endorsement statement")?;
            Ok(to_expected_digests(
                &[hex_to_raw_digest(&get_hex_digest_from_statement(&endorsement_statement)?)?],
                endorsement_statement.predicate.validity.as_ref(),
            ))
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(to_expected_digests(&expected_digests.digests, None))
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

// Generic helper to extract digest values for the provided endorsement and
// binary reference value. The resulting values can be cached by the client to
// avoid re-computation later.
fn acquire_expected_digests(
    now_utc_millis: i64,
    signed_endorsement: Option<&SignedEndorsement>,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<ExpectedDigests> {
    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Skip(_)) => Ok(ExpectedDigests {
            r#type: Some(expected_digests::Type::Skipped(VerificationSkipped {})),
        }),
        Some(binary_reference_value::Type::Endorsement(ref_value)) => {
            let statement = verify_endorsement(
                now_utc_millis,
                signed_endorsement.context("endorsement missing")?,
                ref_value,
            )
            .context("verifying generic endorsement")?;
            Ok(to_expected_digests(
                &[hex_to_raw_digest(&get_hex_digest_from_statement(&statement)?)?],
                statement.predicate.validity.as_ref(),
            ))
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(to_expected_digests(&expected_digests.digests, None))
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

// Extract the stage0 data from the provided Endorsement
// It will only be returned if the endorsement was verified.
fn get_verified_stage0_attachment(
    now_utc_millis: i64,
    endorsement: &TransparentReleaseEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<FirmwareAttachment> {
    verify_endorsement_wrapper(
        now_utc_millis,
        &endorsement.endorsement,
        &endorsement.endorsement_signature,
        &endorsement.rekor_log_entry,
        ref_value,
    )
    .context("verifying firmware endorsement")?;
    // Parse endorsement statement and verify attachment digest.
    let statement =
        parse_statement(&endorsement.endorsement).context("parsing endorsement statement")?;
    if !is_firmware_type(&statement) {
        anyhow::bail!("expected endorsement for firmware-type binary");
    }
    let expected_digest =
        get_hex_digest_from_statement(&statement).context("getting expected digest")?;
    let actual_digest = raw_to_hex_digest(&raw_digest_from_contents(&endorsement.subject));
    is_hex_digest_match(&actual_digest, &expected_digest).context("comparing digests")?;
    FirmwareAttachment::decode(&*endorsement.subject)
        .map_err(|_| anyhow::anyhow!("couldn't parse stage0 attachment"))
}

fn acquire_verified_stage0_attachment(
    now_utc_millis: i64,
    signed_endorsement: &SignedEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<(FirmwareAttachment, DefaultStatement)> {
    let statement = verify_endorsement(now_utc_millis, signed_endorsement, ref_value)
        .context("verifying firmware endorsement")?;
    if !is_firmware_type(&statement) {
        anyhow::bail!("expected endorsement for firmware-type binary");
    }

    let expected_digest =
        get_hex_digest_from_statement(&statement).context("getting expected digest")?;
    let endorsement = signed_endorsement
        .endorsement
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing endorsement"))?;
    let actual_digest = raw_to_hex_digest(&raw_digest_from_contents(&endorsement.subject));
    is_hex_digest_match(&actual_digest, &expected_digest).context("comparing expected digest")?;

    let decoded = FirmwareAttachment::decode(&*endorsement.subject)
        .map_err(|_| anyhow::anyhow!("couldn't parse firmware attachment"))?;
    Ok((decoded, statement))
}

// Get the expected values from the provided TransparentReleaseEndorsement.
// The endorsement is expected to contain a subject that can be deserialized as
// a FirmwareAttachment.
// The subject itself will be verified, and then the expected digests (each
// corresponding to a number of vCPU, any of them a valid match for the digest
// in the evidence).
pub(crate) fn get_stage0_expected_values(
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

            let firmware_attachment =
                get_verified_stage0_attachment(now_utc_millis, endorsement, public_keys)
                    .context("getting verified stage0 attachment")?;

            let endorsement_statement = parse_statement(&endorsement.endorsement)
                .context("parsing endorsement statement")?;

            Ok(to_expected_digests(
                firmware_attachment
                    .configs
                    .values()
                    .map(|digest| hex_to_raw_digest(digest).unwrap())
                    .collect::<Vec<RawDigest>>()
                    .as_slice(),
                endorsement_statement.predicate.validity.as_ref(),
            ))
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(to_expected_digests(expected_digests.digests.as_slice(), None))
        }

        None => Err(anyhow::anyhow!("empty stage0 reference value")),
    }
}

pub(crate) fn acquire_stage0_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&FirmwareEndorsement>,
    reference_value: &BinaryReferenceValue,
) -> anyhow::Result<ExpectedDigests> {
    match reference_value.r#type.as_ref() {
        Some(binary_reference_value::Type::Skip(_)) => Ok(ExpectedDigests {
            r#type: Some(expected_digests::Type::Skipped(VerificationSkipped {})),
        }),
        Some(binary_reference_value::Type::Endorsement(ref_value)) => {
            let (firmware_attachment, statement) = acquire_verified_stage0_attachment(
                now_utc_millis,
                endorsement.and_then(|value| value.firmware.as_ref()).expect(""),
                ref_value,
            )
            .context("getting verified stage0 attachment")?;

            Ok(to_expected_digests(
                firmware_attachment
                    .configs
                    .values()
                    .map(|digest| hex_to_raw_digest(digest).unwrap())
                    .collect::<Vec<RawDigest>>()
                    .as_slice(),
                statement.predicate.validity.as_ref(),
            ))
        }
        Some(binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(to_expected_digests(expected_digests.digests.as_slice(), None))
        }

        None => Err(anyhow::anyhow!("empty stage0 reference value")),
    }
}

// Extract the KernelAttachment data from the provided Endorsement
// It will only be returned if the endorsement was verified.
fn get_verified_kernel_attachment(
    now_utc_millis: i64,
    endorsement: &TransparentReleaseEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<KernelAttachment> {
    verify_endorsement_wrapper(
        now_utc_millis,
        &endorsement.endorsement,
        &endorsement.endorsement_signature,
        &endorsement.rekor_log_entry,
        ref_value,
    )
    .context("verifying kernel endorsement")?;
    // Parse endorsement statement and verify attachment digest.
    let statement =
        parse_statement(&endorsement.endorsement).context("parsing endorsement statement")?;
    if !is_kernel_type(&statement) {
        anyhow::bail!("expected endorsement for kernel-type binary");
    }
    let expected_digest =
        get_hex_digest_from_statement(&statement).context("getting expected digest")?;
    let actual_digest = raw_to_hex_digest(&raw_digest_from_contents(&endorsement.subject));
    is_hex_digest_match(&actual_digest, &expected_digest).context("comparing expected digest")?;
    KernelAttachment::decode(&*endorsement.subject)
        .map_err(|_| anyhow::anyhow!("couldn't parse kernel attachment"))
}

fn acquire_verified_kernel_attachment(
    now_utc_millis: i64,
    signed_endorsement: &SignedEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<(KernelAttachment, DefaultStatement)> {
    let statement = verify_endorsement(now_utc_millis, signed_endorsement, ref_value)
        .context("verifying kernel endorsement")?;
    if !is_kernel_type(&statement) {
        anyhow::bail!("expected endorsement for kernel-type binary");
    }
    let expected_digest =
        get_hex_digest_from_statement(&statement).context("getting expected digest")?;
    let endorsement = signed_endorsement
        .endorsement
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("missing endorsement"))?;
    let actual_digest = raw_to_hex_digest(&raw_digest_from_contents(&endorsement.subject));
    is_hex_digest_match(&actual_digest, &expected_digest).context("comparing expected digest")?;

    let decoded = KernelAttachment::decode(&*endorsement.subject)
        .map_err(|_| anyhow::anyhow!("couldn't parse kernel attachment"))?;
    Ok((decoded, statement))
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

            let endorsement = endorsement.context("No endorsement provided")?;
            let statement = parse_statement(&endorsement.endorsement)
                .context("parsing endorsement statement")?;

            Ok(KernelExpectedValues {
                image: Some(to_expected_digests(
                    &[hex_to_raw_digest(&expected_image)?],
                    statement.predicate.validity.as_ref(),
                )),
                setup_data: Some(to_expected_digests(
                    &[hex_to_raw_digest(&expected_setup_data)?],
                    statement.predicate.validity.as_ref(),
                )),
            })
        }
        Some(kernel_binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(KernelExpectedValues {
                image: Some(to_expected_digests(
                    &expected_digests
                        .image
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("no image digests provided"))?
                        .digests,
                    None,
                )),
                setup_data: Some(to_expected_digests(
                    &expected_digests
                        .setup_data
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("no setup_data digests provided"))?
                        .digests,
                    None,
                )),
            })
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

fn acquire_kernel_expected_values(
    now_utc_millis: i64,
    signed_endorsement: Option<&SignedEndorsement>,
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
            let (kernel_attachment, statement) = acquire_verified_kernel_attachment(
                now_utc_millis,
                signed_endorsement.context("endorsement not found")?,
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
                image: Some(to_expected_digests(
                    &[hex_to_raw_digest(&expected_image)?],
                    statement.predicate.validity.as_ref(),
                )),
                setup_data: Some(to_expected_digests(
                    &[hex_to_raw_digest(&expected_setup_data)?],
                    statement.predicate.validity.as_ref(),
                )),
            })
        }
        Some(kernel_binary_reference_value::Type::Digests(expected_digests)) => {
            Ok(KernelExpectedValues {
                image: Some(to_expected_digests(
                    &expected_digests
                        .image
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("no image digests provided"))?
                        .digests,
                    None,
                )),
                setup_data: Some(to_expected_digests(
                    &expected_digests
                        .setup_data
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("no setup_data digests provided"))?
                        .digests,
                    None,
                )),
            })
        }
        None => Err(anyhow::anyhow!("empty binary reference value")),
    }
}

pub(crate) fn get_text_expected_values(
    now_utc_millis: i64,
    endorsement: Option<&TransparentReleaseEndorsement>,
    value: &TextReferenceValue,
) -> anyhow::Result<TextExpectedValue> {
    match value.r#type.as_ref() {
        Some(text_reference_value::Type::Skip(_)) => Ok(TextExpectedValue {
            r#type: Some(text_expected_value::Type::Skipped(VerificationSkipped {})),
        }),
        Some(text_reference_value::Type::Endorsement(ref_value)) => {
            let endorsement =
                endorsement.context("matching endorsement not found for text reference value")?;
            verify_endorsement_wrapper(
                now_utc_millis,
                &endorsement.endorsement,
                &endorsement.endorsement_signature,
                &endorsement.rekor_log_entry,
                ref_value,
            )
            .context("verifying text endorsement")?;
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

pub(crate) fn acquire_text_expected_values(
    now_utc_millis: i64,
    signed_endorsement: Option<&SignedEndorsement>,
    value: &TextReferenceValue,
) -> anyhow::Result<TextExpectedValue> {
    match value.r#type.as_ref() {
        Some(text_reference_value::Type::Skip(_)) => Ok(TextExpectedValue {
            r#type: Some(text_expected_value::Type::Skipped(VerificationSkipped {})),
        }),
        Some(text_reference_value::Type::Endorsement(ref_value)) => {
            let signed = signed_endorsement.context("missing signed endorsement")?;
            let _statement = verify_endorsement(now_utc_millis, signed, ref_value)
                .context("verifying text endorsement")?;
            // Compare the actual command line against the one inlined in the endorsement.
            let endorsement = signed.endorsement.as_ref().context("missing endorsement")?;
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

fn to_expected_digests(source: &[RawDigest], claim_validity: Option<&Validity>) -> ExpectedDigests {
    ExpectedDigests {
        r#type: Some(expected_digests::Type::Digests(RawDigests {
            digests: source.to_vec(),
            valid: claim_validity.map(|cv| cv.into()),
        })),
    }
}

// Adapts the old-style endorsement verification to the new one: the
// reference values are used to determine the style.
//
// Old-style means that deprecated fields `endorser_public_key` and
// `rekor_public_key` are populated in EndorsementReferenceValue.
// New-style means that the other fields (`endorser`, `required_claims`
// and `rekor`) are populated. In that case, the deprecated fields
// related to the old style are ignored.
fn verify_endorsement_wrapper(
    now_utc_millis: i64,
    endorsement: &[u8],
    signature: &[u8],
    log_entry: &[u8],
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<()> {
    // Use the new-style `endorser` field to determine if the reference value
    // has the new fields populated. If not, fall back to the deprecated code
    // branch.
    //
    // TODO: b/379253152 - Remove this early out block, along with entire
    //     verify_binary_endorsement function once all clients verify via the
    //     new-style fields in EndorsementReferenceValue.
    if ref_value.endorser.is_none() {
        #[allow(deprecated)]
        return verify_binary_endorsement(
            now_utc_millis,
            endorsement,
            signature,
            log_entry,
            &ref_value.endorser_public_key,
            &ref_value.rekor_public_key,
        );
    }

    // Suboptimal but OK to make the new-style reference values work with the
    // non-policy-based attestation verification: The `endorser` key set may
    // contain several verification keys. Under the deprecated notation, we
    // don't have any key ID for the signature, so we have to try all the keys.
    // In practice, reference values will almost always contain a single
    // public key, so the for loop consists of exactly one iteration.
    let mut err = Error::msg("no endorser keys");
    for key in &ref_value.endorser.as_ref().unwrap().keys {
        // Eventually the signed endorsement will come directly from the host,
        // assembling it here from the deprecated TransparentReleaseEndorsement
        // is temporary.
        let signed_endorsement = SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: endorsement.to_vec(),
                subject: Vec::new(),
            }),
            signature: Some(Signature { key_id: key.key_id, raw: signature.to_vec() }),
            rekor_log_entry: log_entry.to_vec(),
        };

        let result = verify_endorsement(now_utc_millis, &signed_endorsement, ref_value);
        if result.is_ok() {
            return Ok(());
        }
        err = result.err().unwrap();
    }

    anyhow::bail!(err);
}

#[cfg(test)]
mod tests;
