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

extern crate alloc;

#[cfg(test)]
extern crate std;

use alloc::{format, string::String};
use std::fmt::Write;

use anyhow::{Context, Result};
use oak_proto_rust::oak::{
    RawDigest, attestation,
    attestation::v1::{
        ApplicationLayerData, ApplicationLayerReferenceValues, ContainerLayerData,
        ContainerLayerReferenceValues, ExtractedEvidence, KernelLayerData,
        KernelLayerReferenceValues, OakContainersData, OakContainersReferenceValues,
        OakRestrictedKernelData, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerData, RootLayerReferenceValues, SystemLayerData, SystemLayerReferenceValues,
        root_layer_data::Report,
    },
};
use sha2::{Digest, Sha256};
use zerocopy::{FromBytes, KnownLayout};

use crate::alloc::{borrow::ToOwned, string::ToString};

mod json_serialization;

const AMD_SEV_SNP_TITLE: &str = "AMD SEV-SNP";
const INTEL_TDX_TITLE: &str = "Intel TDX";
const INSECURE_TEE_TITLE: &str = "FAKE INSECURE";

const ATTESTATIONS_INTRO: &str = "Attestations identifying artifacts accepted by the reference values for this layer are described below.\n";
const REFERENCE_VALUES_INTRO: &str =
    "The reference values describing this layer are printed below.\n";

/// Provides human readable explanations for attestation data.
pub trait HumanReadableTitle {
    /// Concise title, eg. "Oak Containers Stack in a AMD SEV-SNP TEE".
    fn title(&self) -> Result<String, anyhow::Error>;
}

pub trait HumanReadableExplanation {
    /// Provides human readable explanations for a layer of an attestation data
    /// stack, including directions to map the attestation data to source code.
    fn description(&self) -> Result<String, anyhow::Error>;
}

fn get_tee_name_from_root_layer_evidence(
    root_layer: &RootLayerData,
) -> Result<&'static str, anyhow::Error> {
    match root_layer.report.as_ref().context("unexpectedly unset report proto field")? {
        Report::SevSnp(_) => Ok(AMD_SEV_SNP_TITLE),
        Report::Tdx(_) => Ok(INTEL_TDX_TITLE),
        Report::Fake(_) => Ok(INSECURE_TEE_TITLE),
    }
}

fn get_tee_name_from_root_layer_reference_values(
    root_layer_reference_values: &RootLayerReferenceValues,
) -> Result<String, anyhow::Error> {
    match root_layer_reference_values {
        RootLayerReferenceValues { insecure: Some(_), .. } => Ok(INSECURE_TEE_TITLE.to_owned()),
        RootLayerReferenceValues { amd_sev: Some(_), intel_tdx: Some(_), insecure: None } => {
            Ok(format!("{} or {}", AMD_SEV_SNP_TITLE, INTEL_TDX_TITLE))
        }
        RootLayerReferenceValues { amd_sev: None, intel_tdx: Some(_), insecure: None } => {
            Ok(INTEL_TDX_TITLE.to_owned())
        }
        RootLayerReferenceValues { amd_sev: Some(_), intel_tdx: None, insecure: None } => {
            Ok(AMD_SEV_SNP_TITLE.to_owned())
        }
        RootLayerReferenceValues { amd_sev: None, intel_tdx: None, insecure: None } => {
            Err(anyhow::Error::msg("no TEE value found in the reference values"))
        }
    }
}

impl HumanReadableExplanation for ExtractedEvidence {
    fn description(&self) -> Result<String, anyhow::Error> {
        let yaml_representation = {
            let json_representation = json_serialization::serialize_extracted_evidence(self);
            serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
        };
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for ReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        match &self.r#type {
            Some(attestation::v1::reference_values::Type::OakRestrictedKernel(_value)) => {
                Ok("Reference values for the Oak Restricted Kernel stack".to_owned())
            }
            Some(attestation::v1::reference_values::Type::OakContainers(_value)) => {
                Ok("Reference values for the Oak Containers stack".to_owned())
            }
            _ => Ok("Unrecognized reference values".to_owned()),
        }
    }
}

impl HumanReadableExplanation for ReferenceValues {
    fn description(&self) -> Result<String> {
        match self {
            ReferenceValues {
                r#type:
                    Some(attestation::v1::reference_values::Type::OakRestrictedKernel(
                        OakRestrictedKernelReferenceValues {
                            root_layer: Some(root_layer),
                            kernel_layer: Some(kernel_layer),
                            application_layer: Some(application_layer),
                        },
                    )),
            } => Ok(format!(
                "_____ {} _____\n\n{}\n\n_____ {} _____\n\n{}\n\n_____ {} _____\n\n{}",
                root_layer.title()?,
                root_layer.description()?,
                kernel_layer.title()?,
                kernel_layer.description()?,
                application_layer.title()?,
                application_layer.description()?
            )),
            ReferenceValues {
                r#type:
                    Some(attestation::v1::reference_values::Type::OakContainers(
                        OakContainersReferenceValues {
                            root_layer: Some(root_layer),
                            kernel_layer: Some(kernel_layer),
                            system_layer: Some(system_layer),
                            container_layer: Some(container_layer),
                        },
                    )),
            } => Ok(format!(
                "_____ {} _____\n\n{}\n\n_____ {} _____\n\n{}\n\n_____ {} _____\n\n{}\n\n_____ {} _____\n\n{}",
                root_layer.title()?,
                root_layer.description()?,
                kernel_layer.title()?,
                kernel_layer.description()?,
                system_layer.title()?,
                system_layer.description()?,
                container_layer.title()?,
                container_layer.description()?
            )),
            _ => {
                let yaml_representation = {
                    let json_representation = json_serialization::serialize_reference_values(self);
                    serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
                };
                serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
            }
        }
    }
}

impl HumanReadableTitle for OakRestrictedKernelData {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.clone().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_evidence(&root_layer)?;
        Ok(format!("Oak Restricted Kernel Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakRestrictedKernelReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.as_ref().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_reference_values(root_layer)?;
        Ok(format!("Oak Restricted Kernel Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakContainersData {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.clone().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_evidence(&root_layer)?;
        Ok(format!("Oak Containers Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakContainersReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.as_ref().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_reference_values(root_layer)?;
        Ok(format!("Oak Containers Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for RootLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Root Layer".to_string())
    }
}

impl HumanReadableExplanation for RootLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        match self.report.as_ref().context("unexpectedly unset report proto field")? {
            Report::SevSnp(report) => {
                let tee_name = get_tee_name_from_root_layer_evidence(self)?;
                let initial_memory_sha256_digest =
                    SNPInitialMemoryMeasurement::try_from(report.initial_measurement.as_slice())?;
                let firmware_provenace_link = initial_memory_sha256_digest.provenance_link();
                let firmware_hash_explaination =
                    initial_memory_sha256_digest.display_hash_explaination();
                let yaml_string = {
                    let yaml_representation = {
                        let json_representation =
                            json_serialization::serialize_root_layer_data(self);
                        serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
                    };
                    serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
                };
                Ok(format!(
                    "The attestation is rooted in an {tee_name} TEE.

Attestations identifying the firmware captured in the evidence can be found here:
{firmware_provenace_link}

{firmware_hash_explaination}

The evidence describing this layer is outlined below.

{yaml_string}"
                ))
            }
            _ => Err(anyhow::Error::msg(
                "human readable description not yet implemented for this type of TEE",
            )),
        }
    }
}

impl HumanReadableTitle for RootLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Root Layer".to_string())
    }
}

fn provenance_explaination_for_root_layer_reference_values(
    values: &RootLayerReferenceValues,
) -> Result<Option<String>> {
    match values {
        RootLayerReferenceValues {
            amd_sev:
                Some(attestation::v1::AmdSevReferenceValues {
                    stage0:
                        Some(attestation::v1::BinaryReferenceValue {
                            r#type:
                                Some(attestation::v1::binary_reference_value::Type::Digests(digests)),
                        }),
                    ..
                }),
            ..
        } => {
            let firmware_provenances_as_bullet_points = digests
                .digests
                .iter()
                .map(|digest| {
                    SNPInitialMemoryMeasurement::try_from(digest.sha2_384.as_slice())
                        .map(|measurement| format!("- {}", measurement.provenance_link()))
                })
                .collect::<Result<Vec<String>>>()?;

            Ok(if firmware_provenances_as_bullet_points.is_empty() {
                None
            } else {
                Some(format!(
        "Attestations identifying firmware artifacts accepted by the reference values for this layer can be found at:
{}

ⓘ In reference values for {AMD_SEV_SNP_TITLE} TEEs, the firmware is captured as a SHA2-384 hash. This is the expected memory measurement that would be taken by the TEE. Attestations that describe this firmware, reference it using the SHA2-256 hash of the SHA2-384 hash.",
firmware_provenances_as_bullet_points.join("\n")
    ))
            })
        }
        _ => Ok(None),
    }
}

impl HumanReadableExplanation for RootLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let attestation_root_explaination: String = match self {
            RootLayerReferenceValues { amd_sev: Some(_), intel_tdx: None, insecure: None } => {
                format!("The attestation must be rooted in an {AMD_SEV_SNP_TITLE} TEE.")
            }
            RootLayerReferenceValues { amd_sev: None, intel_tdx: Some(_), insecure: None } => {
                format!("The attestation must be rooted in an {INTEL_TDX_TITLE} TEE.")
            }
            RootLayerReferenceValues { amd_sev: Some(_), intel_tdx: Some(_), insecure: None } => {
                format!(
                    "The attestation must be rooted in an {AMD_SEV_SNP_TITLE} or {INTEL_TDX_TITLE} TEE."
                )
            }
            RootLayerReferenceValues { insecure: Some(_), .. } => {
                "The root of the attestation is not being verified.".to_owned()
            }
            RootLayerReferenceValues { amd_sev: None, intel_tdx: None, insecure: None } => {
                anyhow::bail!("invalid root layer reference values")
            }
        };
        let reference_values = {
            let yaml_representation = {
                let json_representation =
                    json_serialization::serialize_root_layer_reference_values(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            format!(
                "{REFERENCE_VALUES_INTRO}
{}",
                serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
            )
        };
        if let Some(provenance_explaination) =
            provenance_explaination_for_root_layer_reference_values(self)?
        {
            Ok(format!(
                "{attestation_root_explaination}

{provenance_explaination}

{reference_values}"
            ))
        } else {
            Ok(format!(
                "{attestation_root_explaination}

{reference_values}"
            ))
        }
    }
}

impl HumanReadableTitle for KernelLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Kernel Layer".to_string())
    }
}

impl HumanReadableExplanation for KernelLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let kernel_provenance_link = {
            let kernel_image_digest: ArtifactDigestSha2_256 = self
                .kernel_image
                .as_ref()
                .context("unexpectedly unset kernel_image proto field")
                .and_then(ArtifactDigestSha2_256::try_from)?;
            kernel_image_digest.provenance_link()
        };
        let initial_ramdisk_provenance_link = {
            let init_ram_fs_digest: ArtifactDigestSha2_256 = self
                .init_ram_fs
                .as_ref()
                .context("unexpectedly unset init_ram_fs proto field")
                .and_then(ArtifactDigestSha2_256::try_from)?;
            init_ram_fs_digest.provenance_link()
        };
        let yaml_string = {
            let yaml_representation = {
                let json_representation = json_serialization::serialize_kernel_layer_data(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };

        Ok(format!(
"Attestations identifying the binaries captured in the evidence in this layer can be found as outlined below.
Kernel: {kernel_provenance_link}
Initial Ramdisk: {initial_ramdisk_provenance_link}

The evidence describing the kernel layer is outlined below.

{yaml_string}"
        ))
    }
}

impl HumanReadableTitle for KernelLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Kernel Layer".to_string())
    }
}

fn provenance_explanation_for_kernel_layer_reference_values(
    values: &KernelLayerReferenceValues,
) -> Result<Option<String>> {
    let mut output = String::new();

    if let Some(attestation::v1::KernelBinaryReferenceValue {
        r#type:
            Some(attestation::v1::kernel_binary_reference_value::Type::Digests(
                attestation::v1::KernelDigests {
                    image: Some(attestation::v1::Digests { digests, .. }),
                    ..
                },
            )),
        ..
    }) = &values.kernel
    {
        writeln!(output, "Accepted Kernel Image Artifacts:").map_err(anyhow::Error::msg)?;
        for digest in digests {
            writeln!(output, "- {}", ArtifactDigestSha2_256::try_from(digest)?.provenance_link())
                .map_err(anyhow::Error::msg)?;
        }
    };

    if let Some(attestation::v1::BinaryReferenceValue {
        r#type:
            Some(attestation::v1::binary_reference_value::Type::Digests(attestation::v1::Digests {
                digests,
                ..
            })),
        ..
    }) = &values.init_ram_fs
    {
        writeln!(output, "Accepted Initial Ramdisk Artifacts:").map_err(anyhow::Error::msg)?;
        for digest in digests {
            writeln!(output, "- {}", ArtifactDigestSha2_256::try_from(digest)?.provenance_link())
                .map_err(anyhow::Error::msg)?;
        }
    };

    if output.is_empty() {
        Ok(None)
    } else {
        output.insert(0, '\n');
        output.insert_str(0, ATTESTATIONS_INTRO);
        Ok(Some(output))
    }
}

impl HumanReadableExplanation for KernelLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let reference_values = {
            let yaml_representation = {
                let json_representation =
                    json_serialization::serialize_kernel_layer_reference_values(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            format!(
                "{REFERENCE_VALUES_INTRO}
{}",
                serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
            )
        };
        if let Some(provenance_explanation) =
            provenance_explanation_for_kernel_layer_reference_values(self)?
        {
            Ok(format!(
                "{provenance_explanation}

{reference_values}"
            ))
        } else {
            Ok(reference_values)
        }
    }
}

impl HumanReadableTitle for SystemLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("System Layer".to_string())
    }
}

impl HumanReadableExplanation for SystemLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let system_image_provenance_link = {
            let system_image_digest = self
                .system_image
                .as_ref()
                .context("unexpectedly unset system_image proto field")
                .and_then(ArtifactDigestSha2_256::try_from)?;
            system_image_digest.provenance_link()
        };
        let yaml_string = {
            let yaml_representation = {
                let json_representation = json_serialization::serialize_system_layer_data(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };
        Ok(format!(
            "Attestations identifying the system image captured in the evidence can be found here: {system_image_provenance_link}

The evidence describing this layer is outlined below.

{yaml_string}"
        ))
    }
}

impl HumanReadableTitle for SystemLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("System Layer".to_string())
    }
}

fn provenance_explanation_for_system_layer_reference_values(
    values: &SystemLayerReferenceValues,
) -> Result<Option<String>> {
    let mut output = String::new();

    if let Some(attestation::v1::BinaryReferenceValue {
        r#type:
            Some(attestation::v1::binary_reference_value::Type::Digests(attestation::v1::Digests {
                digests,
                ..
            })),
        ..
    }) = &values.system_image
    {
        writeln!(output, "Accepted System Image Artifacts:").map_err(anyhow::Error::msg)?;
        for digest in digests {
            writeln!(output, "- {}", ArtifactDigestSha2_256::try_from(digest)?.provenance_link())
                .map_err(anyhow::Error::msg)?;
        }
    };

    if output.is_empty() {
        Ok(None)
    } else {
        output.insert_str(0, ATTESTATIONS_INTRO);
        Ok(Some(output))
    }
}

impl HumanReadableExplanation for SystemLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let reference_values = {
            let yaml_representation = {
                let json_representation =
                    json_serialization::serialize_system_layer_reference_values(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            format!(
                "{REFERENCE_VALUES_INTRO}
{}",
                serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
            )
        };
        if let Some(provenance_explanation) =
            provenance_explanation_for_system_layer_reference_values(self)?
        {
            Ok(format!(
                "{provenance_explanation}

{reference_values}"
            ))
        } else {
            Ok(reference_values)
        }
    }
}

impl HumanReadableTitle for ApplicationLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Application Layer".to_string())
    }
}

impl HumanReadableExplanation for ApplicationLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let yaml_string = {
            let yaml_representation = {
                let json_representation =
                    json_serialization::serialize_application_layer_data(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };
        Ok(format!(
            "The evidence describing the application is outlined below.

{yaml_string}"
        ))
    }
}

impl HumanReadableTitle for ApplicationLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Application Layer".to_string())
    }
}

impl HumanReadableExplanation for ApplicationLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let yaml_representation = {
            let json_representation =
                json_serialization::serialize_application_layer_reference_values(self);
            serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
        };
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for ContainerLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Container Layer".to_string())
    }
}

impl HumanReadableExplanation for ContainerLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let yaml_string = {
            let yaml_representation = {
                let json_representation = json_serialization::serialize_container_layer_data(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };
        Ok(format!(
            "The evidence describing the application is outlined below.

{yaml_string}"
        ))
    }
}

impl HumanReadableTitle for ContainerLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Container Layer".to_string())
    }
}

fn provenance_explanation_for_container_layer_reference_values(
    values: &ContainerLayerReferenceValues,
) -> Result<Option<String>> {
    let mut output = String::new();

    if let Some(attestation::v1::BinaryReferenceValue {
        r#type:
            Some(attestation::v1::binary_reference_value::Type::Digests(attestation::v1::Digests {
                digests,
                ..
            })),
        ..
    }) = &values.binary
    {
        writeln!(output, "Accepted Binary Artifacts:").map_err(anyhow::Error::msg)?;
        for digest in digests {
            writeln!(output, "- {}", ArtifactDigestSha2_256::try_from(digest)?.provenance_link())
                .map_err(anyhow::Error::msg)?;
        }
    };

    if let Some(attestation::v1::BinaryReferenceValue {
        r#type:
            Some(attestation::v1::binary_reference_value::Type::Digests(attestation::v1::Digests {
                digests,
                ..
            })),
        ..
    }) = &values.configuration
    {
        writeln!(output, "Accepted Configuration Artifacts:").map_err(anyhow::Error::msg)?;
        for digest in digests {
            writeln!(output, "- {}", ArtifactDigestSha2_256::try_from(digest)?.provenance_link())
                .map_err(anyhow::Error::msg)?;
        }
    };

    if output.is_empty() {
        Ok(None)
    } else {
        output.insert_str(0, ATTESTATIONS_INTRO);
        Ok(Some(output))
    }
}

impl HumanReadableExplanation for ContainerLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let reference_values = {
            let yaml_representation = {
                let json_representation =
                    json_serialization::serialize_container_layer_reference_values(self);
                serde_yaml::to_value(json_representation).map_err(anyhow::Error::msg)?
            };
            format!(
                "{REFERENCE_VALUES_INTRO}
{}",
                serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
            )
        };
        if let Some(provenance_explanation) =
            provenance_explanation_for_container_layer_reference_values(self)?
        {
            Ok(format!(
                "{provenance_explanation}

{reference_values}"
            ))
        } else {
            Ok(reference_values)
        }
    }
}

trait OakDigestDisplay {
    /// String of the hash in the following format: [alg]:[hash]. The algorithm
    /// descripter follows fieldnames of the proto-message: oak.RawDigest
    /// struct.
    #[allow(dead_code)]
    fn display_hash(&self) -> String;

    fn provenance_link(&self) -> String;
}

/// Convience struct that maintains type safety determinig the length of the
/// underlying slice. Provides consistent methods for creating and printing the
/// data.
#[derive(FromBytes, KnownLayout)]
struct ArtifactDigestSha2_256(pub [u8; 32]);

impl TryFrom<&RawDigest> for ArtifactDigestSha2_256 {
    type Error = anyhow::Error;

    fn try_from(value: &RawDigest) -> Result<Self, Self::Error> {
        match value.sha2_256.as_slice() {
            [] => Err(anyhow::Error::msg("no sha2_256 hash found")),
            _ => value.sha2_256.as_slice().try_into(),
        }
    }
}

impl TryFrom<&[u8]> for ArtifactDigestSha2_256 {
    type Error = anyhow::Error;

    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        ArtifactDigestSha2_256::read_from_bytes(slice)
            .map_err(|err| anyhow::anyhow!("unexpected length of measurement: {}", err))
    }
}

impl OakDigestDisplay for ArtifactDigestSha2_256 {
    // # TODO: b/335458726 - Stop permitting unexported code once mod is completed.
    #[allow(dead_code)]
    fn provenance_link(&self) -> String {
        format!("https://search.sigstore.dev/?hash={}", hex::encode(self.0))
    }
    fn display_hash(&self) -> String {
        format!("SHA2-256:{}", hex::encode(self.0.as_slice()))
    }
}

/// Convience struct that maintains type safety determinig the length of the
/// underlying slice. Provides consistent methods for creating and printing the
/// data.
#[derive(FromBytes, KnownLayout)]
struct SNPInitialMemoryMeasurement([u8; 48]);

impl SNPInitialMemoryMeasurement {
    fn sha2_256(&self) -> ArtifactDigestSha2_256 {
        Sha256::digest(self.0).as_slice().try_into().expect("sha256 digest to have expected length")
    }
    /// Print a hash in the following format: [alg]:[hash]. The algorithm
    /// descripter follows fieldnames of the proto-message: oak.RawDigest
    /// struct.
    fn display_hash_explaination(&self) -> String {
        format!(
            "ⓘ The firmware attestation digest is the SHA2-256 hash of the SHA2-384 hash of the initial memory state taken by the AMD SoC. The original SHA2-384 hash of the initial memory is: SHA2-384:{}; it is listed as the 'initial_measurement' in the evidence of this layer.",
            { hex::encode(self.0.as_slice()) }
        )
    }
}

impl OakDigestDisplay for SNPInitialMemoryMeasurement {
    fn display_hash(&self) -> String {
        self.sha2_256().display_hash()
    }

    fn provenance_link(&self) -> String {
        format!("https://search.sigstore.dev/?hash={}", hex::encode(self.sha2_256().0))
    }
}

impl TryFrom<&[u8]> for SNPInitialMemoryMeasurement {
    type Error = anyhow::Error;

    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        SNPInitialMemoryMeasurement::read_from_bytes(slice)
            .map_err(|err| anyhow::anyhow!("unexpected length of measurement: {}", err))
    }
}
